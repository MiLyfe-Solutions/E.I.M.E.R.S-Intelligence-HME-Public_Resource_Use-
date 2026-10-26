import V185TrunkScan20Chunk050

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_310279 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_310279 : Nat := 118140960795 + 310279 * 2 ^ 59
def prefixEnd_310279 : Nat := 4983230072969 + 3 ^ 40 * 310279 * 2
def baseEnd_310279 : Nat := 141619790219108236164941

theorem tailTrace_310279 : CollatzResearch.WordTrace tailWord_310279 prefixEnd_310279 141619790219108236164941 := by
  unfold tailWord_310279
  simp only [CollatzResearch.WordTrace]
  refine ⟨11316804842919649279445891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7544536561946432852963927 11316804842919649279445891)
  ·
    refine ⟨16975207264379473919168837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11316804842919649279445891 16975207264379473919168837)
    ·
      refine ⟨3182851362071151359844157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16975207264379473919168837 3182851362071151359844157)
      ·
        refine ⟨1193569260776681759941559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3182851362071151359844157 1193569260776681759941559)
        ·
          refine ⟨1790353891165022639912339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193569260776681759941559 1790353891165022639912339)
          ·
            refine ⟨2685530836747533959868509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790353891165022639912339 2685530836747533959868509)
            ·
              refine ⟨1007074063780325234950691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2685530836747533959868509 1007074063780325234950691)
              ·
                refine ⟨1510611095670487852426037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007074063780325234950691 1510611095670487852426037)
                ·
                  refine ⟨141619790219108236164941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510611095670487852426037 141619790219108236164941)
                  ·
                    rfl

theorem cell20_310279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_310279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310279 prefixEnd_310279 := by exact prefixLift 310279
  have htrace : WordTrace (prefixWord ++ tailWord_310279) baseStart_310279 baseEnd_310279 := by
    simpa [prefixWord, tailWord_310279, baseEnd_310279] using wordTrace_append hprefix tailTrace_310279
  have hstable : (prefixWord ++ tailWord_310279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310279).length < 2 ^ (prefixWord ++ tailWord_310279).sum := by decide
  have hdescent : baseEnd_310279 < baseStart_310279 := by decide
  rcases family_descends (prefixWord ++ tailWord_310279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310282 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_310282 : Nat := 118140960795 + 310282 * 2 ^ 59
def prefixEnd_310282 : Nat := 4983230072969 + 3 ^ 40 * 310282 * 2
def baseEnd_310282 : Nat := 141621159500853559064929

theorem tailTrace_310282 : CollatzResearch.WordTrace tailWord_310282 prefixEnd_310282 141621159500853559064929 := by
  unfold tailWord_310282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829228565477195197951275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7544609507939187194536733 2829228565477195197951275)
  ·
    refine ⟨4243842848215792796926913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829228565477195197951275 4243842848215792796926913)
    ·
      refine ⟨3182882136161844597695185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4243842848215792796926913 3182882136161844597695185)
      ·
        refine ⟨2387161602121383448271389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3182882136161844597695185 2387161602121383448271389)
        ·
          refine ⟨895185600795518793101771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2387161602121383448271389 895185600795518793101771)
          ·
            refine ⟨1342778401193278189652657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895185600795518793101771 1342778401193278189652657)
            ·
              refine ⟨1007083800894958642239493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342778401193278189652657 1007083800894958642239493)
              ·
                refine ⟨188828212667804745419905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1007083800894958642239493 188828212667804745419905)
                ·
                  refine ⟨141621159500853559064929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188828212667804745419905 141621159500853559064929)
                  ·
                    rfl

theorem cell20_310282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_310282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310282 prefixEnd_310282 := by exact prefixLift 310282
  have htrace : WordTrace (prefixWord ++ tailWord_310282) baseStart_310282 baseEnd_310282 := by
    simpa [prefixWord, tailWord_310282, baseEnd_310282] using wordTrace_append hprefix tailTrace_310282
  have hstable : (prefixWord ++ tailWord_310282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310282).length < 2 ^ (prefixWord ++ tailWord_310282).sum := by decide
  have hdescent : baseEnd_310282 < baseStart_310282 := by decide
  rcases family_descends (prefixWord ++ tailWord_310282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310334 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_310334 : Nat := 118140960795 + 310334 * 2 ^ 59
def prefixEnd_310334 : Nat := 4983230072969 + 3 ^ 40 * 310334 * 2
def baseEnd_310334 : Nat := 141644893717772489331383

theorem tailTrace_310334 : CollatzResearch.WordTrace tailWord_310334 prefixEnd_310334 141644893717772489331383 := by
  unfold tailWord_310334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414851357215049209087257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7545873905146929115132037 1414851357215049209087257)
  ·
    refine ⟨1061138517911286906815443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1414851357215049209087257 1061138517911286906815443)
    ·
      refine ⟨1591707776866930360223165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061138517911286906815443 1591707776866930360223165)
      ·
        refine ⟨596890416325098885083687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1591707776866930360223165 596890416325098885083687)
        ·
          refine ⟨895335624487648327625531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596890416325098885083687 895335624487648327625531)
          ·
            refine ⟨1343003436731472491438297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895335624487648327625531 1343003436731472491438297)
            ·
              refine ⟨1007252577548604368578723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343003436731472491438297 1007252577548604368578723)
              ·
                refine ⟨1510878866322906552868085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007252577548604368578723 1510878866322906552868085)
                ·
                  refine ⟨141644893717772489331383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510878866322906552868085 141644893717772489331383)
                  ·
                    rfl

theorem cell20_310334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_310334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310334 prefixEnd_310334 := by exact prefixLift 310334
  have htrace : WordTrace (prefixWord ++ tailWord_310334) baseStart_310334 baseEnd_310334 := by
    simpa [prefixWord, tailWord_310334, baseEnd_310334] using wordTrace_append hprefix tailTrace_310334
  have hstable : (prefixWord ++ tailWord_310334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310334).length < 2 ^ (prefixWord ++ tailWord_310334).sum := by decide
  have hdescent : baseEnd_310334 < baseStart_310334 := by decide
  rcases family_descends (prefixWord ++ tailWord_310334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310337 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 4]
def baseStart_310337 : Nat := 118140960795 + 310337 * 2 ^ 59
def prefixEnd_310337 : Nat := 4983230072969 + 3 ^ 40 * 310337 * 2
def baseEnd_310337 : Nat := 141646262999517812231371

theorem tailTrace_310337 : CollatzResearch.WordTrace tailWord_310337 prefixEnd_310337 141646262999517812231371 := by
  unfold tailWord_310337
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318920276709525185057265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7545946851139683456704843 11318920276709525185057265)
  ·
    refine ⟨8489190207532143888792949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11318920276709525185057265 8489190207532143888792949)
    ·
      refine ⟨795861581956138489574339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8489190207532143888792949 795861581956138489574339)
      ·
        refine ⟨1193792372934207734361509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795861581956138489574339 1193792372934207734361509)
        ·
          refine ⟨223836069925163950192783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1193792372934207734361509 223836069925163950192783)
          ·
            refine ⟨335754104887745925289175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223836069925163950192783 335754104887745925289175)
            ·
              refine ⟨503631157331618887933763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335754104887745925289175 503631157331618887933763)
              ·
                refine ⟨755446735997428331900645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503631157331618887933763 755446735997428331900645)
                ·
                  refine ⟨141646262999517812231371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 755446735997428331900645 141646262999517812231371)
                  ·
                    rfl

theorem cell20_310337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_310337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310337 prefixEnd_310337 := by exact prefixLift 310337
  have htrace : WordTrace (prefixWord ++ tailWord_310337) baseStart_310337 baseEnd_310337 := by
    simpa [prefixWord, tailWord_310337, baseEnd_310337] using wordTrace_append hprefix tailTrace_310337
  have hstable : (prefixWord ++ tailWord_310337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310337).length < 2 ^ (prefixWord ++ tailWord_310337).sum := by decide
  have hdescent : baseEnd_310337 < baseStart_310337 := by decide
  rcases family_descends (prefixWord ++ tailWord_310337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310341 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 2]
def baseStart_310341 : Nat := 118140960795 + 310341 * 2 ^ 59
def prefixEnd_310341 : Nat := 4983230072969 + 3 ^ 40 * 310341 * 2
def baseEnd_310341 : Nat := 141648088708511576098021

theorem tailTrace_310341 : CollatzResearch.WordTrace tailWord_310341 prefixEnd_310341 141648088708511576098021 := by
  unfold tailWord_310341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319066168695033868202877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7546044112463355912135251 11319066168695033868202877)
  ·
    refine ⟨4244649813260637700576079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11319066168695033868202877 4244649813260637700576079)
    ·
      refine ⟨6366974719890956550864119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244649813260637700576079 6366974719890956550864119)
      ·
        refine ⟨9550462079836434826296179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366974719890956550864119 9550462079836434826296179)
        ·
          refine ⟨14325693119754652239444269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9550462079836434826296179 14325693119754652239444269)
          ·
            refine ⟨5372134919907994589791601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14325693119754652239444269 5372134919907994589791601)
            ·
              refine ⟨4029101189930995942343701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5372134919907994589791601 4029101189930995942343701)
              ·
                refine ⟨188864118278015434797361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4029101189930995942343701 188864118278015434797361)
                ·
                  refine ⟨141648088708511576098021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188864118278015434797361 141648088708511576098021)
                  ·
                    rfl

theorem cell20_310341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_310341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310341 prefixEnd_310341 := by exact prefixLift 310341
  have htrace : WordTrace (prefixWord ++ tailWord_310341) baseStart_310341 baseEnd_310341 := by
    simpa [prefixWord, tailWord_310341, baseEnd_310341] using wordTrace_append hprefix tailTrace_310341
  have hstable : (prefixWord ++ tailWord_310341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310341).length < 2 ^ (prefixWord ++ tailWord_310341).sum := by decide
  have hdescent : baseEnd_310341 < baseStart_310341 := by decide
  rcases family_descends (prefixWord ++ tailWord_310341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310369 : List Nat := [1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_310369 : Nat := 118140960795 + 310369 * 2 ^ 59
def prefixEnd_310369 : Nat := 4983230072969 + 3 ^ 40 * 310369 * 2
def baseEnd_310369 : Nat := 47220289557155974388191

theorem tailTrace_310369 : CollatzResearch.WordTrace tailWord_310369 prefixEnd_310369 47220289557155974388191 := by
  unfold tailWord_310369
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320087412593594650222161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7546724941729063100148107 11320087412593594650222161)
  ·
    refine ⟨8490065559445195987666621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11320087412593594650222161 8490065559445195987666621)
    ·
      refine ⟨3183774584791948495374983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8490065559445195987666621 3183774584791948495374983)
      ·
        refine ⟨4775661877187922743062475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183774584791948495374983 4775661877187922743062475)
        ·
          refine ⟨7163492815781884114593713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775661877187922743062475 7163492815781884114593713)
          ·
            refine ⟨5372619611836413085945285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7163492815781884114593713 5372619611836413085945285)
            ·
              refine ⟨1007366177219327453614741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5372619611836413085945285 1007366177219327453614741)
              ·
                refine ⟨47220289557155974388191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1007366177219327453614741 47220289557155974388191)
                ·
                  rfl

theorem cell20_310369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_310369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310369 prefixEnd_310369 := by exact prefixLift 310369
  have htrace : WordTrace (prefixWord ++ tailWord_310369) baseStart_310369 baseEnd_310369 := by
    simpa [prefixWord, tailWord_310369, baseEnd_310369] using wordTrace_append hprefix tailTrace_310369
  have hstable : (prefixWord ++ tailWord_310369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310369).length < 2 ^ (prefixWord ++ tailWord_310369).sum := by decide
  have hdescent : baseEnd_310369 < baseStart_310369 := by decide
  rcases family_descends (prefixWord ++ tailWord_310369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310455 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 2]
def baseStart_310455 : Nat := 118140960795 + 310455 * 2 ^ 59
def prefixEnd_310455 : Nat := 4983230072969 + 3 ^ 40 * 310455 * 2
def baseEnd_310455 : Nat := 141700121414833846297555

theorem tailTrace_310455 : CollatzResearch.WordTrace tailWord_310455 prefixEnd_310455 141700121414833846297555 := by
  unfold tailWord_310455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11323224090282031337852819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7548816060188020891901879 11323224090282031337852819)
  ·
    refine ⟨16984836135423047006779229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11323224090282031337852819 16984836135423047006779229)
    ·
      refine ⟨6369313550783642627542211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16984836135423047006779229 6369313550783642627542211)
      ·
        refine ⟨9553970326175463941313317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6369313550783642627542211 9553970326175463941313317)
        ·
          refine ⟨1791369436157899488996247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9553970326175463941313317 1791369436157899488996247)
          ·
            refine ⟨2687054154236849233494371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791369436157899488996247 2687054154236849233494371)
            ·
              refine ⟨4030581231355273850241557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687054154236849233494371 4030581231355273850241557)
              ·
                refine ⟨188933495219778461730073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4030581231355273850241557 188933495219778461730073)
                ·
                  refine ⟨141700121414833846297555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188933495219778461730073 141700121414833846297555)
                  ·
                    rfl

theorem cell20_310455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2].length) (baseStart_310455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310455 prefixEnd_310455 := by exact prefixLift 310455
  have htrace : WordTrace (prefixWord ++ tailWord_310455) baseStart_310455 baseEnd_310455 := by
    simpa [prefixWord, tailWord_310455, baseEnd_310455] using wordTrace_append hprefix tailTrace_310455
  have hstable : (prefixWord ++ tailWord_310455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310455).length < 2 ^ (prefixWord ++ tailWord_310455).sum := by decide
  have hdescent : baseEnd_310455 < baseStart_310455 := by decide
  rcases family_descends (prefixWord ++ tailWord_310455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310516 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_310516 : Nat := 118140960795 + 310516 * 2 ^ 59
def prefixEnd_310516 : Nat := 4983230072969 + 3 ^ 40 * 310516 * 2
def baseEnd_310516 : Nat := 141727963476988745263973

theorem tailTrace_310516 : CollatzResearch.WordTrace tailWord_310516 prefixEnd_310516 141727963476988745263973 := by
  unfold tailWord_310516
  simp only [CollatzResearch.WordTrace]
  refine ⟨5662724471530519377911701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7550299295374025837215601 5662724471530519377911701)
  ·
    refine ⟨265440209602993095839611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5662724471530519377911701 265440209602993095839611)
    ·
      refine ⟨398160314404489643759417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265440209602993095839611 398160314404489643759417)
      ·
        refine ⟨298620235803367232819563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398160314404489643759417 298620235803367232819563)
        ·
          refine ⟨447930353705050849229345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298620235803367232819563 447930353705050849229345)
          ·
            refine ⟨335947765278788136922009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447930353705050849229345 335947765278788136922009)
            ·
              refine ⟨251960823959091102691507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335947765278788136922009 251960823959091102691507)
              ·
                refine ⟨377941235938636654037261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251960823959091102691507 377941235938636654037261)
                ·
                  refine ⟨141727963476988745263973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377941235938636654037261 141727963476988745263973)
                  ·
                    rfl

theorem cell20_310516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_310516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310516 prefixEnd_310516 := by exact prefixLift 310516
  have htrace : WordTrace (prefixWord ++ tailWord_310516) baseStart_310516 baseEnd_310516 := by
    simpa [prefixWord, tailWord_310516, baseEnd_310516] using wordTrace_append hprefix tailTrace_310516
  have hstable : (prefixWord ++ tailWord_310516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310516).length < 2 ^ (prefixWord ++ tailWord_310516).sum := by decide
  have hdescent : baseEnd_310516 < baseStart_310516 := by decide
  rcases family_descends (prefixWord ++ tailWord_310516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310521 : List Nat := [1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_310521 : Nat := 118140960795 + 310521 * 2 ^ 59
def prefixEnd_310521 : Nat := 4983230072969 + 3 ^ 40 * 310521 * 2
def baseEnd_310521 : Nat := 47243415204410316699095

theorem tailTrace_310521 : CollatzResearch.WordTrace tailWord_310521 prefixEnd_310521 47243415204410316699095 := by
  unfold tailWord_310521
  simp only [CollatzResearch.WordTrace]
  refine ⟨11325631308042924609755417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7550420872028616406503611 11325631308042924609755417)
  ·
    refine ⟨8494223481032193457316563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11325631308042924609755417 8494223481032193457316563)
    ·
      refine ⟨12741335221548290185974845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494223481032193457316563 12741335221548290185974845)
      ·
        refine ⟨4778000708080608819740567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12741335221548290185974845 4778000708080608819740567)
        ·
          refine ⟨7167001062120913229610851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778000708080608819740567 7167001062120913229610851)
          ·
            refine ⟨10750501593181369844416277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167001062120913229610851 10750501593181369844416277)
            ·
              refine ⟨503929762180376711457013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10750501593181369844416277 503929762180376711457013)
              ·
                refine ⟨47243415204410316699095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503929762180376711457013 47243415204410316699095)
                ·
                  rfl

theorem cell20_310521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_310521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310521 prefixEnd_310521 := by exact prefixLift 310521
  have htrace : WordTrace (prefixWord ++ tailWord_310521) baseStart_310521 baseEnd_310521 := by
    simpa [prefixWord, tailWord_310521, baseEnd_310521] using wordTrace_append hprefix tailTrace_310521
  have hstable : (prefixWord ++ tailWord_310521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310521).length < 2 ^ (prefixWord ++ tailWord_310521).sum := by decide
  have hdescent : baseEnd_310521 < baseStart_310521 := by decide
  rcases family_descends (prefixWord ++ tailWord_310521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310524 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_310524 : Nat := 118140960795 + 310524 * 2 ^ 59
def prefixEnd_310524 : Nat := 4983230072969 + 3 ^ 40 * 310524 * 2
def baseEnd_310524 : Nat := 141731614894976272997273

theorem tailTrace_310524 : CollatzResearch.WordTrace tailWord_310524 prefixEnd_310524 141731614894976272997273 := by
  unfold tailWord_310524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5662870363516028061057313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7550493818021370748076417 5662870363516028061057313)
  ·
    refine ⟨4247152772637021045792985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5662870363516028061057313 4247152772637021045792985)
    ·
      refine ⟨3185364579477765784344739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4247152772637021045792985 3185364579477765784344739)
      ·
        refine ⟨4778046869216648676517109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185364579477765784344739 4778046869216648676517109)
        ·
          refine ⟨447941893989060813423479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4778046869216648676517109 447941893989060813423479)
          ·
            refine ⟨671912840983591220135219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447941893989060813423479 671912840983591220135219)
            ·
              refine ⟨1007869261475386830202829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671912840983591220135219 1007869261475386830202829)
              ·
                refine ⟨377950973053270061326061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007869261475386830202829 377950973053270061326061)
                ·
                  refine ⟨141731614894976272997273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377950973053270061326061 141731614894976272997273)
                  ·
                    rfl

theorem cell20_310524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_310524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310524 prefixEnd_310524 := by exact prefixLift 310524
  have htrace : WordTrace (prefixWord ++ tailWord_310524) baseStart_310524 baseEnd_310524 := by
    simpa [prefixWord, tailWord_310524, baseEnd_310524] using wordTrace_append hprefix tailTrace_310524
  have hstable : (prefixWord ++ tailWord_310524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310524).length < 2 ^ (prefixWord ++ tailWord_310524).sum := by decide
  have hdescent : baseEnd_310524 < baseStart_310524 := by decide
  rcases family_descends (prefixWord ++ tailWord_310524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310558 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_310558 : Nat := 118140960795 + 310558 * 2 ^ 59
def prefixEnd_310558 : Nat := 4983230072969 + 3 ^ 40 * 310558 * 2
def baseEnd_310558 : Nat := 141747133421423265863801

theorem tailTrace_310558 : CollatzResearch.WordTrace tailWord_310558 prefixEnd_310558 141747133421423265863801 := by
  unfold tailWord_310558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415872601113609991106541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7551320539272586619234885 1415872601113609991106541)
  ·
    refine ⟨530952225417603746664953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1415872601113609991106541 530952225417603746664953)
    ·
      refine ⟨398214169063202809998715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530952225417603746664953 398214169063202809998715)
      ·
        refine ⟨597321253594804214998073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398214169063202809998715 597321253594804214998073)
        ·
          refine ⟨447990940196103161248555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597321253594804214998073 447990940196103161248555)
          ·
            refine ⟨671986410294154741872833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447990940196103161248555 671986410294154741872833)
            ·
              refine ⟨503989807720616056404625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671986410294154741872833 503989807720616056404625)
              ·
                refine ⟨377992355790462042303469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503989807720616056404625 377992355790462042303469)
                ·
                  refine ⟨141747133421423265863801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377992355790462042303469 141747133421423265863801)
                  ·
                    rfl

theorem cell20_310558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_310558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310558 prefixEnd_310558 := by exact prefixLift 310558
  have htrace : WordTrace (prefixWord ++ tailWord_310558) baseStart_310558 baseEnd_310558 := by
    simpa [prefixWord, tailWord_310558, baseEnd_310558] using wordTrace_append hprefix tailTrace_310558
  have hstable : (prefixWord ++ tailWord_310558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310558).length < 2 ^ (prefixWord ++ tailWord_310558).sum := by decide
  have hdescent : baseEnd_310558 < baseStart_310558 := by decide
  rcases family_descends (prefixWord ++ tailWord_310558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310559 : List Nat := [1, 1, 2, 4, 4, 8]
def baseStart_310559 : Nat := 118140960795 + 310559 * 2 ^ 59
def prefixEnd_310559 : Nat := 4983230072969 + 3 ^ 40 * 310559 * 2
def baseEnd_310559 : Nat := 5249910735135989141869

theorem tailTrace_310559 : CollatzResearch.WordTrace tailWord_310559 prefixEnd_310559 5249910735135989141869 := by
  unfold tailWord_310559
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327017281905257099638731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7551344854603504733092487 11327017281905257099638731)
  ·
    refine ⟨16990525922857885649458097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327017281905257099638731 16990525922857885649458097)
    ·
      refine ⟨12742894442143414237093573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16990525922857885649458097 12742894442143414237093573)
      ·
        refine ⟨2389292707901890169455045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12742894442143414237093573 2389292707901890169455045)
        ·
          refine ⟨447992382731604406772821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2389292707901890169455045 447992382731604406772821)
          ·
            refine ⟨5249910735135989141869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 447992382731604406772821 5249910735135989141869)
            ·
              rfl

theorem cell20_310559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 8].length) (baseStart_310559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310559 prefixEnd_310559 := by exact prefixLift 310559
  have htrace : WordTrace (prefixWord ++ tailWord_310559) baseStart_310559 baseEnd_310559 := by
    simpa [prefixWord, tailWord_310559, baseEnd_310559] using wordTrace_append hprefix tailTrace_310559
  have hstable : (prefixWord ++ tailWord_310559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310559).length < 2 ^ (prefixWord ++ tailWord_310559).sum := by decide
  have hdescent : baseEnd_310559 < baseStart_310559 := by decide
  rcases family_descends (prefixWord ++ tailWord_310559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310565 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 2]
def baseStart_310565 : Nat := 118140960795 + 310565 * 2 ^ 59
def prefixEnd_310565 : Nat := 4983230072969 + 3 ^ 40 * 310565 * 2
def baseEnd_310565 : Nat := 141750328412162352630439

theorem tailTrace_310565 : CollatzResearch.WordTrace tailWord_310565 prefixEnd_310565 141750328412162352630439 := by
  unfold tailWord_310565
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327236119883520124357149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7551490746589013416238099 11327236119883520124357149)
  ·
    refine ⟨4247713544956320046633931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11327236119883520124357149 4247713544956320046633931)
    ·
      refine ⟨6371570317434480069950897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247713544956320046633931 6371570317434480069950897)
      ·
        refine ⟨4778677738075860052463173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6371570317434480069950897 4778677738075860052463173)
        ·
          refine ⟨896002075889223759836845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4778677738075860052463173 896002075889223759836845)
          ·
            refine ⟨336000778458458909938817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 896002075889223759836845 336000778458458909938817)
            ·
              refine ⟨252000583843844182454113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336000778458458909938817 252000583843844182454113)
              ·
                refine ⟨189000437882883136840585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252000583843844182454113 189000437882883136840585)
                ·
                  refine ⟨141750328412162352630439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189000437882883136840585 141750328412162352630439)
                  ·
                    rfl

theorem cell20_310565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_310565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310565 prefixEnd_310565 := by exact prefixLift 310565
  have htrace : WordTrace (prefixWord ++ tailWord_310565) baseStart_310565 baseEnd_310565 := by
    simpa [prefixWord, tailWord_310565, baseEnd_310565] using wordTrace_append hprefix tailTrace_310565
  have hstable : (prefixWord ++ tailWord_310565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310565).length < 2 ^ (prefixWord ++ tailWord_310565).sum := by decide
  have hdescent : baseEnd_310565 < baseStart_310565 := by decide
  rcases family_descends (prefixWord ++ tailWord_310565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310593 : List Nat := [1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_310593 : Nat := 118140960795 + 310593 * 2 ^ 59
def prefixEnd_310593 : Nat := 4983230072969 + 3 ^ 40 * 310593 * 2
def baseEnd_310593 : Nat := 47254369458372899898997

theorem tailTrace_310593 : CollatzResearch.WordTrace tailWord_310593 prefixEnd_310593 47254369458372899898997 := by
  unfold tailWord_310593
  simp only [CollatzResearch.WordTrace]
  refine ⟨11328257363782080906376433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7552171575854720604250955 11328257363782080906376433)
  ·
    refine ⟨8496193022836560679782325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11328257363782080906376433 8496193022836560679782325)
    ·
      refine ⟨796518095890927563729593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8496193022836560679782325 796518095890927563729593)
      ·
        refine ⟨597388571918195672797195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796518095890927563729593 597388571918195672797195)
        ·
          refine ⟨896082857877293509195793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597388571918195672797195 896082857877293509195793)
          ·
            refine ⟨672062143407970131896845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896082857877293509195793 672062143407970131896845)
            ·
              refine ⟨252023303777988799461317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 672062143407970131896845 252023303777988799461317)
              ·
                refine ⟨47254369458372899898997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252023303777988799461317 47254369458372899898997)
                ·
                  rfl

theorem cell20_310593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_310593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310593 prefixEnd_310593 := by exact prefixLift 310593
  have htrace : WordTrace (prefixWord ++ tailWord_310593) baseStart_310593 baseEnd_310593 := by
    simpa [prefixWord, tailWord_310593, baseEnd_310593] using wordTrace_append hprefix tailTrace_310593
  have hstable : (prefixWord ++ tailWord_310593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310593).length < 2 ^ (prefixWord ++ tailWord_310593).sum := by decide
  have hdescent : baseEnd_310593 < baseStart_310593 := by decide
  rcases family_descends (prefixWord ++ tailWord_310593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310611 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_310611 : Nat := 118140960795 + 310611 * 2 ^ 59
def prefixEnd_310611 : Nat := 4983230072969 + 3 ^ 40 * 310611 * 2
def baseEnd_310611 : Nat := 141771324065590637096917

theorem tailTrace_310611 : CollatzResearch.WordTrace tailWord_310611 prefixEnd_310611 141771324065590637096917 := by
  unfold tailWord_310611
  simp only [CollatzResearch.WordTrace]
  refine ⟨11328913877716869980531687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7552609251811246653687791 11328913877716869980531687)
  ·
    refine ⟨16993370816575304970797531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11328913877716869980531687 16993370816575304970797531)
    ·
      refine ⟨25490056224862957456196297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16993370816575304970797531 25490056224862957456196297)
      ·
        refine ⟨19117542168647218092147223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25490056224862957456196297 19117542168647218092147223)
        ·
          refine ⟨28676313252970827138220835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19117542168647218092147223 28676313252970827138220835)
          ·
            refine ⟨43014469879456240707331253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28676313252970827138220835 43014469879456240707331253)
            ·
              refine ⟨4032606551199022566312305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43014469879456240707331253 4032606551199022566312305)
              ·
                refine ⟨3024454913399266924734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4032606551199022566312305 3024454913399266924734229)
                ·
                  refine ⟨141771324065590637096917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3024454913399266924734229 141771324065590637096917)
                  ·
                    rfl

theorem cell20_310611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_310611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310611 prefixEnd_310611 := by exact prefixLift 310611
  have htrace : WordTrace (prefixWord ++ tailWord_310611) baseStart_310611 baseEnd_310611 := by
    simpa [prefixWord, tailWord_310611, baseEnd_310611] using wordTrace_append hprefix tailTrace_310611
  have hstable : (prefixWord ++ tailWord_310611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310611).length < 2 ^ (prefixWord ++ tailWord_310611).sum := by decide
  have hdescent : baseEnd_310611 < baseStart_310611 := by decide
  rcases family_descends (prefixWord ++ tailWord_310611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310628 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_310628 : Nat := 118140960795 + 310628 * 2 ^ 59
def prefixEnd_310628 : Nat := 4983230072969 + 3 ^ 40 * 310628 * 2
def baseEnd_310628 : Nat := 141779083328814133530181

theorem tailTrace_310628 : CollatzResearch.WordTrace tailWord_310628 prefixEnd_310628 141779083328814133530181 := by
  unfold tailWord_310628
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664766959327640941950269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7553022612436854589267025 5664766959327640941950269)
  ·
    refine ⟨2124287609747865353231351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5664766959327640941950269 2124287609747865353231351)
    ·
      refine ⟨3186431414621798029847027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124287609747865353231351 3186431414621798029847027)
      ·
        refine ⟨4779647121932697044770541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186431414621798029847027 4779647121932697044770541)
        ·
          refine ⟨1792367670724761391788953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4779647121932697044770541 1792367670724761391788953)
          ·
            refine ⟨1344275753043571043841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792367670724761391788953 1344275753043571043841715)
            ·
              refine ⟨2016413629565356565762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344275753043571043841715 2016413629565356565762573)
              ·
                refine ⟨756155111087008712160965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2016413629565356565762573 756155111087008712160965)
                ·
                  refine ⟨141779083328814133530181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756155111087008712160965 141779083328814133530181)
                  ·
                    rfl

theorem cell20_310628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_310628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310628 prefixEnd_310628 := by exact prefixLift 310628
  have htrace : WordTrace (prefixWord ++ tailWord_310628) baseStart_310628 baseEnd_310628 := by
    simpa [prefixWord, tailWord_310628, baseEnd_310628] using wordTrace_append hprefix tailTrace_310628
  have hstable : (prefixWord ++ tailWord_310628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310628).length < 2 ^ (prefixWord ++ tailWord_310628).sum := by decide
  have hdescent : baseEnd_310628 < baseStart_310628 := by decide
  rcases family_descends (prefixWord ++ tailWord_310628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310658 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_310658 : Nat := 118140960795 + 310658 * 2 ^ 59
def prefixEnd_310658 : Nat := 4983230072969 + 3 ^ 40 * 310658 * 2
def baseEnd_310658 : Nat := 141792776146267362530059

theorem tailTrace_310658 : CollatzResearch.WordTrace tailWord_310658 prefixEnd_310658 141792776146267362530059 := by
  unfold tailWord_310658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832657027136649251873157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7553752072364398004995085 2832657027136649251873157)
  ·
    refine ⟨531123192588121734726217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2832657027136649251873157 531123192588121734726217)
    ·
      refine ⟨398342394441091301044663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 531123192588121734726217 398342394441091301044663)
      ·
        refine ⟨597513591661636951566995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398342394441091301044663 597513591661636951566995)
        ·
          refine ⟨896270387492455427350493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597513591661636951566995 896270387492455427350493)
          ·
            refine ⟨336101395309670785256435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 896270387492455427350493 336101395309670785256435)
            ·
              refine ⟨504152092964506177884653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336101395309670785256435 504152092964506177884653)
              ·
                refine ⟨189057034861689816706745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504152092964506177884653 189057034861689816706745)
                ·
                  refine ⟨141792776146267362530059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189057034861689816706745 141792776146267362530059)
                  ·
                    rfl

theorem cell20_310658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_310658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310658 prefixEnd_310658 := by exact prefixLift 310658
  have htrace : WordTrace (prefixWord ++ tailWord_310658) baseStart_310658 baseEnd_310658 := by
    simpa [prefixWord, tailWord_310658, baseEnd_310658] using wordTrace_append hprefix tailTrace_310658
  have hstable : (prefixWord ++ tailWord_310658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310658).length < 2 ^ (prefixWord ++ tailWord_310658).sum := by decide
  have hdescent : baseEnd_310658 < baseStart_310658 := by decide
  rcases family_descends (prefixWord ++ tailWord_310658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310690 : List Nat := [3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_310690 : Nat := 118140960795 + 310690 * 2 ^ 59
def prefixEnd_310690 : Nat := 4983230072969 + 3 ^ 40 * 310690 * 2
def baseEnd_310690 : Nat := 47269127272739157821087

theorem tailTrace_310690 : CollatzResearch.WordTrace tailWord_310690 prefixEnd_310690 47269127272739157821087 := by
  unfold tailWord_310690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832948811107666618164381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7554530162953777648438349 2832948811107666618164381)
  ·
    refine ⟨1062355804165374981811643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2832948811107666618164381 1062355804165374981811643)
    ·
      refine ⟨1593533706248062472717465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062355804165374981811643 1593533706248062472717465)
      ·
        refine ⟨1195150279686046854538099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1593533706248062472717465 1195150279686046854538099)
        ·
          refine ⟨1792725419529070281807149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195150279686046854538099 1792725419529070281807149)
          ·
            refine ⟨672272032323401355677681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792725419529070281807149 672272032323401355677681)
            ·
              refine ⟨504204024242551016758261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672272032323401355677681 504204024242551016758261)
              ·
                refine ⟨47269127272739157821087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 504204024242551016758261 47269127272739157821087)
                ·
                  rfl

theorem cell20_310690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_310690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310690 prefixEnd_310690 := by exact prefixLift 310690
  have htrace : WordTrace (prefixWord ++ tailWord_310690) baseStart_310690 baseEnd_310690 := by
    simpa [prefixWord, tailWord_310690, baseEnd_310690] using wordTrace_append hprefix tailTrace_310690
  have hstable : (prefixWord ++ tailWord_310690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310690).length < 2 ^ (prefixWord ++ tailWord_310690).sum := by decide
  have hdescent : baseEnd_310690 < baseStart_310690 := by decide
  rcases family_descends (prefixWord ++ tailWord_310690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310766 : List Nat := [4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_310766 : Nat := 118140960795 + 310766 * 2 ^ 59
def prefixEnd_310766 : Nat := 4983230072969 + 3 ^ 40 * 310766 * 2
def baseEnd_310766 : Nat := 47280690096366328976539

theorem tailTrace_310766 : CollatzResearch.WordTrace tailWord_310766 prefixEnd_310766 47280690096366328976539 := by
  unfold tailWord_310766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416820899019416431553019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7556378128103554301616101 1416820899019416431553019)
  ·
    refine ⟨2125231348529124647329529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1416820899019416431553019 2125231348529124647329529)
    ·
      refine ⟨1593923511396843485497147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125231348529124647329529 1593923511396843485497147)
      ·
        refine ⟨2390885267095265228245721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593923511396843485497147 2390885267095265228245721)
        ·
          refine ⟨1793163950321448921184291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2390885267095265228245721 1793163950321448921184291)
          ·
            refine ⟨2689745925482173381776437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793163950321448921184291 2689745925482173381776437)
            ·
              refine ⟨252163680513953754541541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2689745925482173381776437 252163680513953754541541)
              ·
                refine ⟨47280690096366328976539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252163680513953754541541 47280690096366328976539)
                ·
                  rfl

theorem cell20_310766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_310766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310766 prefixEnd_310766 := by exact prefixLift 310766
  have htrace : WordTrace (prefixWord ++ tailWord_310766) baseStart_310766 baseEnd_310766 := by
    simpa [prefixWord, tailWord_310766, baseEnd_310766] using wordTrace_append hprefix tailTrace_310766
  have hstable : (prefixWord ++ tailWord_310766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310766).length < 2 ^ (prefixWord ++ tailWord_310766).sum := by decide
  have hdescent : baseEnd_310766 < baseStart_310766 := by decide
  rcases family_descends (prefixWord ++ tailWord_310766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310818 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_310818 : Nat := 118140960795 + 310818 * 2 ^ 59
def prefixEnd_310818 : Nat := 4983230072969 + 3 ^ 40 * 310818 * 2
def baseEnd_310818 : Nat := 141865804506017917196071

theorem tailTrace_310818 : CollatzResearch.WordTrace tailWord_310818 prefixEnd_310818 141865804506017917196071 := by
  unfold tailWord_310818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834115946991736083329277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7557642525311296222211405 2834115946991736083329277)
  ·
    refine ⟨1062793480121901031248479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2834115946991736083329277 1062793480121901031248479)
    ·
      refine ⟨1594190220182851546872719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062793480121901031248479 1594190220182851546872719)
      ·
        refine ⟨2391285330274277320309079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594190220182851546872719 2391285330274277320309079)
        ·
          refine ⟨3586927995411415980463619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391285330274277320309079 3586927995411415980463619)
          ·
            refine ⟨5380391993117123970695429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586927995411415980463619 5380391993117123970695429)
            ·
              refine ⟨1008823498709460744505393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5380391993117123970695429 1008823498709460744505393)
              ·
                refine ⟨756617624032095558379045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008823498709460744505393 756617624032095558379045)
                ·
                  refine ⟨141865804506017917196071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756617624032095558379045 141865804506017917196071)
                  ·
                    rfl

theorem cell20_310818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_310818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310818 prefixEnd_310818 := by exact prefixLift 310818
  have htrace : WordTrace (prefixWord ++ tailWord_310818) baseStart_310818 baseEnd_310818 := by
    simpa [prefixWord, tailWord_310818, baseEnd_310818] using wordTrace_append hprefix tailTrace_310818
  have hstable : (prefixWord ++ tailWord_310818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310818).length < 2 ^ (prefixWord ++ tailWord_310818).sum := by decide
  have hdescent : baseEnd_310818 < baseStart_310818 := by decide
  rcases family_descends (prefixWord ++ tailWord_310818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310835 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 2]
def baseStart_310835 : Nat := 118140960795 + 310835 * 2 ^ 59
def prefixEnd_310835 : Nat := 4983230072969 + 3 ^ 40 * 310835 * 2
def baseEnd_310835 : Nat := 141873563769241413629335

theorem tailTrace_310835 : CollatzResearch.WordTrace tailWord_310835 prefixEnd_310835 141873563769241413629335 := by
  unfold tailWord_310835
  simp only [CollatzResearch.WordTrace]
  refine ⟨11337083828905356236685959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7558055885936904157790639 11337083828905356236685959)
  ·
    refine ⟨17005625743358034355028939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11337083828905356236685959 17005625743358034355028939)
    ·
      refine ⟨25508438615037051532543409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17005625743358034355028939 25508438615037051532543409)
      ·
        refine ⟨19131328961277788649407557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25508438615037051532543409 19131328961277788649407557)
        ·
          refine ⟨3587124180239585371763917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19131328961277788649407557 3587124180239585371763917)
          ·
            refine ⟨1345171567589844514411469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3587124180239585371763917 1345171567589844514411469)
            ·
              refine ⟨504439337846191692904301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1345171567589844514411469 504439337846191692904301)
              ·
                refine ⟨189164751692321884839113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504439337846191692904301 189164751692321884839113)
                ·
                  refine ⟨141873563769241413629335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189164751692321884839113 141873563769241413629335)
                  ·
                    rfl

theorem cell20_310835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2].length) (baseStart_310835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310835 prefixEnd_310835 := by exact prefixLift 310835
  have htrace : WordTrace (prefixWord ++ tailWord_310835) baseStart_310835 baseEnd_310835 := by
    simpa [prefixWord, tailWord_310835, baseEnd_310835] using wordTrace_append hprefix tailTrace_310835
  have hstable : (prefixWord ++ tailWord_310835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310835).length < 2 ^ (prefixWord ++ tailWord_310835).sum := by decide
  have hdescent : baseEnd_310835 < baseStart_310835 := by decide
  rcases family_descends (prefixWord ++ tailWord_310835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310849 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_310849 : Nat := 118140960795 + 310849 * 2 ^ 59
def prefixEnd_310849 : Nat := 4983230072969 + 3 ^ 40 * 310849 * 2
def baseEnd_310849 : Nat := 141879953750719587162611

theorem tailTrace_310849 : CollatzResearch.WordTrace tailWord_310849 prefixEnd_310849 141879953750719587162611 := by
  unfold tailWord_310849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11337594450854636627695601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7558396300569757751797067 11337594450854636627695601)
  ·
    refine ⟨8503195838140977470771701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11337594450854636627695601 8503195838140977470771701)
    ·
      refine ⟨797174609825716637884847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8503195838140977470771701 797174609825716637884847)
      ·
        refine ⟨1195761914738574956827271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797174609825716637884847 1195761914738574956827271)
        ·
          refine ⟨1793642872107862435240907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195761914738574956827271 1793642872107862435240907)
          ·
            refine ⟨2690464308161793652861361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793642872107862435240907 2690464308161793652861361)
            ·
              refine ⟨2017848231121345239646021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2690464308161793652861361 2017848231121345239646021)
              ·
                refine ⟨378346543335252232433629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2017848231121345239646021 378346543335252232433629)
                ·
                  refine ⟨141879953750719587162611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378346543335252232433629 141879953750719587162611)
                  ·
                    rfl

theorem cell20_310849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_310849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310849 prefixEnd_310849 := by exact prefixLift 310849
  have htrace : WordTrace (prefixWord ++ tailWord_310849) baseStart_310849 baseEnd_310849 := by
    simpa [prefixWord, tailWord_310849, baseEnd_310849] using wordTrace_append hprefix tailTrace_310849
  have hstable : (prefixWord ++ tailWord_310849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310849).length < 2 ^ (prefixWord ++ tailWord_310849).sum := by decide
  have hdescent : baseEnd_310849 < baseStart_310849 := by decide
  rcases family_descends (prefixWord ++ tailWord_310849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310866 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_310866 : Nat := 118140960795 + 310866 * 2 ^ 59
def prefixEnd_310866 : Nat := 4983230072969 + 3 ^ 40 * 310866 * 2
def baseEnd_310866 : Nat := 141887713013943083595875

theorem tailTrace_310866 : CollatzResearch.WordTrace tailWord_310866 prefixEnd_310866 141887713013943083595875 := by
  unfold tailWord_310866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834553622948262132766113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7558809661195365687376301 2834553622948262132766113)
  ·
    refine ⟨2125915217211196599574585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2834553622948262132766113 2125915217211196599574585)
    ·
      refine ⟨1594436412908397449680939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125915217211196599574585 1594436412908397449680939)
      ·
        refine ⟨2391654619362596174521409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594436412908397449680939 2391654619362596174521409)
        ·
          refine ⟨1793740964521947130891057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2391654619362596174521409 1793740964521947130891057)
          ·
            refine ⟨1345305723391460348168293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1793740964521947130891057 1345305723391460348168293)
            ·
              refine ⟨252244823135898815281555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1345305723391460348168293 252244823135898815281555)
              ·
                refine ⟨378367234703848222922333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252244823135898815281555 378367234703848222922333)
                ·
                  refine ⟨141887713013943083595875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378367234703848222922333 141887713013943083595875)
                  ·
                    rfl

theorem cell20_310866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_310866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310866 prefixEnd_310866 := by exact prefixLift 310866
  have htrace : WordTrace (prefixWord ++ tailWord_310866) baseStart_310866 baseEnd_310866 := by
    simpa [prefixWord, tailWord_310866, baseEnd_310866] using wordTrace_append hprefix tailTrace_310866
  have hstable : (prefixWord ++ tailWord_310866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310866).length < 2 ^ (prefixWord ++ tailWord_310866).sum := by decide
  have hdescent : baseEnd_310866 < baseStart_310866 := by decide
  rcases family_descends (prefixWord ++ tailWord_310866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310901 : List Nat := [1, 3, 4, 2, 1, 9]
def baseStart_310901 : Nat := 118140960795 + 310901 * 2 ^ 59
def prefixEnd_310901 : Nat := 4983230072969 + 3 ^ 40 * 310901 * 2
def baseEnd_310901 : Nat := 5255692146949574719595

theorem tailTrace_310901 : CollatzResearch.WordTrace tailWord_310901 prefixEnd_310901 5255692146949574719595 := by
  unfold tailWord_310901
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339491046666249508588557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7559660697777499672392371 11339491046666249508588557)
  ·
    refine ⟨4252309142499843565720709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11339491046666249508588557 4252309142499843565720709)
    ·
      refine ⟨797307964218720668572633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4252309142499843565720709 797307964218720668572633)
      ·
        refine ⟨597980973164040501429475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797307964218720668572633 597980973164040501429475)
        ·
          refine ⟨896971459746060752144213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597980973164040501429475 896971459746060752144213)
          ·
            refine ⟨5255692146949574719595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 896971459746060752144213 5255692146949574719595)
            ·
              rfl

theorem cell20_310901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 9].length) (baseStart_310901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310901 prefixEnd_310901 := by exact prefixLift 310901
  have htrace : WordTrace (prefixWord ++ tailWord_310901) baseStart_310901 baseEnd_310901 := by
    simpa [prefixWord, tailWord_310901, baseEnd_310901] using wordTrace_append hprefix tailTrace_310901
  have hstable : (prefixWord ++ tailWord_310901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310901).length < 2 ^ (prefixWord ++ tailWord_310901).sum := by decide
  have hdescent : baseEnd_310901 < baseStart_310901 := by decide
  rcases family_descends (prefixWord ++ tailWord_310901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310915 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_310915 : Nat := 118140960795 + 310915 * 2 ^ 59
def prefixEnd_310915 : Nat := 4983230072969 + 3 ^ 40 * 310915 * 2
def baseEnd_310915 : Nat := 141910077949116690962341

theorem tailTrace_310915 : CollatzResearch.WordTrace tailWord_310915 prefixEnd_310915 141910077949116690962341 := by
  unfold tailWord_310915
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340001668615529899598199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7560001112410353266398799 11340001668615529899598199)
  ·
    refine ⟨17010002502923294849397299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11340001668615529899598199 17010002502923294849397299)
    ·
      refine ⟨25515003754384942274095949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17010002502923294849397299 25515003754384942274095949)
      ·
        refine ⟨9568126407894353352785981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25515003754384942274095949 9568126407894353352785981)
        ·
          refine ⟨3588047402960382507294743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9568126407894353352785981 3588047402960382507294743)
          ·
            refine ⟨5382071104440573760942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588047402960382507294743 5382071104440573760942115)
            ·
              refine ⟨8073106656660860641413173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382071104440573760942115 8073106656660860641413173)
              ·
                refine ⟨756853749061955685132485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8073106656660860641413173 756853749061955685132485)
                ·
                  refine ⟨141910077949116690962341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756853749061955685132485 141910077949116690962341)
                  ·
                    rfl

theorem cell20_310915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_310915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310915 prefixEnd_310915 := by exact prefixLift 310915
  have htrace : WordTrace (prefixWord ++ tailWord_310915) baseStart_310915 baseEnd_310915 := by
    simpa [prefixWord, tailWord_310915, baseEnd_310915] using wordTrace_append hprefix tailTrace_310915
  have hstable : (prefixWord ++ tailWord_310915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310915).length < 2 ^ (prefixWord ++ tailWord_310915).sum := by decide
  have hdescent : baseEnd_310915 < baseStart_310915 := by decide
  rcases family_descends (prefixWord ++ tailWord_310915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310966 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_310966 : Nat := 118140960795 + 310966 * 2 ^ 59
def prefixEnd_310966 : Nat := 4983230072969 + 3 ^ 40 * 310966 * 2
def baseEnd_310966 : Nat := 141933355738787180262133

theorem tailTrace_310966 : CollatzResearch.WordTrace tailWord_310966 prefixEnd_310966 141933355738787180262133 := by
  unfold tailWord_310966
  simp only [CollatzResearch.WordTrace]
  refine ⟨708866361964422850606547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7561241194287177073136501 708866361964422850606547)
  ·
    refine ⟨1063299542946634275909821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 708866361964422850606547 1063299542946634275909821)
    ·
      refine ⟨398737328604987853466183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1063299542946634275909821 398737328604987853466183)
      ·
        refine ⟨598105992907481780199275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398737328604987853466183 598105992907481780199275)
        ·
          refine ⟨897158989361222670298913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598105992907481780199275 897158989361222670298913)
          ·
            refine ⟨672869242020917002724185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897158989361222670298913 672869242020917002724185)
            ·
              refine ⟨504651931515687752043139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672869242020917002724185 504651931515687752043139)
              ·
                refine ⟨756977897273531628064709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504651931515687752043139 756977897273531628064709)
                ·
                  refine ⟨141933355738787180262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756977897273531628064709 141933355738787180262133)
                  ·
                    rfl

theorem cell20_310966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_310966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310966 prefixEnd_310966 := by exact prefixLift 310966
  have htrace : WordTrace (prefixWord ++ tailWord_310966) baseStart_310966 baseEnd_310966 := by
    simpa [prefixWord, tailWord_310966, baseEnd_310966] using wordTrace_append hprefix tailTrace_310966
  have hstable : (prefixWord ++ tailWord_310966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310966).length < 2 ^ (prefixWord ++ tailWord_310966).sum := by decide
  have hdescent : baseEnd_310966 < baseStart_310966 := by decide
  rcases family_descends (prefixWord ++ tailWord_310966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310970 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_310970 : Nat := 118140960795 + 310970 * 2 ^ 59
def prefixEnd_310970 : Nat := 4983230072969 + 3 ^ 40 * 310970 * 2
def baseEnd_310970 : Nat := 141935181447780944128783

theorem tailTrace_310970 : CollatzResearch.WordTrace tailWord_310970 prefixEnd_310970 141935181447780944128783 := by
  unfold tailWord_310970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835501920854068573212591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7561338455610849528566909 2835501920854068573212591)
  ·
    refine ⟨4253252881281102859818887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835501920854068573212591 4253252881281102859818887)
    ·
      refine ⟨6379879321921654289728331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253252881281102859818887 6379879321921654289728331)
      ·
        refine ⟨9569818982882481434592497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379879321921654289728331 9569818982882481434592497)
        ·
          refine ⟨7177364237161861075944373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9569818982882481434592497 7177364237161861075944373)
          ·
            refine ⟨672877897233924475869785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7177364237161861075944373 672877897233924475869785)
            ·
              refine ⟨504658422925443356902339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672877897233924475869785 504658422925443356902339)
              ·
                refine ⟨756987634388165035353509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504658422925443356902339 756987634388165035353509)
                ·
                  refine ⟨141935181447780944128783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756987634388165035353509 141935181447780944128783)
                  ·
                    rfl

theorem cell20_310970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_310970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310970 prefixEnd_310970 := by exact prefixLift 310970
  have htrace : WordTrace (prefixWord ++ tailWord_310970) baseStart_310970 baseEnd_310970 := by
    simpa [prefixWord, tailWord_310970, baseEnd_310970] using wordTrace_append hprefix tailTrace_310970
  have hstable : (prefixWord ++ tailWord_310970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310970).length < 2 ^ (prefixWord ++ tailWord_310970).sum := by decide
  have hdescent : baseEnd_310970 < baseStart_310970 := by decide
  rcases family_descends (prefixWord ++ tailWord_310970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310980 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_310980 : Nat := 118140960795 + 310980 * 2 ^ 59
def prefixEnd_310980 : Nat := 4983230072969 + 3 ^ 40 * 310980 * 2
def baseEnd_310980 : Nat := 141939745720265353795409

theorem tailTrace_310980 : CollatzResearch.WordTrace tailWord_310980 prefixEnd_310980 141939745720265353795409 := by
  unfold tailWord_310980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671186206690023000357197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7561581608920030667142929 5671186206690023000357197)
  ·
    refine ⟨2126694827508758625133949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5671186206690023000357197 2126694827508758625133949)
    ·
      refine ⟨797510560315784484425231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2126694827508758625133949 797510560315784484425231)
      ·
        refine ⟨1196265840473676726637847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797510560315784484425231 1196265840473676726637847)
        ·
          refine ⟨1794398760710515089956771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196265840473676726637847 1794398760710515089956771)
          ·
            refine ⟨2691598141065772634935157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794398760710515089956771 2691598141065772634935157)
            ·
              refine ⟨252337325724916184525171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2691598141065772634935157 252337325724916184525171)
              ·
                refine ⟨378505988587374276787757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252337325724916184525171 378505988587374276787757)
                ·
                  refine ⟨141939745720265353795409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378505988587374276787757 141939745720265353795409)
                  ·
                    rfl

theorem cell20_310980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_310980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310980 prefixEnd_310980 := by exact prefixLift 310980
  have htrace : WordTrace (prefixWord ++ tailWord_310980) baseStart_310980 baseEnd_310980 := by
    simpa [prefixWord, tailWord_310980, baseEnd_310980] using wordTrace_append hprefix tailTrace_310980
  have hstable : (prefixWord ++ tailWord_310980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310980).length < 2 ^ (prefixWord ++ tailWord_310980).sum := by decide
  have hdescent : baseEnd_310980 < baseStart_310980 := by decide
  rcases family_descends (prefixWord ++ tailWord_310980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310994 : List Nat := [3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_310994 : Nat := 118140960795 + 310994 * 2 ^ 59
def prefixEnd_310994 : Nat := 4983230072969 + 3 ^ 40 * 310994 * 2
def baseEnd_310994 : Nat := 47315378567247842442895

theorem tailTrace_310994 : CollatzResearch.WordTrace tailWord_310994 prefixEnd_310994 47315378567247842442895 := by
  unfold tailWord_310994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835720758832331597931009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7561922023552884261149357 2835720758832331597931009)
  ·
    refine ⟨2126790569124248698448257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2835720758832331597931009 2126790569124248698448257)
    ·
      refine ⟨1595092926843186523836193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126790569124248698448257 1595092926843186523836193)
      ·
        refine ⟨1196319695132389892877145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1595092926843186523836193 1196319695132389892877145)
        ·
          refine ⟨897239771349292419657859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196319695132389892877145 897239771349292419657859)
          ·
            refine ⟨1345859657023938629486789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897239771349292419657859 1345859657023938629486789)
            ·
              refine ⟨252348685691988493028773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1345859657023938629486789 252348685691988493028773)
              ·
                refine ⟨47315378567247842442895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252348685691988493028773 47315378567247842442895)
                ·
                  rfl

theorem cell20_310994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_310994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310994 prefixEnd_310994 := by exact prefixLift 310994
  have htrace : WordTrace (prefixWord ++ tailWord_310994) baseStart_310994 baseEnd_310994 := by
    simpa [prefixWord, tailWord_310994, baseEnd_310994] using wordTrace_append hprefix tailTrace_310994
  have hstable : (prefixWord ++ tailWord_310994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310994).length < 2 ^ (prefixWord ++ tailWord_310994).sum := by decide
  have hdescent : baseEnd_310994 < baseStart_310994 := by decide
  rcases family_descends (prefixWord ++ tailWord_310994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311022 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_311022 : Nat := 118140960795 + 311022 * 2 ^ 59
def prefixEnd_311022 : Nat := 4983230072969 + 3 ^ 40 * 311022 * 2
def baseEnd_311022 : Nat := 141958915664699874395237

theorem tailTrace_311022 : CollatzResearch.WordTrace tailWord_311022 prefixEnd_311022 141958915664699874395237 := by
  unfold tailWord_311022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417988034903485896717915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7562602852818591449162213 1417988034903485896717915)
  ·
    refine ⟨2126982052355228845076873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417988034903485896717915 2126982052355228845076873)
    ·
      refine ⟨1595236539266421633807655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126982052355228845076873 1595236539266421633807655)
      ·
        refine ⟨2392854808899632450711483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595236539266421633807655 2392854808899632450711483)
        ·
          refine ⟨3589282213349448676067225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392854808899632450711483 3589282213349448676067225)
          ·
            refine ⟨2691961660012086507050419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3589282213349448676067225 2691961660012086507050419)
            ·
              refine ⟨4037942490018129760575629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691961660012086507050419 4037942490018129760575629)
              ·
                refine ⟨1514228433756798660215861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4037942490018129760575629 1514228433756798660215861)
                ·
                  refine ⟨141958915664699874395237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1514228433756798660215861 141958915664699874395237)
                  ·
                    rfl

theorem cell20_311022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_311022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311022 prefixEnd_311022 := by exact prefixLift 311022
  have htrace : WordTrace (prefixWord ++ tailWord_311022) baseStart_311022 baseEnd_311022 := by
    simpa [prefixWord, tailWord_311022, baseEnd_311022] using wordTrace_append hprefix tailTrace_311022
  have hstable : (prefixWord ++ tailWord_311022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311022).length < 2 ^ (prefixWord ++ tailWord_311022).sum := by decide
  have hdescent : baseEnd_311022 < baseStart_311022 := by decide
  rcases family_descends (prefixWord ++ tailWord_311022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311039 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 3]
def baseStart_311039 : Nat := 118140960795 + 311039 * 2 ^ 59
def prefixEnd_311039 : Nat := 4983230072969 + 3 ^ 40 * 311039 * 2
def baseEnd_311039 : Nat := 141966674927923370828501

theorem tailTrace_311039 : CollatzResearch.WordTrace tailWord_311039 prefixEnd_311039 141966674927923370828501 := by
  unfold tailWord_311039
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344524320166299077112171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7563016213444199384741447 11344524320166299077112171)
  ·
    refine ⟨17016786480249448615668257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11344524320166299077112171 17016786480249448615668257)
    ·
      refine ⟨12762589860187086461751193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17016786480249448615668257 12762589860187086461751193)
      ·
        refine ⟨9571942395140314846313395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12762589860187086461751193 9571942395140314846313395)
        ·
          refine ⟨14357913592710472269470093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9571942395140314846313395 14357913592710472269470093)
          ·
            refine ⟨5384217597266427101051285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14357913592710472269470093 5384217597266427101051285)
            ·
              refine ⟨252385199871863770361779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5384217597266427101051285 252385199871863770361779)
              ·
                refine ⟨378577799807795655542669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252385199871863770361779 378577799807795655542669)
                ·
                  refine ⟨141966674927923370828501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378577799807795655542669 141966674927923370828501)
                  ·
                    rfl

theorem cell20_311039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_311039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311039 prefixEnd_311039 := by exact prefixLift 311039
  have htrace : WordTrace (prefixWord ++ tailWord_311039) baseStart_311039 baseEnd_311039 := by
    simpa [prefixWord, tailWord_311039, baseEnd_311039] using wordTrace_append hprefix tailTrace_311039
  have hstable : (prefixWord ++ tailWord_311039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311039).length < 2 ^ (prefixWord ++ tailWord_311039).sum := by decide
  have hdescent : baseEnd_311039 < baseStart_311039 := by decide
  rcases family_descends (prefixWord ++ tailWord_311039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311070 : List Nat := [4, 3, 2, 2, 9]
def baseStart_311070 : Nat := 118140960795 + 311070 * 2 ^ 59
def prefixEnd_311070 : Nat := 4983230072969 + 3 ^ 40 * 311070 * 2
def baseEnd_311070 : Nat := 1752849681143519022161

theorem tailTrace_311070 : CollatzResearch.WordTrace tailWord_311070 prefixEnd_311070 1752849681143519022161 := by
  unfold tailWord_311070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418206872881748921436333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7563769988702660914327109 1418206872881748921436333)
  ·
    refine ⟨531827577330655845538625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1418206872881748921436333 531827577330655845538625)
    ·
      refine ⟨398870682997991884153969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 531827577330655845538625 398870682997991884153969)
      ·
        refine ⟨299153012248493913115477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398870682997991884153969 299153012248493913115477)
        ·
          refine ⟨1752849681143519022161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 299153012248493913115477 1752849681143519022161)
          ·
            rfl

theorem cell20_311070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 9].length) (baseStart_311070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311070 prefixEnd_311070 := by exact prefixLift 311070
  have htrace : WordTrace (prefixWord ++ tailWord_311070) baseStart_311070 baseEnd_311070 := by
    simpa [prefixWord, tailWord_311070, baseEnd_311070] using wordTrace_append hprefix tailTrace_311070
  have hstable : (prefixWord ++ tailWord_311070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311070).length < 2 ^ (prefixWord ++ tailWord_311070).sum := by decide
  have hdescent : baseEnd_311070 < baseStart_311070 := by decide
  rcases family_descends (prefixWord ++ tailWord_311070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311077 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_311077 : Nat := 118140960795 + 311077 * 2 ^ 59
def prefixEnd_311077 : Nat := 4983230072969 + 3 ^ 40 * 311077 * 2
def baseEnd_311077 : Nat := 141984019163364127561679

theorem tailTrace_311077 : CollatzResearch.WordTrace tailWord_311077 prefixEnd_311077 141984019163364127561679 := by
  unfold tailWord_311077
  simp only [CollatzResearch.WordTrace]
  refine ⟨11345910294028631566995485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7563940196019087711330323 11345910294028631566995485)
  ·
    refine ⟨4254716360260736837623307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11345910294028631566995485 4254716360260736837623307)
    ·
      refine ⟨6382074540391105256434961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4254716360260736837623307 6382074540391105256434961)
      ·
        refine ⟨4786555905293328942326221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6382074540391105256434961 4786555905293328942326221)
        ·
          refine ⟨1794958464484998353372333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4786555905293328942326221 1794958464484998353372333)
          ·
            refine ⟨673109424181874382514625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1794958464484998353372333 673109424181874382514625)
            ·
              refine ⟨504832068136405786885969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673109424181874382514625 504832068136405786885969)
              ·
                refine ⟨378624051102304340164477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504832068136405786885969 378624051102304340164477)
                ·
                  refine ⟨141984019163364127561679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378624051102304340164477 141984019163364127561679)
                  ·
                    rfl

theorem cell20_311077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_311077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311077 prefixEnd_311077 := by exact prefixLift 311077
  have htrace : WordTrace (prefixWord ++ tailWord_311077) baseStart_311077 baseEnd_311077 := by
    simpa [prefixWord, tailWord_311077, baseEnd_311077] using wordTrace_append hprefix tailTrace_311077
  have hstable : (prefixWord ++ tailWord_311077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311077).length < 2 ^ (prefixWord ++ tailWord_311077).sum := by decide
  have hdescent : baseEnd_311077 < baseStart_311077 := by decide
  rcases family_descends (prefixWord ++ tailWord_311077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311080 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_311080 : Nat := 118140960795 + 311080 * 2 ^ 59
def prefixEnd_311080 : Nat := 4983230072969 + 3 ^ 40 * 311080 * 2
def baseEnd_311080 : Nat := 141985388445109450461667

theorem tailTrace_311080 : CollatzResearch.WordTrace tailWord_311080 prefixEnd_311080 141985388445109450461667 := by
  unfold tailWord_311080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673009856508881539677347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7564013142011842052903129 5673009856508881539677347)
  ·
    refine ⟨8509514784763322309516021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5673009856508881539677347 8509514784763322309516021)
    ·
      refine ⟨797767011071561466517127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8509514784763322309516021 797767011071561466517127)
      ·
        refine ⟨1196650516607342199775691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797767011071561466517127 1196650516607342199775691)
        ·
          refine ⟨1794975774911013299663537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196650516607342199775691 1794975774911013299663537)
          ·
            refine ⟨1346231831183259974747653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794975774911013299663537 1346231831183259974747653)
            ·
              refine ⟨252418468346861245265185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1346231831183259974747653 252418468346861245265185)
              ·
                refine ⟨189313851260145933948889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252418468346861245265185 189313851260145933948889)
                ·
                  refine ⟨141985388445109450461667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189313851260145933948889 141985388445109450461667)
                  ·
                    rfl

theorem cell20_311080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_311080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311080 prefixEnd_311080 := by exact prefixLift 311080
  have htrace : WordTrace (prefixWord ++ tailWord_311080) baseStart_311080 baseEnd_311080 := by
    simpa [prefixWord, tailWord_311080, baseEnd_311080] using wordTrace_append hprefix tailTrace_311080
  have hstable : (prefixWord ++ tailWord_311080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311080).length < 2 ^ (prefixWord ++ tailWord_311080).sum := by decide
  have hdescent : baseEnd_311080 < baseStart_311080 := by decide
  rcases family_descends (prefixWord ++ tailWord_311080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311094 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_311094 : Nat := 118140960795 + 311094 * 2 ^ 59
def prefixEnd_311094 : Nat := 4983230072969 + 3 ^ 40 * 311094 * 2
def baseEnd_311094 : Nat := 141991778426587623994943

theorem tailTrace_311094 : CollatzResearch.WordTrace tailWord_311094 prefixEnd_311094 141991778426587623994943 := by
  unfold tailWord_311094
  simp only [CollatzResearch.WordTrace]
  refine ⟨709158145935440216897771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7564353556644695646909557 709158145935440216897771)
  ·
    refine ⟨1063737218903160325346657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709158145935440216897771 1063737218903160325346657)
    ·
      refine ⟨797802914177370244009993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1063737218903160325346657 797802914177370244009993)
      ·
        refine ⟨598352185633027683007495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797802914177370244009993 598352185633027683007495)
        ·
          refine ⟨897528278449541524511243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598352185633027683007495 897528278449541524511243)
          ·
            refine ⟨1346292417674312286766865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897528278449541524511243 1346292417674312286766865)
            ·
              refine ⟨1009719313255734215075149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346292417674312286766865 1009719313255734215075149)
              ·
                refine ⟨378644742470900330653181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009719313255734215075149 378644742470900330653181)
                ·
                  refine ⟨141991778426587623994943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378644742470900330653181 141991778426587623994943)
                  ·
                    rfl

theorem cell20_311094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_311094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311094 prefixEnd_311094 := by exact prefixLift 311094
  have htrace : WordTrace (prefixWord ++ tailWord_311094) baseStart_311094 baseEnd_311094 := by
    simpa [prefixWord, tailWord_311094, baseEnd_311094] using wordTrace_append hprefix tailTrace_311094
  have hstable : (prefixWord ++ tailWord_311094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311094).length < 2 ^ (prefixWord ++ tailWord_311094).sum := by decide
  have hdescent : baseEnd_311094 < baseStart_311094 := by decide
  rcases family_descends (prefixWord ++ tailWord_311094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311136 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_311136 : Nat := 118140960795 + 311136 * 2 ^ 59
def prefixEnd_311136 : Nat := 4983230072969 + 3 ^ 40 * 311136 * 2
def baseEnd_311136 : Nat := 142010948371022144594771

theorem tailTrace_311136 : CollatzResearch.WordTrace tailWord_311136 prefixEnd_311136 142010948371022144594771 := by
  unfold tailWord_311136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674031100407442321696631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7565374800543256428928841 5674031100407442321696631)
  ·
    refine ⟨8511046650611163482544947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5674031100407442321696631 8511046650611163482544947)
    ·
      refine ⟨12766569975916745223817421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8511046650611163482544947 12766569975916745223817421)
      ·
        refine ⟨4787463740968779458931533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12766569975916745223817421 4787463740968779458931533)
        ·
          refine ⟨1795298902863292297099325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4787463740968779458931533 1795298902863292297099325)
          ·
            refine ⟨673237088573734611412247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1795298902863292297099325 673237088573734611412247)
            ·
              refine ⟨1009855632860601917118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673237088573734611412247 1009855632860601917118371)
              ·
                refine ⟨1514783449290902875677557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009855632860601917118371 1514783449290902875677557)
                ·
                  refine ⟨142010948371022144594771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1514783449290902875677557 142010948371022144594771)
                  ·
                    rfl

theorem cell20_311136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_311136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311136 prefixEnd_311136 := by exact prefixLift 311136
  have htrace : WordTrace (prefixWord ++ tailWord_311136) baseStart_311136 baseEnd_311136 := by
    simpa [prefixWord, tailWord_311136, baseEnd_311136] using wordTrace_append hprefix tailTrace_311136
  have hstable : (prefixWord ++ tailWord_311136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311136).length < 2 ^ (prefixWord ++ tailWord_311136).sum := by decide
  have hdescent : baseEnd_311136 < baseStart_311136 := by decide
  rcases family_descends (prefixWord ++ tailWord_311136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311153 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 3]
def baseStart_311153 : Nat := 118140960795 + 311153 * 2 ^ 59
def prefixEnd_311153 : Nat := 4983230072969 + 3 ^ 40 * 311153 * 2
def baseEnd_311153 : Nat := 142018707634245641028035

theorem tailTrace_311153 : CollatzResearch.WordTrace tailWord_311153 prefixEnd_311153 142018707634245641028035 := by
  unfold tailWord_311153
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348682241753296546762113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7565788161168864364508075 11348682241753296546762113)
  ·
    refine ⟨8511511681314972410071585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11348682241753296546762113 8511511681314972410071585)
    ·
      refine ⟨6383633760986229307553689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8511511681314972410071585 6383633760986229307553689)
      ·
        refine ⟨4787725320739671980665267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6383633760986229307553689 4787725320739671980665267)
        ·
          refine ⟨7181587981109507970997901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787725320739671980665267 7181587981109507970997901)
          ·
            refine ⟨2693095492916065489124213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7181587981109507970997901 2693095492916065489124213)
            ·
              refine ⟨252477702460881139605395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2693095492916065489124213 252477702460881139605395)
              ·
                refine ⟨378716553691321709408093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252477702460881139605395 378716553691321709408093)
                ·
                  refine ⟨142018707634245641028035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378716553691321709408093 142018707634245641028035)
                  ·
                    rfl

theorem cell20_311153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_311153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311153 prefixEnd_311153 := by exact prefixLift 311153
  have htrace : WordTrace (prefixWord ++ tailWord_311153) baseStart_311153 baseEnd_311153 := by
    simpa [prefixWord, tailWord_311153, baseEnd_311153] using wordTrace_append hprefix tailTrace_311153
  have hstable : (prefixWord ++ tailWord_311153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311153).length < 2 ^ (prefixWord ++ tailWord_311153).sum := by decide
  have hdescent : baseEnd_311153 < baseStart_311153 := by decide
  rcases family_descends (prefixWord ++ tailWord_311153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311190 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_311190 : Nat := 118140960795 + 311190 * 2 ^ 59
def prefixEnd_311190 : Nat := 4983230072969 + 3 ^ 40 * 311190 * 2
def baseEnd_311190 : Nat := 142035595442437956794551

theorem tailTrace_311190 : CollatzResearch.WordTrace tailWord_311190 prefixEnd_311190 142035595442437956794551 := by
  unfold tailWord_311190
  simp only [CollatzResearch.WordTrace]
  refine ⟨709376983913703241616189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7566687828412834577239349 709376983913703241616189)
  ·
    refine ⟨266016368967638715606071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 709376983913703241616189 266016368967638715606071)
    ·
      refine ⟨399024553451458073409107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266016368967638715606071 399024553451458073409107)
      ·
        refine ⟨598536830177187110113661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399024553451458073409107 598536830177187110113661)
        ·
          refine ⟨224451311316445166292623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598536830177187110113661 224451311316445166292623)
          ·
            refine ⟨336676966974667749438935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224451311316445166292623 336676966974667749438935)
            ·
              refine ⟨505015450462001624158403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336676966974667749438935 505015450462001624158403)
              ·
                refine ⟨757523175693002436237605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505015450462001624158403 757523175693002436237605)
                ·
                  refine ⟨142035595442437956794551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757523175693002436237605 142035595442437956794551)
                  ·
                    rfl

theorem cell20_311190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_311190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311190 prefixEnd_311190 := by exact prefixLift 311190
  have htrace : WordTrace (prefixWord ++ tailWord_311190) baseStart_311190 baseEnd_311190 := by
    simpa [prefixWord, tailWord_311190, baseEnd_311190] using wordTrace_append hprefix tailTrace_311190
  have hstable : (prefixWord ++ tailWord_311190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311190).length < 2 ^ (prefixWord ++ tailWord_311190).sum := by decide
  have hdescent : baseEnd_311190 < baseStart_311190 := by decide
  rcases family_descends (prefixWord ++ tailWord_311190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311194 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_311194 : Nat := 118140960795 + 311194 * 2 ^ 59
def prefixEnd_311194 : Nat := 4983230072969 + 3 ^ 40 * 311194 * 2
def baseEnd_311194 : Nat := 142037421151431720661201

theorem tailTrace_311194 : CollatzResearch.WordTrace tailWord_311194 prefixEnd_311194 142037421151431720661201 := by
  unfold tailWord_311194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837544408651190137251159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7566785089736507032669757 2837544408651190137251159)
  ·
    refine ⟨4256316612976785205876739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837544408651190137251159 4256316612976785205876739)
    ·
      refine ⟨6384474919465177808815109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256316612976785205876739 6384474919465177808815109)
      ·
        refine ⟨1197089047399720839152833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6384474919465177808815109 1197089047399720839152833)
        ·
          refine ⟨897816785549790629364625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197089047399720839152833 897816785549790629364625)
          ·
            refine ⟨673362589162342972023469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897816785549790629364625 673362589162342972023469)
            ·
              refine ⟨252510970935878614508801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673362589162342972023469 252510970935878614508801)
              ·
                refine ⟨189383228201908960881601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252510970935878614508801 189383228201908960881601)
                ·
                  refine ⟨142037421151431720661201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189383228201908960881601 142037421151431720661201)
                  ·
                    rfl

theorem cell20_311194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_311194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311194 prefixEnd_311194 := by exact prefixLift 311194
  have htrace : WordTrace (prefixWord ++ tailWord_311194) baseStart_311194 baseEnd_311194 := by
    simpa [prefixWord, tailWord_311194, baseEnd_311194] using wordTrace_append hprefix tailTrace_311194
  have hstable : (prefixWord ++ tailWord_311194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311194).length < 2 ^ (prefixWord ++ tailWord_311194).sum := by decide
  have hdescent : baseEnd_311194 < baseStart_311194 := by decide
  rcases family_descends (prefixWord ++ tailWord_311194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311253 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 2]
def baseStart_311253 : Nat := 118140960795 + 311253 * 2 ^ 59
def prefixEnd_311253 : Nat := 4983230072969 + 3 ^ 40 * 311253 * 2
def baseEnd_311253 : Nat := 142064350359089737694293

theorem tailTrace_311253 : CollatzResearch.WordTrace tailWord_311253 prefixEnd_311253 142064350359089737694293 := by
  unfold tailWord_311253
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352329541391013625402413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7568219694260675750268275 11352329541391013625402413)
  ·
    refine ⟨4257123578021630109525905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11352329541391013625402413 4257123578021630109525905)
    ·
      refine ⟨3192842683516222582144429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4257123578021630109525905 3192842683516222582144429)
      ·
        refine ⟨1197316006318583468304161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3192842683516222582144429 1197316006318583468304161)
        ·
          refine ⟨897987004738937601228121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197316006318583468304161 897987004738937601228121)
          ·
            refine ⟨673490253554203200921091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897987004738937601228121 673490253554203200921091)
            ·
              refine ⟨1010235380331304801381637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673490253554203200921091 1010235380331304801381637)
              ·
                refine ⟨189419133812119650259057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1010235380331304801381637 189419133812119650259057)
                ·
                  refine ⟨142064350359089737694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189419133812119650259057 142064350359089737694293)
                  ·
                    rfl

theorem cell20_311253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_311253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311253 prefixEnd_311253 := by exact prefixLift 311253
  have htrace : WordTrace (prefixWord ++ tailWord_311253) baseStart_311253 baseEnd_311253 := by
    simpa [prefixWord, tailWord_311253, baseEnd_311253] using wordTrace_append hprefix tailTrace_311253
  have hstable : (prefixWord ++ tailWord_311253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311253).length < 2 ^ (prefixWord ++ tailWord_311253).sum := by decide
  have hdescent : baseEnd_311253 < baseStart_311253 := by decide
  rcases family_descends (prefixWord ++ tailWord_311253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311277 : List Nat := [1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_311277 : Nat := 118140960795 + 311277 * 2 ^ 59
def prefixEnd_311277 : Nat := 4983230072969 + 3 ^ 40 * 311277 * 2
def baseEnd_311277 : Nat := 47358434871017440298065

theorem tailTrace_311277 : CollatzResearch.WordTrace tailWord_311277 prefixEnd_311277 47358434871017440298065 := by
  unfold tailWord_311277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353204893304065724276085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7568803262202710482850723 11353204893304065724276085)
  ·
    refine ⟨1064362958747256161650883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11353204893304065724276085 1064362958747256161650883)
    ·
      refine ⟨1596544438120884242476325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1064362958747256161650883 1596544438120884242476325)
      ·
        refine ⟨299352082147665795464311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1596544438120884242476325 299352082147665795464311)
        ·
          refine ⟨449028123221498693196467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299352082147665795464311 449028123221498693196467)
          ·
            refine ⟨673542184832248039794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449028123221498693196467 673542184832248039794701)
            ·
              refine ⟨252578319312093014923013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673542184832248039794701 252578319312093014923013)
              ·
                refine ⟨47358434871017440298065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252578319312093014923013 47358434871017440298065)
                ·
                  rfl

theorem cell20_311277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_311277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311277 prefixEnd_311277 := by exact prefixLift 311277
  have htrace : WordTrace (prefixWord ++ tailWord_311277) baseStart_311277 baseEnd_311277 := by
    simpa [prefixWord, tailWord_311277, baseEnd_311277] using wordTrace_append hprefix tailTrace_311277
  have hstable : (prefixWord ++ tailWord_311277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311277).length < 2 ^ (prefixWord ++ tailWord_311277).sum := by decide
  have hdescent : baseEnd_311277 < baseStart_311277 := by decide
  rcases family_descends (prefixWord ++ tailWord_311277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311333 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_311333 : Nat := 118140960795 + 311333 * 2 ^ 59
def prefixEnd_311333 : Nat := 4983230072969 + 3 ^ 40 * 311333 * 2
def baseEnd_311333 : Nat := 142100864538965015027299

theorem tailTrace_311333 : CollatzResearch.WordTrace tailWord_311333 prefixEnd_311333 142100864538965015027299 := by
  unfold tailWord_311333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355247381101187288314653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7570164920734124858876435 11355247381101187288314653)
  ·
    refine ⟨4258217767912945233117995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11355247381101187288314653 4258217767912945233117995)
    ·
      refine ⟨6387326651869417849676993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258217767912945233117995 6387326651869417849676993)
      ·
        refine ⟨4790494988902063387257745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6387326651869417849676993 4790494988902063387257745)
        ·
          refine ⟨3592871241676547540443309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4790494988902063387257745 3592871241676547540443309)
          ·
            refine ⟨1347326715628705327666241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3592871241676547540443309 1347326715628705327666241)
            ·
              refine ⟨1010495036721528995749681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347326715628705327666241 1010495036721528995749681)
              ·
                refine ⟨757871277541146746812261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010495036721528995749681 757871277541146746812261)
                ·
                  refine ⟨142100864538965015027299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757871277541146746812261 142100864538965015027299)
                  ·
                    rfl

theorem cell20_311333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_311333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311333 prefixEnd_311333 := by exact prefixLift 311333
  have htrace : WordTrace (prefixWord ++ tailWord_311333) baseStart_311333 baseEnd_311333 := by
    simpa [prefixWord, tailWord_311333, baseEnd_311333] using wordTrace_append hprefix tailTrace_311333
  have hstable : (prefixWord ++ tailWord_311333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311333).length < 2 ^ (prefixWord ++ tailWord_311333).sum := by decide
  have hdescent : baseEnd_311333 < baseStart_311333 := by decide
  rcases family_descends (prefixWord ++ tailWord_311333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311336 : List Nat := [2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_311336 : Nat := 118140960795 + 311336 * 2 ^ 59
def prefixEnd_311336 : Nat := 4983230072969 + 3 ^ 40 * 311336 * 2
def baseEnd_311336 : Nat := 47367411273570112642429

theorem tailTrace_311336 : CollatzResearch.WordTrace tailWord_311336 prefixEnd_311336 47367411273570112642429 := by
  unfold tailWord_311336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677678400045159400336931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7570237866726879200449241 5677678400045159400336931)
  ·
    refine ⟨8516517600067739100505397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5677678400045159400336931 8516517600067739100505397)
    ·
      refine ⟨798423525006350540672381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8516517600067739100505397 798423525006350540672381)
      ·
        refine ⟨299408821877381452752143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 798423525006350540672381 299408821877381452752143)
        ·
          refine ⟨449113232816072179128215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299408821877381452752143 449113232816072179128215)
          ·
            refine ⟨673669849224108268692323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449113232816072179128215 673669849224108268692323)
            ·
              refine ⟨1010504773836162403038485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673669849224108268692323 1010504773836162403038485)
              ·
                refine ⟨47367411273570112642429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1010504773836162403038485 47367411273570112642429)
                ·
                  rfl

theorem cell20_311336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_311336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311336 prefixEnd_311336 := by exact prefixLift 311336
  have htrace : WordTrace (prefixWord ++ tailWord_311336) baseStart_311336 baseEnd_311336 := by
    simpa [prefixWord, tailWord_311336, baseEnd_311336] using wordTrace_append hprefix tailTrace_311336
  have hstable : (prefixWord ++ tailWord_311336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311336).length < 2 ^ (prefixWord ++ tailWord_311336).sum := by decide
  have hdescent : baseEnd_311336 < baseStart_311336 := by decide
  rcases family_descends (prefixWord ++ tailWord_311336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311347 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_311347 : Nat := 118140960795 + 311347 * 2 ^ 59
def prefixEnd_311347 : Nat := 4983230072969 + 3 ^ 40 * 311347 * 2
def baseEnd_311347 : Nat := 142107254520443188560575

theorem tailTrace_311347 : CollatzResearch.WordTrace tailWord_311347 prefixEnd_311347 142107254520443188560575 := by
  unfold tailWord_311347
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355758003050467679324295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7570505335366978452882863 11355758003050467679324295)
  ·
    refine ⟨17033637004575701518986443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11355758003050467679324295 17033637004575701518986443)
    ·
      refine ⟨25550455506863552278479665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17033637004575701518986443 25550455506863552278479665)
      ·
        refine ⟨19162841630147664208859749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25550455506863552278479665 19162841630147664208859749)
        ·
          refine ⟨3593032805652687039161203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19162841630147664208859749 3593032805652687039161203)
          ·
            refine ⟨5389549208479030558741805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593032805652687039161203 5389549208479030558741805)
            ·
              refine ⟨2021080953179636459528177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5389549208479030558741805 2021080953179636459528177)
              ·
                refine ⟨1515810714884727344646133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021080953179636459528177 1515810714884727344646133)
                ·
                  refine ⟨142107254520443188560575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1515810714884727344646133 142107254520443188560575)
                  ·
                    rfl

theorem cell20_311347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_311347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311347 prefixEnd_311347 := by exact prefixLift 311347
  have htrace : WordTrace (prefixWord ++ tailWord_311347) baseStart_311347 baseEnd_311347 := by
    simpa [prefixWord, tailWord_311347, baseEnd_311347] using wordTrace_append hprefix tailTrace_311347
  have hstable : (prefixWord ++ tailWord_311347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311347).length < 2 ^ (prefixWord ++ tailWord_311347).sum := by decide
  have hdescent : baseEnd_311347 < baseStart_311347 := by decide
  rcases family_descends (prefixWord ++ tailWord_311347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311367 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 2]
def baseStart_311367 : Nat := 118140960795 + 311367 * 2 ^ 59
def prefixEnd_311367 : Nat := 4983230072969 + 3 ^ 40 * 311367 * 2
def baseEnd_311367 : Nat := 142116383065412007893827

theorem tailTrace_311367 : CollatzResearch.WordTrace tailWord_311367 prefixEnd_311367 142116383065412007893827 := by
  unfold tailWord_311367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356487462978011095052355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7570991641985340730034903 11356487462978011095052355)
  ·
    refine ⟨17034731194467016642578533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11356487462978011095052355 17034731194467016642578533)
    ·
      refine ⟨3194012098962565620483475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17034731194467016642578533 3194012098962565620483475)
      ·
        refine ⟨4791018148443848430725213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194012098962565620483475 4791018148443848430725213)
        ·
          refine ⟨1796631805666443161521955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4791018148443848430725213 1796631805666443161521955)
          ·
            refine ⟨2694947708499664742282933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796631805666443161521955 2694947708499664742282933)
            ·
              refine ⟨252651347671843569589025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2694947708499664742282933 252651347671843569589025)
              ·
                refine ⟨189488510753882677191769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252651347671843569589025 189488510753882677191769)
                ·
                  refine ⟨142116383065412007893827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189488510753882677191769 142116383065412007893827)
                  ·
                    rfl

theorem cell20_311367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2].length) (baseStart_311367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311367 prefixEnd_311367 := by exact prefixLift 311367
  have htrace : WordTrace (prefixWord ++ tailWord_311367) baseStart_311367 baseEnd_311367 := by
    simpa [prefixWord, tailWord_311367, baseEnd_311367] using wordTrace_append hprefix tailTrace_311367
  have hstable : (prefixWord ++ tailWord_311367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311367).length < 2 ^ (prefixWord ++ tailWord_311367).sum := by decide
  have hdescent : baseEnd_311367 < baseStart_311367 := by decide
  rcases family_descends (prefixWord ++ tailWord_311367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311381 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 3]
def baseStart_311381 : Nat := 118140960795 + 311381 * 2 ^ 59
def prefixEnd_311381 : Nat := 4983230072969 + 3 ^ 40 * 311381 * 2
def baseEnd_311381 : Nat := 142122773046890181427103

theorem tailTrace_311381 : CollatzResearch.WordTrace tailWord_311381 prefixEnd_311381 142122773046890181427103 := by
  unfold tailWord_311381
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356998084927291486061997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7571332056618194324041331 11356998084927291486061997)
  ·
    refine ⟨4258874281847734307273249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11356998084927291486061997 4258874281847734307273249)
    ·
      refine ⟨3194155711385800730454937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4258874281847734307273249 3194155711385800730454937)
      ·
        refine ⟨2395616783539350547841203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3194155711385800730454937 2395616783539350547841203)
        ·
          refine ⟨3593425175309025821761805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2395616783539350547841203 3593425175309025821761805)
          ·
            refine ⟨1347534440740884683160677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3593425175309025821761805 1347534440740884683160677)
            ·
              refine ⟨252662707638915878092627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1347534440740884683160677 252662707638915878092627)
              ·
                refine ⟨378994061458373817138941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252662707638915878092627 378994061458373817138941)
                ·
                  refine ⟨142122773046890181427103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378994061458373817138941 142122773046890181427103)
                  ·
                    rfl

theorem cell20_311381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_311381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311381 prefixEnd_311381 := by exact prefixLift 311381
  have htrace : WordTrace (prefixWord ++ tailWord_311381) baseStart_311381 baseEnd_311381 := by
    simpa [prefixWord, tailWord_311381, baseEnd_311381] using wordTrace_append hprefix tailTrace_311381
  have hstable : (prefixWord ++ tailWord_311381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311381).length < 2 ^ (prefixWord ++ tailWord_311381).sum := by decide
  have hdescent : baseEnd_311381 < baseStart_311381 := by decide
  rcases family_descends (prefixWord ++ tailWord_311381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311450 : List Nat := [3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_311450 : Nat := 118140960795 + 311450 * 2 ^ 59
def prefixEnd_311450 : Nat := 4983230072969 + 3 ^ 40 * 311450 * 2
def baseEnd_311450 : Nat := 47384755509010869375607

theorem tailTrace_311450 : CollatzResearch.WordTrace tailWord_311450 prefixEnd_311450 47384755509010869375607 := by
  unfold tailWord_311450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839878680419329067580951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7573009814451544180215869 2839878680419329067580951)
  ·
    refine ⟨4259818020628993601371427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839878680419329067580951 4259818020628993601371427)
    ·
      refine ⟨6389727030943490402057141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259818020628993601371427 6389727030943490402057141)
      ·
        refine ⟨599036909150952225192857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6389727030943490402057141 599036909150952225192857)
        ·
          refine ⟨449277681863214168894643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599036909150952225192857 449277681863214168894643)
          ·
            refine ⟨673916522794821253341965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449277681863214168894643 673916522794821253341965)
            ·
              refine ⟨252718696048057970003237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673916522794821253341965 252718696048057970003237)
              ·
                refine ⟨47384755509010869375607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252718696048057970003237 47384755509010869375607)
                ·
                  rfl

theorem cell20_311450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_311450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311450 prefixEnd_311450 := by exact prefixLift 311450
  have htrace : WordTrace (prefixWord ++ tailWord_311450) baseStart_311450 baseEnd_311450 := by
    simpa [prefixWord, tailWord_311450, baseEnd_311450] using wordTrace_append hprefix tailTrace_311450
  have hstable : (prefixWord ++ tailWord_311450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311450).length < 2 ^ (prefixWord ++ tailWord_311450).sum := by decide
  have hdescent : baseEnd_311450 < baseStart_311450 := by decide
  rcases family_descends (prefixWord ++ tailWord_311450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311461 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_311461 : Nat := 118140960795 + 311461 * 2 ^ 59
def prefixEnd_311461 : Nat := 4983230072969 + 3 ^ 40 * 311461 * 2
def baseEnd_311461 : Nat := 142159287226765458760109

theorem tailTrace_311461 : CollatzResearch.WordTrace tailWord_311461 prefixEnd_311461 142159287226765458760109 := by
  unfold tailWord_311461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359915924637465148974237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7573277283091643432649491 11359915924637465148974237)
  ·
    refine ⟨4259968471739049430865339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11359915924637465148974237 4259968471739049430865339)
    ·
      refine ⟨6389952707608574146298009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259968471739049430865339 6389952707608574146298009)
      ·
        refine ⟨4792464530706430609723507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6389952707608574146298009 4792464530706430609723507)
        ·
          refine ⟨7188696796059645914585261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792464530706430609723507 7188696796059645914585261)
          ·
            refine ⟨2695761298522367217969473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7188696796059645914585261 2695761298522367217969473)
            ·
              refine ⟨2021820973891775413477105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2695761298522367217969473 2021820973891775413477105)
              ·
                refine ⟨1516365730418831560107829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021820973891775413477105 1516365730418831560107829)
                ·
                  refine ⟨142159287226765458760109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516365730418831560107829 142159287226765458760109)
                  ·
                    rfl

theorem cell20_311461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_311461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311461 prefixEnd_311461 := by exact prefixLift 311461
  have htrace : WordTrace (prefixWord ++ tailWord_311461) baseStart_311461 baseEnd_311461 := by
    simpa [prefixWord, tailWord_311461, baseEnd_311461] using wordTrace_append hprefix tailTrace_311461
  have hstable : (prefixWord ++ tailWord_311461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311461).length < 2 ^ (prefixWord ++ tailWord_311461).sum := by decide
  have hdescent : baseEnd_311461 < baseStart_311461 := by decide
  rcases family_descends (prefixWord ++ tailWord_311461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311470 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_311470 : Nat := 118140960795 + 311470 * 2 ^ 59
def prefixEnd_311470 : Nat := 4983230072969 + 3 ^ 40 * 311470 * 2
def baseEnd_311470 : Nat := 142163395072001427460073

theorem tailTrace_311470 : CollatzResearch.WordTrace tailWord_311470 prefixEnd_311470 142163395072001427460073 := by
  unfold tailWord_311470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420030522700607460756483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7573496121069906457367909 1420030522700607460756483)
  ·
    refine ⟨2130045784050911191134725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420030522700607460756483 2130045784050911191134725)
    ·
      refine ⟨399383584509545848337761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2130045784050911191134725 399383584509545848337761)
      ·
        refine ⟨299537688382159386253321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399383584509545848337761 299537688382159386253321)
        ·
          refine ⟨224653266286619539689991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299537688382159386253321 224653266286619539689991)
          ·
            refine ⟨336979899429929309534987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224653266286619539689991 336979899429929309534987)
            ·
              refine ⟨505469849144893964302481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336979899429929309534987 505469849144893964302481)
              ·
                refine ⟨379102386858670473226861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505469849144893964302481 379102386858670473226861)
                ·
                  refine ⟨142163395072001427460073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379102386858670473226861 142163395072001427460073)
                  ·
                    rfl

theorem cell20_311470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_311470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311470 prefixEnd_311470 := by exact prefixLift 311470
  have htrace : WordTrace (prefixWord ++ tailWord_311470) baseStart_311470 baseEnd_311470 := by
    simpa [prefixWord, tailWord_311470, baseEnd_311470] using wordTrace_append hprefix tailTrace_311470
  have hstable : (prefixWord ++ tailWord_311470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311470).length < 2 ^ (prefixWord ++ tailWord_311470).sum := by decide
  have hdescent : baseEnd_311470 < baseStart_311470 := by decide
  rcases family_descends (prefixWord ++ tailWord_311470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311509 : List Nat := [1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_311509 : Nat := 118140960795 + 311509 * 2 ^ 59
def prefixEnd_311509 : Nat := 4983230072969 + 3 ^ 40 * 311509 * 2
def baseEnd_311509 : Nat := 47393731911563541719971

theorem tailTrace_311509 : CollatzResearch.WordTrace tailWord_311509 prefixEnd_311509 47393731911563541719971 := by
  unfold tailWord_311509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361666628463569346721581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7574444418975712897814387 11361666628463569346721581)
  ·
    refine ⟨4260624985673838505020593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11361666628463569346721581 4260624985673838505020593)
    ·
      refine ⟨3195468739255378878765445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4260624985673838505020593 3195468739255378878765445)
      ·
        refine ⟨599150388610383539768521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3195468739255378878765445 599150388610383539768521)
        ·
          refine ⟨449362791457787654826391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599150388610383539768521 449362791457787654826391)
          ·
            refine ⟨674044187186681482239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449362791457787654826391 674044187186681482239587)
            ·
              refine ⟨1011066280780022223359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674044187186681482239587 1011066280780022223359381)
              ·
                refine ⟨47393731911563541719971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1011066280780022223359381 47393731911563541719971)
                ·
                  rfl

theorem cell20_311509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_311509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311509 prefixEnd_311509 := by exact prefixLift 311509
  have htrace : WordTrace (prefixWord ++ tailWord_311509) baseStart_311509 baseEnd_311509 := by
    simpa [prefixWord, tailWord_311509, baseEnd_311509] using wordTrace_append hprefix tailTrace_311509
  have hstable : (prefixWord ++ tailWord_311509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311509).length < 2 ^ (prefixWord ++ tailWord_311509).sum := by decide
  have hdescent : baseEnd_311509 < baseStart_311509 := by decide
  rcases family_descends (prefixWord ++ tailWord_311509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311522 : List Nat := [3, 3, 4, 1, 2, 1, 6]
def baseStart_311522 : Nat := 118140960795 + 311522 * 2 ^ 59
def prefixEnd_311522 : Nat := 4983230072969 + 3 ^ 40 * 311522 * 2
def baseEnd_311522 : Nat := 15798569920991150858503

theorem tailTrace_311522 : CollatzResearch.WordTrace tailWord_311522 prefixEnd_311522 15798569920991150858503 := by
  unfold tailWord_311522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840535194354118141736205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7574760518277648377963213 2840535194354118141736205)
  ·
    refine ⟨1065200697882794303151077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2840535194354118141736205 1065200697882794303151077)
    ·
      refine ⟨199725130853023931840827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1065200697882794303151077 199725130853023931840827)
      ·
        refine ⟨299587696279535897761241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199725130853023931840827 299587696279535897761241)
        ·
          refine ⟨224690772209651923320931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299587696279535897761241 224690772209651923320931)
          ·
            refine ⟨337036158314477884981397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224690772209651923320931 337036158314477884981397)
            ·
              refine ⟨15798569920991150858503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 337036158314477884981397 15798569920991150858503)
              ·
                rfl

theorem cell20_311522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 6].length) (baseStart_311522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311522 prefixEnd_311522 := by exact prefixLift 311522
  have htrace : WordTrace (prefixWord ++ tailWord_311522) baseStart_311522 baseEnd_311522 := by
    simpa [prefixWord, tailWord_311522, baseEnd_311522] using wordTrace_append hprefix tailTrace_311522
  have hstable : (prefixWord ++ tailWord_311522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311522).length < 2 ^ (prefixWord ++ tailWord_311522).sum := by decide
  have hdescent : baseEnd_311522 < baseStart_311522 := by decide
  rcases family_descends (prefixWord ++ tailWord_311522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311537 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_311537 : Nat := 118140960795 + 311537 * 2 ^ 59
def prefixEnd_311537 : Nat := 4983230072969 + 3 ^ 40 * 311537 * 2
def baseEnd_311537 : Nat := 142193975697646972226465

theorem tailTrace_311537 : CollatzResearch.WordTrace tailWord_311537 prefixEnd_311537 142193975697646972226465 := by
  unfold tailWord_311537
  simp only [CollatzResearch.WordTrace]
  refine ⟨11362687872362130128740865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7575125248241420085827243 11362687872362130128740865)
  ·
    refine ⟨8522015904271597596555649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11362687872362130128740865 8522015904271597596555649)
    ·
      refine ⟨6391511928203698197416737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8522015904271597596555649 6391511928203698197416737)
      ·
        refine ⟨4793633946152773648062553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6391511928203698197416737 4793633946152773648062553)
        ·
          refine ⟨3595225459614580236046915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4793633946152773648062553 3595225459614580236046915)
          ·
            refine ⟨5392838189421870354070373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595225459614580236046915 5392838189421870354070373)
            ·
              refine ⟨1011157160516600691388195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5392838189421870354070373 1011157160516600691388195)
              ·
                refine ⟨1516735740774901037082293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011157160516600691388195 1516735740774901037082293)
                ·
                  refine ⟨142193975697646972226465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516735740774901037082293 142193975697646972226465)
                  ·
                    rfl

theorem cell20_311537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_311537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311537 prefixEnd_311537 := by exact prefixLift 311537
  have htrace : WordTrace (prefixWord ++ tailWord_311537) baseStart_311537 baseEnd_311537 := by
    simpa [prefixWord, tailWord_311537, baseEnd_311537] using wordTrace_append hprefix tailTrace_311537
  have hstable : (prefixWord ++ tailWord_311537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311537).length < 2 ^ (prefixWord ++ tailWord_311537).sum := by decide
  have hdescent : baseEnd_311537 < baseStart_311537 := by decide
  rcases family_descends (prefixWord ++ tailWord_311537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311589 : List Nat := [1, 3, 1, 2, 13]
def baseStart_311589 : Nat := 118140960795 + 311589 * 2 ^ 59
def prefixEnd_311589 : Nat := 4983230072969 + 3 ^ 40 * 311589 * 2
def baseEnd_311589 : Nat := 1755774196476122252999

theorem tailTrace_311589 : CollatzResearch.WordTrace tailWord_311589 prefixEnd_311589 1755774196476122252999 := by
  unfold tailWord_311589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364584468173743009633821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7576389645449162006422547 11364584468173743009633821)
  ·
    refine ⟨4261719175565153628612683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11364584468173743009633821 4261719175565153628612683)
    ·
      refine ⟨6392578763347730442919025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261719175565153628612683 6392578763347730442919025)
      ·
        refine ⟨4794434072510797832189269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6392578763347730442919025 4794434072510797832189269)
        ·
          refine ⟨1755774196476122252999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4794434072510797832189269 1755774196476122252999)
          ·
            rfl

theorem cell20_311589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 13].length) (baseStart_311589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311589 prefixEnd_311589 := by exact prefixLift 311589
  have htrace : WordTrace (prefixWord ++ tailWord_311589) baseStart_311589 baseEnd_311589 := by
    simpa [prefixWord, tailWord_311589, baseEnd_311589] using wordTrace_append hprefix tailTrace_311589
  have hstable : (prefixWord ++ tailWord_311589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311589).length < 2 ^ (prefixWord ++ tailWord_311589).sum := by decide
  have hdescent : baseEnd_311589 < baseStart_311589 := by decide
  rcases family_descends (prefixWord ++ tailWord_311589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311591 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 2]
def baseStart_311591 : Nat := 118140960795 + 311591 * 2 ^ 59
def prefixEnd_311591 : Nat := 4983230072969 + 3 ^ 40 * 311591 * 2
def baseEnd_311591 : Nat := 142218622769062784426245

theorem tailTrace_311591 : CollatzResearch.WordTrace tailWord_311591 prefixEnd_311591 142218622769062784426245 := by
  unfold tailWord_311591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364657414166497351206627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7576438276110998234137751 11364657414166497351206627)
  ·
    refine ⟨17046986121249746026809941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11364657414166497351206627 17046986121249746026809941)
    ·
      refine ⟨199769368608395461251679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 17046986121249746026809941 199769368608395461251679)
      ·
        refine ⟨299654052912593191877519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199769368608395461251679 299654052912593191877519)
        ·
          refine ⟨449481079368889787816279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299654052912593191877519 449481079368889787816279)
          ·
            refine ⟨674221619053334681724419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449481079368889787816279 674221619053334681724419)
            ·
              refine ⟨1011332428580002022586629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674221619053334681724419 1011332428580002022586629)
              ·
                refine ⟨189624830358750379234993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1011332428580002022586629 189624830358750379234993)
                ·
                  refine ⟨142218622769062784426245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189624830358750379234993 142218622769062784426245)
                  ·
                    rfl

theorem cell20_311591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2].length) (baseStart_311591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311591 prefixEnd_311591 := by exact prefixLift 311591
  have htrace : WordTrace (prefixWord ++ tailWord_311591) baseStart_311591 baseEnd_311591 := by
    simpa [prefixWord, tailWord_311591, baseEnd_311591] using wordTrace_append hprefix tailTrace_311591
  have hstable : (prefixWord ++ tailWord_311591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311591).length < 2 ^ (prefixWord ++ tailWord_311591).sum := by decide
  have hdescent : baseEnd_311591 < baseStart_311591 := by decide
  rcases family_descends (prefixWord ++ tailWord_311591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311602 : List Nat := [3, 2, 1, 1, 6, 1, 1, 5]
def baseStart_311602 : Nat := 118140960795 + 311602 * 2 ^ 59
def prefixEnd_311602 : Nat := 4983230072969 + 3 ^ 40 * 311602 * 2
def baseEnd_311602 : Nat := 47407881156265211686511

theorem tailTrace_311602 : CollatzResearch.WordTrace tailWord_311602 prefixEnd_311602 47407881156265211686511 := by
  unfold tailWord_311602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841264654281661557464265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7576705744751097486571373 2841264654281661557464265)
  ·
    refine ⟨2130948490711246168098199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2841264654281661557464265 2130948490711246168098199)
    ·
      refine ⟨3196422736066869252147299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130948490711246168098199 3196422736066869252147299)
      ·
        refine ⟨4794634104100303878220949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196422736066869252147299 4794634104100303878220949)
        ·
          refine ⟨224748473629701744291607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4794634104100303878220949 224748473629701744291607)
          ·
            refine ⟨337122710444552616437411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224748473629701744291607 337122710444552616437411)
            ·
              refine ⟨505684065666828924656117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337122710444552616437411 505684065666828924656117)
              ·
                refine ⟨47407881156265211686511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505684065666828924656117 47407881156265211686511)
                ·
                  rfl

theorem cell20_311602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_311602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311602 prefixEnd_311602 := by exact prefixLift 311602
  have htrace : WordTrace (prefixWord ++ tailWord_311602) baseStart_311602 baseEnd_311602 := by
    simpa [prefixWord, tailWord_311602, baseEnd_311602] using wordTrace_append hprefix tailTrace_311602
  have hstable : (prefixWord ++ tailWord_311602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311602).length < 2 ^ (prefixWord ++ tailWord_311602).sum := by decide
  have hdescent : baseEnd_311602 < baseStart_311602 := by decide
  rcases family_descends (prefixWord ++ tailWord_311602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311651 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_311651 : Nat := 118140960795 + 311651 * 2 ^ 59
def prefixEnd_311651 : Nat := 4983230072969 + 3 ^ 40 * 311651 * 2
def baseEnd_311651 : Nat := 142246008403969242425999

theorem tailTrace_311651 : CollatzResearch.WordTrace tailWord_311651 prefixEnd_311651 142246008403969242425999 := by
  unfold tailWord_311651
  simp only [CollatzResearch.WordTrace]
  refine ⟨11366845793949127598390807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7577897195966085065593871 11366845793949127598390807)
  ·
    refine ⟨17050268690923691397586211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11366845793949127598390807 17050268690923691397586211)
    ·
      refine ⟨25575403036385537096379317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17050268690923691397586211 25575403036385537096379317)
      ·
        refine ⟨2397694034661144102785561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25575403036385537096379317 2397694034661144102785561)
        ·
          refine ⟨1798270525995858077089171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397694034661144102785561 1798270525995858077089171)
          ·
            refine ⟨2697405788993787115633757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798270525995858077089171 2697405788993787115633757)
            ·
              refine ⟨1011527170872670168362659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2697405788993787115633757 1011527170872670168362659)
              ·
                refine ⟨1517290756309005252543989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011527170872670168362659 1517290756309005252543989)
                ·
                  refine ⟨142246008403969242425999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517290756309005252543989 142246008403969242425999)
                  ·
                    rfl

theorem cell20_311651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_311651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311651 prefixEnd_311651 := by exact prefixLift 311651
  have htrace : WordTrace (prefixWord ++ tailWord_311651) baseStart_311651 baseEnd_311651 := by
    simpa [prefixWord, tailWord_311651, baseEnd_311651] using wordTrace_append hprefix tailTrace_311651
  have hstable : (prefixWord ++ tailWord_311651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311651).length < 2 ^ (prefixWord ++ tailWord_311651).sum := by decide
  have hdescent : baseEnd_311651 < baseStart_311651 := by decide
  rcases family_descends (prefixWord ++ tailWord_311651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311665 : List Nat := [1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_311665 : Nat := 118140960795 + 311665 * 2 ^ 59
def prefixEnd_311665 : Nat := 4983230072969 + 3 ^ 40 * 311665 * 2
def baseEnd_311665 : Nat := 47417466128482471986425

theorem tailTrace_311665 : CollatzResearch.WordTrace tailWord_311665 prefixEnd_311665 47417466128482471986425 := by
  unfold tailWord_311665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367356415898407989400449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7578237610598938659600299 11367356415898407989400449)
  ·
    refine ⟨8525517311923805992050337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11367356415898407989400449 8525517311923805992050337)
    ·
      refine ⟨6394137983942854494037753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8525517311923805992050337 6394137983942854494037753)
      ·
        refine ⟨4795603487957140870528315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6394137983942854494037753 4795603487957140870528315)
        ·
          refine ⟨7193405231935711305792473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795603487957140870528315 7193405231935711305792473)
          ·
            refine ⟨5395053923951783479344355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7193405231935711305792473 5395053923951783479344355)
            ·
              refine ⟨8092580885927675219016533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395053923951783479344355 8092580885927675219016533)
              ·
                refine ⟨47417466128482471986425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8092580885927675219016533 47417466128482471986425)
                ·
                  rfl

theorem cell20_311665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_311665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311665 prefixEnd_311665 := by exact prefixLift 311665
  have htrace : WordTrace (prefixWord ++ tailWord_311665) baseStart_311665 baseEnd_311665 := by
    simpa [prefixWord, tailWord_311665, baseEnd_311665] using wordTrace_append hprefix tailTrace_311665
  have hstable : (prefixWord ++ tailWord_311665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311665).length < 2 ^ (prefixWord ++ tailWord_311665).sum := by decide
  have hdescent : baseEnd_311665 < baseStart_311665 := by decide
  rcases family_descends (prefixWord ++ tailWord_311665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311689 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_311689 : Nat := 118140960795 + 311689 * 2 ^ 59
def prefixEnd_311689 : Nat := 4983230072969 + 3 ^ 40 * 311689 * 2
def baseEnd_311689 : Nat := 142263352639409999159177

theorem tailTrace_311689 : CollatzResearch.WordTrace tailWord_311689 prefixEnd_311689 142263352639409999159177 := by
  unfold tailWord_311689
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368231767811460088274121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7578821178540973392182747 11368231767811460088274121)
  ·
    refine ⟨8526173825858595066205591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11368231767811460088274121 8526173825858595066205591)
    ·
      refine ⟨12789260738787892599308387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8526173825858595066205591 12789260738787892599308387)
      ·
        refine ⟨19183891108181838898962581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12789260738787892599308387 19183891108181838898962581)
        ·
          refine ⟨899244895696023698388871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19183891108181838898962581 899244895696023698388871)
          ·
            refine ⟨1348867343544035547583307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899244895696023698388871 1348867343544035547583307)
            ·
              refine ⟨2023301015316053321374961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348867343544035547583307 2023301015316053321374961)
              ·
                refine ⟨1517475761487039991031221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023301015316053321374961 1517475761487039991031221)
                ·
                  refine ⟨142263352639409999159177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517475761487039991031221 142263352639409999159177)
                  ·
                    rfl

theorem cell20_311689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_311689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311689 prefixEnd_311689 := by exact prefixLift 311689
  have htrace : WordTrace (prefixWord ++ tailWord_311689) baseStart_311689 baseEnd_311689 := by
    simpa [prefixWord, tailWord_311689, baseEnd_311689] using wordTrace_append hprefix tailTrace_311689
  have hstable : (prefixWord ++ tailWord_311689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311689).length < 2 ^ (prefixWord ++ tailWord_311689).sum := by decide
  have hdescent : baseEnd_311689 < baseStart_311689 := by decide
  rcases family_descends (prefixWord ++ tailWord_311689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311692 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_311692 : Nat := 118140960795 + 311692 * 2 ^ 59
def prefixEnd_311692 : Nat := 4983230072969 + 3 ^ 40 * 311692 * 2
def baseEnd_311692 : Nat := 142264721921155322059165

theorem tailTrace_311692 : CollatzResearch.WordTrace tailWord_311692 prefixEnd_311692 142264721921155322059165 := by
  unfold tailWord_311692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684170593400295800316665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7578894124533727733755553 5684170593400295800316665)
  ·
    refine ⟨4263127945050221850237499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5684170593400295800316665 4263127945050221850237499)
    ·
      refine ⟨6394691917575332775356249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4263127945050221850237499 6394691917575332775356249)
      ·
        refine ⟨4796018938181499581517187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6394691917575332775356249 4796018938181499581517187)
        ·
          refine ⟨7194028407272249372275781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796018938181499581517187 7194028407272249372275781)
          ·
            refine ⟨1348880326363546757301709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7194028407272249372275781 1348880326363546757301709)
            ·
              refine ⟨505830122386330033988141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1348880326363546757301709 505830122386330033988141)
              ·
                refine ⟨189686295894873762745553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 505830122386330033988141 189686295894873762745553)
                ·
                  refine ⟨142264721921155322059165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189686295894873762745553 142264721921155322059165)
                  ·
                    rfl

theorem cell20_311692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_311692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311692 prefixEnd_311692 := by exact prefixLift 311692
  have htrace : WordTrace (prefixWord ++ tailWord_311692) baseStart_311692 baseEnd_311692 := by
    simpa [prefixWord, tailWord_311692, baseEnd_311692] using wordTrace_append hprefix tailTrace_311692
  have hstable : (prefixWord ++ tailWord_311692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311692).length < 2 ^ (prefixWord ++ tailWord_311692).sum := by decide
  have hdescent : baseEnd_311692 < baseStart_311692 := by decide
  rcases family_descends (prefixWord ++ tailWord_311692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311703 : List Nat := [1, 1, 3, 3, 1, 1, 10]
def baseStart_311703 : Nat := 118140960795 + 311703 * 2 ^ 59
def prefixEnd_311703 : Nat := 4983230072969 + 3 ^ 40 * 311703 * 2
def baseEnd_311703 : Nat := 15807749180098685854717

theorem tailTrace_311703 : CollatzResearch.WordTrace tailWord_311703 prefixEnd_311703 15807749180098685854717 := by
  unfold tailWord_311703
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368742389760740479283763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7579161593173826986189175 11368742389760740479283763)
  ·
    refine ⟨17053113584641110718925645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11368742389760740479283763 17053113584641110718925645)
    ·
      refine ⟨6394917594240416519597117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17053113584641110718925645 6394917594240416519597117)
      ·
        refine ⟨2398094097840156194848919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6394917594240416519597117 2398094097840156194848919)
        ·
          refine ⟨3597141146760234292273379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398094097840156194848919 3597141146760234292273379)
          ·
            refine ⟨5395711720140351438410069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597141146760234292273379 5395711720140351438410069)
            ·
              refine ⟨15807749180098685854717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5395711720140351438410069 15807749180098685854717)
              ·
                rfl

theorem cell20_311703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_311703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311703 prefixEnd_311703 := by exact prefixLift 311703
  have htrace : WordTrace (prefixWord ++ tailWord_311703) baseStart_311703 baseEnd_311703 := by
    simpa [prefixWord, tailWord_311703, baseEnd_311703] using wordTrace_append hprefix tailTrace_311703
  have hstable : (prefixWord ++ tailWord_311703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311703).length < 2 ^ (prefixWord ++ tailWord_311703).sum := by decide
  have hdescent : baseEnd_311703 < baseStart_311703 := by decide
  rcases family_descends (prefixWord ++ tailWord_311703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311709 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 4]
def baseStart_311709 : Nat := 118140960795 + 311709 * 2 ^ 59
def prefixEnd_311709 : Nat := 4983230072969 + 3 ^ 40 * 311709 * 2
def baseEnd_311709 : Nat := 142272481184378818492429

theorem tailTrace_311709 : CollatzResearch.WordTrace tailWord_311709 prefixEnd_311709 142272481184378818492429 := by
  unfold tailWord_311709
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368961227739003504002181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7579307485159335669334787 11368961227739003504002181)
  ·
    refine ⟨2131680230201063157000409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11368961227739003504002181 2131680230201063157000409)
    ·
      refine ⟨1598760172650797367750307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2131680230201063157000409 1598760172650797367750307)
      ·
        refine ⟨2398140258976196051625461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598760172650797367750307 2398140258976196051625461)
        ·
          refine ⟨224825649279018379839887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2398140258976196051625461 224825649279018379839887)
          ·
            refine ⟨337238473918527569759831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224825649279018379839887 337238473918527569759831)
            ·
              refine ⟨505857710877791354639747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337238473918527569759831 505857710877791354639747)
              ·
                refine ⟨758786566316687031959621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505857710877791354639747 758786566316687031959621)
                ·
                  refine ⟨142272481184378818492429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758786566316687031959621 142272481184378818492429)
                  ·
                    rfl

theorem cell20_311709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_311709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311709 prefixEnd_311709 := by exact prefixLift 311709
  have htrace : WordTrace (prefixWord ++ tailWord_311709) baseStart_311709 baseEnd_311709 := by
    simpa [prefixWord, tailWord_311709, baseEnd_311709] using wordTrace_append hprefix tailTrace_311709
  have hstable : (prefixWord ++ tailWord_311709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311709).length < 2 ^ (prefixWord ++ tailWord_311709).sum := by decide
  have hdescent : baseEnd_311709 < baseStart_311709 := by decide
  rcases family_descends (prefixWord ++ tailWord_311709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311764 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_311764 : Nat := 118140960795 + 311764 * 2 ^ 59
def prefixEnd_311764 : Nat := 4983230072969 + 3 ^ 40 * 311764 * 2
def baseEnd_311764 : Nat := 142297584683043071658871

theorem tailTrace_311764 : CollatzResearch.WordTrace tailWord_311764 prefixEnd_311764 142297584683043071658871 := by
  unfold tailWord_311764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685483621269873948627173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7580644828359831931502897 5685483621269873948627173)
  ·
    refine ⟨1066028178988101365367595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5685483621269873948627173 1066028178988101365367595)
    ·
      refine ⟨1599042268482152048051393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066028178988101365367595 1599042268482152048051393)
      ·
        refine ⟨1199281701361614036038545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599042268482152048051393 1199281701361614036038545)
        ·
          refine ⟨899461276021210527028909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1199281701361614036038545 899461276021210527028909)
          ·
            refine ⟨337297978507953947635841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 899461276021210527028909 337297978507953947635841)
            ·
              refine ⟨252973483880965460726881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337297978507953947635841 252973483880965460726881)
              ·
                refine ⟨189730112910724095545161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252973483880965460726881 189730112910724095545161)
                ·
                  refine ⟨142297584683043071658871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189730112910724095545161 142297584683043071658871)
                  ·
                    rfl

theorem cell20_311764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_311764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311764 prefixEnd_311764 := by exact prefixLift 311764
  have htrace : WordTrace (prefixWord ++ tailWord_311764) baseStart_311764 baseEnd_311764 := by
    simpa [prefixWord, tailWord_311764, baseEnd_311764] using wordTrace_append hprefix tailTrace_311764
  have hstable : (prefixWord ++ tailWord_311764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311764).length < 2 ^ (prefixWord ++ tailWord_311764).sum := by decide
  have hdescent : baseEnd_311764 < baseStart_311764 := by decide
  rcases family_descends (prefixWord ++ tailWord_311764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311789 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_311789 : Nat := 118140960795 + 311789 * 2 ^ 59
def prefixEnd_311789 : Nat := 4983230072969 + 3 ^ 40 * 311789 * 2
def baseEnd_311789 : Nat := 142308995364254095825435

theorem tailTrace_311789 : CollatzResearch.WordTrace tailWord_311789 prefixEnd_311789 142308995364254095825435 := by
  unfold tailWord_311789
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371879067449177166914421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7581252711632784777942947 11371879067449177166914421)
  ·
    refine ⟨1066113662573360359398227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11371879067449177166914421 1066113662573360359398227)
    ·
      refine ⟨1599170493860040539097341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066113662573360359398227 1599170493860040539097341)
      ·
        refine ⟨599688935197515202161503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1599170493860040539097341 599688935197515202161503)
        ·
          refine ⟨899533402796272803242255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599688935197515202161503 899533402796272803242255)
          ·
            refine ⟨1349300104194409204863383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899533402796272803242255 1349300104194409204863383)
            ·
              refine ⟨2023950156291613807295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349300104194409204863383 2023950156291613807295075)
              ·
                refine ⟨3035925234437420710942613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023950156291613807295075 3035925234437420710942613)
                ·
                  refine ⟨142308995364254095825435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3035925234437420710942613 142308995364254095825435)
                  ·
                    rfl

theorem cell20_311789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_311789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311789 prefixEnd_311789 := by exact prefixLift 311789
  have htrace : WordTrace (prefixWord ++ tailWord_311789) baseStart_311789 baseEnd_311789 := by
    simpa [prefixWord, tailWord_311789, baseEnd_311789] using wordTrace_append hprefix tailTrace_311789
  have hstable : (prefixWord ++ tailWord_311789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311789).length < 2 ^ (prefixWord ++ tailWord_311789).sum := by decide
  have hdescent : baseEnd_311789 < baseStart_311789 := by decide
  rcases family_descends (prefixWord ++ tailWord_311789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311820 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_311820 : Nat := 118140960795 + 311820 * 2 ^ 59
def prefixEnd_311820 : Nat := 4983230072969 + 3 ^ 40 * 311820 * 2
def baseEnd_311820 : Nat := 142323144608955765791975

theorem tailTrace_311820 : CollatzResearch.WordTrace tailWord_311820 prefixEnd_311820 142323144608955765791975 := by
  unfold tailWord_311820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686504865168434730646457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7582006486891246307528609 5686504865168434730646457)
  ·
    refine ⟨4264878648876326047984843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5686504865168434730646457 4264878648876326047984843)
    ·
      refine ⟨6397317973314489071977265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264878648876326047984843 6397317973314489071977265)
      ·
        refine ⟨4797988479985866803982949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6397317973314489071977265 4797988479985866803982949)
        ·
          refine ⟨899622839997350025746803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4797988479985866803982949 899622839997350025746803)
          ·
            refine ⟨1349434259996025038620205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899622839997350025746803 1349434259996025038620205)
            ·
              refine ⟨506037847498509389482577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1349434259996025038620205 506037847498509389482577)
              ·
                refine ⟨379528385623882042111933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506037847498509389482577 379528385623882042111933)
                ·
                  refine ⟨142323144608955765791975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379528385623882042111933 142323144608955765791975)
                  ·
                    rfl

theorem cell20_311820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_311820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311820 prefixEnd_311820 := by exact prefixLift 311820
  have htrace : WordTrace (prefixWord ++ tailWord_311820) baseStart_311820 baseEnd_311820 := by
    simpa [prefixWord, tailWord_311820, baseEnd_311820] using wordTrace_append hprefix tailTrace_311820
  have hstable : (prefixWord ++ tailWord_311820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311820).length < 2 ^ (prefixWord ++ tailWord_311820).sum := by decide
  have hdescent : baseEnd_311820 < baseStart_311820 := by decide
  rcases family_descends (prefixWord ++ tailWord_311820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311827 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 2]
def baseStart_311827 : Nat := 118140960795 + 311827 * 2 ^ 59
def prefixEnd_311827 : Nat := 4983230072969 + 3 ^ 40 * 311827 * 2
def baseEnd_311827 : Nat := 142326339599694852558613

theorem tailTrace_311827 : CollatzResearch.WordTrace tailWord_311827 prefixEnd_311827 142326339599694852558613 := by
  unfold tailWord_311827
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373265041311509656797735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7582176694207673104531823 11373265041311509656797735)
  ·
    refine ⟨17059897561967264485196603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373265041311509656797735 17059897561967264485196603)
    ·
      refine ⟨25589846342950896727794905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17059897561967264485196603 25589846342950896727794905)
      ·
        refine ⟨19192384757213172545846179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25589846342950896727794905 19192384757213172545846179)
        ·
          refine ⟨28788577135819758818769269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19192384757213172545846179 28788577135819758818769269)
          ·
            refine ⟨2698929106483102389259619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28788577135819758818769269 2698929106483102389259619)
            ·
              refine ⟨4048393659724653583889429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698929106483102389259619 4048393659724653583889429)
              ·
                refine ⟨189768452799593136744817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4048393659724653583889429 189768452799593136744817)
                ·
                  refine ⟨142326339599694852558613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189768452799593136744817 142326339599694852558613)
                  ·
                    rfl

theorem cell20_311827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2].length) (baseStart_311827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311827 prefixEnd_311827 := by exact prefixLift 311827
  have htrace : WordTrace (prefixWord ++ tailWord_311827) baseStart_311827 baseEnd_311827 := by
    simpa [prefixWord, tailWord_311827, baseEnd_311827] using wordTrace_append hprefix tailTrace_311827
  have hstable : (prefixWord ++ tailWord_311827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311827).length < 2 ^ (prefixWord ++ tailWord_311827).sum := by decide
  have hdescent : baseEnd_311827 < baseStart_311827 := by decide
  rcases family_descends (prefixWord ++ tailWord_311827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311837 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 3]
def baseStart_311837 : Nat := 118140960795 + 311837 * 2 ^ 59
def prefixEnd_311837 : Nat := 4983230072969 + 3 ^ 40 * 311837 * 2
def baseEnd_311837 : Nat := 142330903872179262225239

theorem tailTrace_311837 : CollatzResearch.WordTrace tailWord_311837 prefixEnd_311837 142330903872179262225239 := by
  unfold tailWord_311837
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373629771275281364661765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7582419847516854243107843 11373629771275281364661765)
  ·
    refine ⟨2132555582114115255874081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11373629771275281364661765 2132555582114115255874081)
    ·
      refine ⟨1599416686585586441905561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2132555582114115255874081 1599416686585586441905561)
      ·
        refine ⟨1199562514939189831429171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599416686585586441905561 1199562514939189831429171)
        ·
          refine ⟨1799343772408784747143757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199562514939189831429171 1799343772408784747143757)
          ·
            refine ⟨674753914653294280178909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1799343772408784747143757 674753914653294280178909)
            ·
              refine ⟨253032717994985355067091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674753914653294280178909 253032717994985355067091)
              ·
                refine ⟨379549076992478032600637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253032717994985355067091 379549076992478032600637)
                ·
                  refine ⟨142330903872179262225239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379549076992478032600637 142330903872179262225239)
                  ·
                    rfl

theorem cell20_311837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_311837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311837 prefixEnd_311837 := by exact prefixLift 311837
  have htrace : WordTrace (prefixWord ++ tailWord_311837) baseStart_311837 baseEnd_311837 := by
    simpa [prefixWord, tailWord_311837, baseEnd_311837] using wordTrace_append hprefix tailTrace_311837
  have hstable : (prefixWord ++ tailWord_311837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311837).length < 2 ^ (prefixWord ++ tailWord_311837).sum := by decide
  have hdescent : baseEnd_311837 < baseStart_311837 := by decide
  rcases family_descends (prefixWord ++ tailWord_311837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311847 : List Nat := [1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_311847 : Nat := 118140960795 + 311847 * 2 ^ 59
def prefixEnd_311847 : Nat := 4983230072969 + 3 ^ 40 * 311847 * 2
def baseEnd_311847 : Nat := 47445156048221223963955

theorem tailTrace_311847 : CollatzResearch.WordTrace tailWord_311847 prefixEnd_311847 47445156048221223963955 := by
  unfold tailWord_311847
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373994501239053072525795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7582663000826035381683863 11373994501239053072525795)
  ·
    refine ⟨17060991751858579608788693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373994501239053072525795 17060991751858579608788693)
    ·
      refine ⟨399866994184185459580985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17060991751858579608788693 399866994184185459580985)
      ·
        refine ⟨299900245638139094685739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399866994184185459580985 299900245638139094685739)
        ·
          refine ⟨449850368457208642028609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299900245638139094685739 449850368457208642028609)
          ·
            refine ⟨337387776342906481521457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449850368457208642028609 337387776342906481521457)
            ·
              refine ⟨253040832257179861141093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337387776342906481521457 253040832257179861141093)
              ·
                refine ⟨47445156048221223963955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253040832257179861141093 47445156048221223963955)
                ·
                  rfl

theorem cell20_311847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_311847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311847 prefixEnd_311847 := by exact prefixLift 311847
  have htrace : WordTrace (prefixWord ++ tailWord_311847) baseStart_311847 baseEnd_311847 := by
    simpa [prefixWord, tailWord_311847, baseEnd_311847] using wordTrace_append hprefix tailTrace_311847
  have hstable : (prefixWord ++ tailWord_311847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311847).length < 2 ^ (prefixWord ++ tailWord_311847).sum := by decide
  have hdescent : baseEnd_311847 < baseStart_311847 := by decide
  rcases family_descends (prefixWord ++ tailWord_311847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311879 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_311879 : Nat := 118140960795 + 311879 * 2 ^ 59
def prefixEnd_311879 : Nat := 4983230072969 + 3 ^ 40 * 311879 * 2
def baseEnd_311879 : Nat := 142350073816613782825067

theorem tailTrace_311879 : CollatzResearch.WordTrace tailWord_311879 prefixEnd_311879 142350073816613782825067 := by
  unfold tailWord_311879
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375161637123122537690691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7583441091415415025127127 11375161637123122537690691)
  ·
    refine ⟨17062742455684683806536037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11375161637123122537690691 17062742455684683806536037)
    ·
      refine ⟨3199264210440878213725507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17062742455684683806536037 3199264210440878213725507)
      ·
        refine ⟨4798896315661317320588261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199264210440878213725507 4798896315661317320588261)
        ·
          refine ⟨899793059186496997610299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4798896315661317320588261 899793059186496997610299)
          ·
            refine ⟨1349689588779745496415449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899793059186496997610299 1349689588779745496415449)
            ·
              refine ⟨1012267191584809122311587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349689588779745496415449 1012267191584809122311587)
              ·
                refine ⟨1518400787377213683467381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012267191584809122311587 1518400787377213683467381)
                ·
                  refine ⟨142350073816613782825067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1518400787377213683467381 142350073816613782825067)
                  ·
                    rfl

theorem cell20_311879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_311879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311879 prefixEnd_311879 := by exact prefixLift 311879
  have htrace : WordTrace (prefixWord ++ tailWord_311879) baseStart_311879 baseEnd_311879 := by
    simpa [prefixWord, tailWord_311879, baseEnd_311879] using wordTrace_append hprefix tailTrace_311879
  have hstable : (prefixWord ++ tailWord_311879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311879).length < 2 ^ (prefixWord ++ tailWord_311879).sum := by decide
  have hdescent : baseEnd_311879 < baseStart_311879 := by decide
  rcases family_descends (prefixWord ++ tailWord_311879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311893 : List Nat := [1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_311893 : Nat := 118140960795 + 311893 * 2 ^ 59
def prefixEnd_311893 : Nat := 4983230072969 + 3 ^ 40 * 311893 * 2
def baseEnd_311893 : Nat := 47452154599363985452781

theorem tailTrace_311893 : CollatzResearch.WordTrace tailWord_311893 prefixEnd_311893 47452154599363985452781 := by
  unfold tailWord_311893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375672259072402928700333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7583781506048268619133555 11375672259072402928700333)
  ·
    refine ⟨4265877097152151098262625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11375672259072402928700333 4265877097152151098262625)
    ·
      refine ⟨3199407822864113323696969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4265877097152151098262625 3199407822864113323696969)
      ·
        refine ⟨2399555867148084992772727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3199407822864113323696969 2399555867148084992772727)
        ·
          refine ⟨3599333800722127489159091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399555867148084992772727 3599333800722127489159091)
          ·
            refine ⟨5399000701083191233738637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599333800722127489159091 5399000701083191233738637)
            ·
              refine ⟨2024625262906196712651989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5399000701083191233738637 2024625262906196712651989)
              ·
                refine ⟨47452154599363985452781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2024625262906196712651989 47452154599363985452781)
                ·
                  rfl

theorem cell20_311893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_311893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311893 prefixEnd_311893 := by exact prefixLift 311893
  have htrace : WordTrace (prefixWord ++ tailWord_311893) baseStart_311893 baseEnd_311893 := by
    simpa [prefixWord, tailWord_311893, baseEnd_311893] using wordTrace_append hprefix tailTrace_311893
  have hstable : (prefixWord ++ tailWord_311893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311893).length < 2 ^ (prefixWord ++ tailWord_311893).sum := by decide
  have hdescent : baseEnd_311893 < baseStart_311893 := by decide
  rcases family_descends (prefixWord ++ tailWord_311893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311896 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_311896 : Nat := 118140960795 + 311896 * 2 ^ 59
def prefixEnd_311896 : Nat := 4983230072969 + 3 ^ 40 * 311896 * 2
def baseEnd_311896 : Nat := 142357833079837279258331

theorem tailTrace_311896 : CollatzResearch.WordTrace tailWord_311896 prefixEnd_311896 142357833079837279258331 := by
  unfold tailWord_311896
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687890839030767220529771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7583854452041022960706361 5687890839030767220529771)
  ·
    refine ⟨8531836258546150830794657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5687890839030767220529771 8531836258546150830794657)
    ·
      refine ⟨6398877193909613123095993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8531836258546150830794657 6398877193909613123095993)
      ·
        refine ⟨4799157895432209842321995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6398877193909613123095993 4799157895432209842321995)
        ·
          refine ⟨7198736843148314763482993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799157895432209842321995 7198736843148314763482993)
          ·
            refine ⟨5399052632361236072612245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198736843148314763482993 5399052632361236072612245)
            ·
              refine ⟨253080592141932940903699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5399052632361236072612245 253080592141932940903699)
              ·
                refine ⟨379620888212899411355549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253080592141932940903699 379620888212899411355549)
                ·
                  refine ⟨142357833079837279258331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379620888212899411355549 142357833079837279258331)
                  ·
                    rfl

theorem cell20_311896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_311896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311896 prefixEnd_311896 := by exact prefixLift 311896
  have htrace : WordTrace (prefixWord ++ tailWord_311896) baseStart_311896 baseEnd_311896 := by
    simpa [prefixWord, tailWord_311896, baseEnd_311896] using wordTrace_append hprefix tailTrace_311896
  have hstable : (prefixWord ++ tailWord_311896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311896).length < 2 ^ (prefixWord ++ tailWord_311896).sum := by decide
  have hdescent : baseEnd_311896 < baseStart_311896 := by decide
  rcases family_descends (prefixWord ++ tailWord_311896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311989 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_311989 : Nat := 118140960795 + 311989 * 2 ^ 59
def prefixEnd_311989 : Nat := 4983230072969 + 3 ^ 40 * 311989 * 2
def baseEnd_311989 : Nat := 142400280813942289157951

theorem tailTrace_311989 : CollatzResearch.WordTrace tailWord_311989 prefixEnd_311989 142400280813942289157951 := by
  unfold tailWord_311989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11379173666724611324195021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7586115777816407549463347 11379173666724611324195021)
  ·
    refine ⟨4267190125021729246573133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11379173666724611324195021 4267190125021729246573133)
    ·
      refine ⟨1600196296883148467464925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4267190125021729246573133 1600196296883148467464925)
      ·
        refine ⟨600073611331180675299347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1600196296883148467464925 600073611331180675299347)
        ·
          refine ⟨900110416996771012949021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600073611331180675299347 900110416996771012949021)
          ·
            refine ⟨337541406373789129855883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 900110416996771012949021 337541406373789129855883)
            ·
              refine ⟨506312109560683694783825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337541406373789129855883 506312109560683694783825)
              ·
                refine ⟨379734082170512771087869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506312109560683694783825 379734082170512771087869)
                ·
                  refine ⟨142400280813942289157951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379734082170512771087869 142400280813942289157951)
                  ·
                    rfl

theorem cell20_311989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_311989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_311989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_311989 prefixEnd_311989 := by exact prefixLift 311989
  have htrace : WordTrace (prefixWord ++ tailWord_311989) baseStart_311989 baseEnd_311989 := by
    simpa [prefixWord, tailWord_311989, baseEnd_311989] using wordTrace_append hprefix tailTrace_311989
  have hstable : (prefixWord ++ tailWord_311989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311989).length < 2 ^ (prefixWord ++ tailWord_311989).sum := by decide
  have hdescent : baseEnd_311989 < baseStart_311989 := by decide
  rcases family_descends (prefixWord ++ tailWord_311989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312000 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_312000 : Nat := 118140960795 + 312000 * 2 ^ 59
def prefixEnd_312000 : Nat := 4983230072969 + 3 ^ 40 * 312000 * 2
def baseEnd_312000 : Nat := 142405301513675139791239

theorem tailTrace_312000 : CollatzResearch.WordTrace tailWord_312000 prefixEnd_312000 142405301513675139791239 := by
  unfold tailWord_312000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5689787434842380101422727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7586383246456506801896969 5689787434842380101422727)
  ·
    refine ⟨8534681152263570152134091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5689787434842380101422727 8534681152263570152134091)
    ·
      refine ⟨12802021728395355228201137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8534681152263570152134091 12802021728395355228201137)
      ·
        refine ⟨9601516296296516421150853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12802021728395355228201137 9601516296296516421150853)
        ·
          refine ⟨1800284305555596828965785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9601516296296516421150853 1800284305555596828965785)
          ·
            refine ⟨1350213229166697621724339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800284305555596828965785 1350213229166697621724339)
            ·
              refine ⟨2025319843750046432586509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350213229166697621724339 2025319843750046432586509)
              ·
                refine ⟨759494941406267412219941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2025319843750046432586509 759494941406267412219941)
                ·
                  refine ⟨142405301513675139791239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759494941406267412219941 142405301513675139791239)
                  ·
                    rfl

theorem cell20_312000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_312000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312000 prefixEnd_312000 := by exact prefixLift 312000
  have htrace : WordTrace (prefixWord ++ tailWord_312000) baseStart_312000 baseEnd_312000 := by
    simpa [prefixWord, tailWord_312000, baseEnd_312000] using wordTrace_append hprefix tailTrace_312000
  have hstable : (prefixWord ++ tailWord_312000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312000).length < 2 ^ (prefixWord ++ tailWord_312000).sum := by decide
  have hdescent : baseEnd_312000 < baseStart_312000 := by decide
  rcases family_descends (prefixWord ++ tailWord_312000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312020 : List Nat := [2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_312020 : Nat := 118140960795 + 312020 * 2 ^ 59
def prefixEnd_312020 : Nat := 4983230072969 + 3 ^ 40 * 312020 * 2
def baseEnd_312020 : Nat := 47471476686214653041497

theorem tailTrace_312020 : CollatzResearch.WordTrace tailWord_312020 prefixEnd_312020 47471476686214653041497 := by
  unfold tailWord_312020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690152164806151809286757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7586869553074869079049009 5690152164806151809286757)
  ·
    refine ⟨1066903530901153464241267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5690152164806151809286757 1066903530901153464241267)
    ·
      refine ⟨1600355296351730196361901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066903530901153464241267 1600355296351730196361901)
      ·
        refine ⟨600133236131898823635713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1600355296351730196361901 600133236131898823635713)
        ·
          refine ⟨450099927098924117726785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600133236131898823635713 450099927098924117726785)
          ·
            refine ⟨337574945324193088295089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450099927098924117726785 337574945324193088295089)
            ·
              refine ⟨253181208993144816221317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337574945324193088295089 253181208993144816221317)
              ·
                refine ⟨47471476686214653041497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253181208993144816221317 47471476686214653041497)
                ·
                  rfl

theorem cell20_312020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_312020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312020 prefixEnd_312020 := by exact prefixLift 312020
  have htrace : WordTrace (prefixWord ++ tailWord_312020) baseStart_312020 baseEnd_312020 := by
    simpa [prefixWord, tailWord_312020, baseEnd_312020] using wordTrace_append hprefix tailTrace_312020
  have hstable : (prefixWord ++ tailWord_312020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312020).length < 2 ^ (prefixWord ++ tailWord_312020).sum := by decide
  have hdescent : baseEnd_312020 < baseStart_312020 := by decide
  rcases family_descends (prefixWord ++ tailWord_312020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312024 : List Nat := [2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_312024 : Nat := 118140960795 + 312024 * 2 ^ 59
def prefixEnd_312024 : Nat := 4983230072969 + 3 ^ 40 * 312024 * 2
def baseEnd_312024 : Nat := 47472085255879240997047

theorem tailTrace_312024 : CollatzResearch.WordTrace tailWord_312024 prefixEnd_312024 47472085255879240997047 := by
  unfold tailWord_312024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690225110798906150859563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7586966814398541534479417 5690225110798906150859563)
  ·
    refine ⟨8535337666198359226289345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690225110798906150859563 8535337666198359226289345)
    ·
      refine ⟨6401503249648769419717009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8535337666198359226289345 6401503249648769419717009)
      ·
        refine ⟨4801127437236577064787757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6401503249648769419717009 4801127437236577064787757)
        ·
          refine ⟨1800422788963716399295409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4801127437236577064787757 1800422788963716399295409)
          ·
            refine ⟨1350317091722787299471557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800422788963716399295409 1350317091722787299471557)
            ·
              refine ⟨253184454698022618650917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1350317091722787299471557 253184454698022618650917)
              ·
                refine ⟨47472085255879240997047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253184454698022618650917 47472085255879240997047)
                ·
                  rfl

theorem cell20_312024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_312024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312024 prefixEnd_312024 := by exact prefixLift 312024
  have htrace : WordTrace (prefixWord ++ tailWord_312024) baseStart_312024 baseEnd_312024 := by
    simpa [prefixWord, tailWord_312024, baseEnd_312024] using wordTrace_append hprefix tailTrace_312024
  have hstable : (prefixWord ++ tailWord_312024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312024).length < 2 ^ (prefixWord ++ tailWord_312024).sum := by decide
  have hdescent : baseEnd_312024 < baseStart_312024 := by decide
  rcases family_descends (prefixWord ++ tailWord_312024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312062 : List Nat := [4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_312062 : Nat := 118140960795 + 312062 * 2 ^ 59
def prefixEnd_312062 : Nat := 4983230072969 + 3 ^ 40 * 312062 * 2
def baseEnd_312062 : Nat := 47477866667692826574773

theorem tailTrace_312062 : CollatzResearch.WordTrace tailWord_312062 prefixEnd_312062 47477866667692826574773 := by
  unfold tailWord_312062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422729524432518098950305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7587890796973429861068293 1422729524432518098950305)
  ·
    refine ⟨1067047143324388574212729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1422729524432518098950305 1067047143324388574212729)
    ·
      refine ⟨800285357493291430659547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067047143324388574212729 800285357493291430659547)
      ·
        refine ⟨1200428036239937145989321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800285357493291430659547 1200428036239937145989321)
        ·
          refine ⟨900321027179952859491991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1200428036239937145989321 900321027179952859491991)
          ·
            refine ⟨1350481540769929289237987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900321027179952859491991 1350481540769929289237987)
            ·
              refine ⟨2025722311154893933856981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350481540769929289237987 2025722311154893933856981)
              ·
                refine ⟨47477866667692826574773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2025722311154893933856981 47477866667692826574773)
                ·
                  rfl

theorem cell20_312062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_312062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312062 prefixEnd_312062 := by exact prefixLift 312062
  have htrace : WordTrace (prefixWord ++ tailWord_312062) baseStart_312062 baseEnd_312062 := by
    simpa [prefixWord, tailWord_312062, baseEnd_312062] using wordTrace_append hprefix tailTrace_312062
  have hstable : (prefixWord ++ tailWord_312062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312062).length < 2 ^ (prefixWord ++ tailWord_312062).sum := by decide
  have hdescent : baseEnd_312062 < baseStart_312062 := by decide
  rcases family_descends (prefixWord ++ tailWord_312062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312100 : List Nat := [2, 3, 1, 3, 4, 7]
def baseStart_312100 : Nat := 118140960795 + 312100 * 2 ^ 59
def prefixEnd_312100 : Nat := 4983230072969 + 3 ^ 40 * 312100 * 2
def baseEnd_312100 : Nat := 5275960897722934683611

theorem tailTrace_312100 : CollatzResearch.WordTrace tailWord_312100 prefixEnd_312100 5275960897722934683611 := by
  unfold tailWord_312100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5691611084661238640742877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7588814779548318187657169 5691611084661238640742877)
  ·
    refine ⟨2134354156747964490278579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5691611084661238640742877 2134354156747964490278579)
    ·
      refine ⟨3201531235121946735417869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134354156747964490278579 3201531235121946735417869)
      ·
        refine ⟨1200574213170730025781701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3201531235121946735417869 1200574213170730025781701)
        ·
          refine ⟨225107664969511879834069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1200574213170730025781701 225107664969511879834069)
          ·
            refine ⟨5275960897722934683611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 225107664969511879834069 5275960897722934683611)
            ·
              rfl

theorem cell20_312100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 7].length) (baseStart_312100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312100 prefixEnd_312100 := by exact prefixLift 312100
  have htrace : WordTrace (prefixWord ++ tailWord_312100) baseStart_312100 baseEnd_312100 := by
    simpa [prefixWord, tailWord_312100, baseEnd_312100] using wordTrace_append hprefix tailTrace_312100
  have hstable : (prefixWord ++ tailWord_312100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312100).length < 2 ^ (prefixWord ++ tailWord_312100).sum := by decide
  have hdescent : baseEnd_312100 < baseStart_312100 := by decide
  rcases family_descends (prefixWord ++ tailWord_312100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312114 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_312114 : Nat := 118140960795 + 312114 * 2 ^ 59
def prefixEnd_312114 : Nat := 4983230072969 + 3 ^ 40 * 312114 * 2
def baseEnd_312114 : Nat := 142457334219997409990773

theorem tailTrace_312114 : CollatzResearch.WordTrace tailWord_312114 prefixEnd_312114 142457334219997409990773 := by
  unfold tailWord_312114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845933197817939418123849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7589155194181171781663597 2845933197817939418123849)
  ·
    refine ⟨2134449898363454563592887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2845933197817939418123849 2134449898363454563592887)
    ·
      refine ⟨3201674847545181845389331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134449898363454563592887 3201674847545181845389331)
      ·
        refine ⟨4802512271317772768083997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201674847545181845389331 4802512271317772768083997)
        ·
          refine ⟨1800942101744164788031499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4802512271317772768083997 1800942101744164788031499)
          ·
            refine ⟨2701413152616247182047249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800942101744164788031499 2701413152616247182047249)
            ·
              refine ⟨2026059864462185386535437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701413152616247182047249 2026059864462185386535437)
              ·
                refine ⟨759772449173319519950789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2026059864462185386535437 759772449173319519950789)
                ·
                  refine ⟨142457334219997409990773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759772449173319519950789 142457334219997409990773)
                  ·
                    rfl

theorem cell20_312114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_312114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312114 prefixEnd_312114 := by exact prefixLift 312114
  have htrace : WordTrace (prefixWord ++ tailWord_312114) baseStart_312114 baseEnd_312114 := by
    simpa [prefixWord, tailWord_312114, baseEnd_312114] using wordTrace_append hprefix tailTrace_312114
  have hstable : (prefixWord ++ tailWord_312114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312114).length < 2 ^ (prefixWord ++ tailWord_312114).sum := by decide
  have hdescent : baseEnd_312114 < baseStart_312114 := by decide
  rcases family_descends (prefixWord ++ tailWord_312114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312162 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_312162 : Nat := 118140960795 + 312162 * 2 ^ 59
def prefixEnd_312162 : Nat := 4983230072969 + 3 ^ 40 * 312162 * 2
def baseEnd_312162 : Nat := 142479242727922576390577

theorem tailTrace_312162 : CollatzResearch.WordTrace tailWord_312162 prefixEnd_312162 142479242727922576390577 := by
  unfold tailWord_312162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846370873774465467560685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7590322330065241246828493 2846370873774465467560685)
  ·
    refine ⟨1067389077665424550335257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2846370873774465467560685 1067389077665424550335257)
    ·
      refine ⟨800541808249068412751443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067389077665424550335257 800541808249068412751443)
      ·
        refine ⟨1200812712373602619127165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800541808249068412751443 1200812712373602619127165)
        ·
          refine ⟨450304767140100982172687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1200812712373602619127165 450304767140100982172687)
          ·
            refine ⟨675457150710151473259031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450304767140100982172687 675457150710151473259031)
            ·
              refine ⟨1013185726065227209888547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675457150710151473259031 1013185726065227209888547)
              ·
                refine ⟨1519778589097840814832821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013185726065227209888547 1519778589097840814832821)
                ·
                  refine ⟨142479242727922576390577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519778589097840814832821 142479242727922576390577)
                  ·
                    rfl

theorem cell20_312162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_312162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312162 prefixEnd_312162 := by exact prefixLift 312162
  have htrace : WordTrace (prefixWord ++ tailWord_312162) baseStart_312162 baseEnd_312162 := by
    simpa [prefixWord, tailWord_312162, baseEnd_312162] using wordTrace_append hprefix tailTrace_312162
  have hstable : (prefixWord ++ tailWord_312162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312162).length < 2 ^ (prefixWord ++ tailWord_312162).sum := by decide
  have hdescent : baseEnd_312162 < baseStart_312162 := by decide
  rcases family_descends (prefixWord ++ tailWord_312162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312197 : List Nat := [1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_312197 : Nat := 118140960795 + 312197 * 2 ^ 59
def prefixEnd_312197 : Nat := 4983230072969 + 3 ^ 40 * 312197 * 2
def baseEnd_312197 : Nat := 47498405893872670074589

theorem tailTrace_312197 : CollatzResearch.WordTrace tailWord_312197 prefixEnd_312197 47498405893872670074589 := by
  unfold tailWord_312197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11386760049971062847766845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7591173366647375231844563 11386760049971062847766845)
  ·
    refine ⟨4270035018739148567912567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11386760049971062847766845 4270035018739148567912567)
    ·
      refine ⟨6405052528108722851868851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270035018739148567912567 6405052528108722851868851)
      ·
        refine ⟨9607578792163084277803277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6405052528108722851868851 9607578792163084277803277)
        ·
          refine ⟨3602842047061156604176229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9607578792163084277803277 3602842047061156604176229)
          ·
            refine ⟨675532883823966863283043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3602842047061156604176229 675532883823966863283043)
            ·
              refine ⟨1013299325735950294924565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675532883823966863283043 1013299325735950294924565)
              ·
                refine ⟨47498405893872670074589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1013299325735950294924565 47498405893872670074589)
                ·
                  rfl

theorem cell20_312197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_312197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312197 prefixEnd_312197 := by exact prefixLift 312197
  have htrace : WordTrace (prefixWord ++ tailWord_312197) baseStart_312197 baseEnd_312197 := by
    simpa [prefixWord, tailWord_312197, baseEnd_312197] using wordTrace_append hprefix tailTrace_312197
  have hstable : (prefixWord ++ tailWord_312197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312197).length < 2 ^ (prefixWord ++ tailWord_312197).sum := by decide
  have hdescent : baseEnd_312197 < baseStart_312197 := by decide
  rcases family_descends (prefixWord ++ tailWord_312197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312204 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_312204 : Nat := 118140960795 + 312204 * 2 ^ 59
def prefixEnd_312204 : Nat := 4983230072969 + 3 ^ 40 * 312204 * 2
def baseEnd_312204 : Nat := 142498412672357096990405

theorem tailTrace_312204 : CollatzResearch.WordTrace tailWord_312204 prefixEnd_312204 142498412672357096990405 := by
  unfold tailWord_312204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693507680472851521635833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7591343573963802028847777 5693507680472851521635833)
  ·
    refine ⟨4270130760354638641226875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5693507680472851521635833 4270130760354638641226875)
    ·
      refine ⟨6405196140531957961840313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270130760354638641226875 6405196140531957961840313)
      ·
        refine ⟨4803897105398968471380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6405196140531957961840313 4803897105398968471380235)
        ·
          refine ⟨7205845658098452707070353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803897105398968471380235 7205845658098452707070353)
          ·
            refine ⟨5404384243573839530302765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7205845658098452707070353 5404384243573839530302765)
            ·
              refine ⟨2026644091340189823863537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5404384243573839530302765 2026644091340189823863537)
              ·
                refine ⟨1519983068505142367897653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026644091340189823863537 1519983068505142367897653)
                ·
                  refine ⟨142498412672357096990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519983068505142367897653 142498412672357096990405)
                  ·
                    rfl

theorem cell20_312204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_312204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312204 prefixEnd_312204 := by exact prefixLift 312204
  have htrace : WordTrace (prefixWord ++ tailWord_312204) baseStart_312204 baseEnd_312204 := by
    simpa [prefixWord, tailWord_312204, baseEnd_312204] using wordTrace_append hprefix tailTrace_312204
  have hstable : (prefixWord ++ tailWord_312204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312204).length < 2 ^ (prefixWord ++ tailWord_312204).sum := by decide
  have hdescent : baseEnd_312204 < baseStart_312204 := by decide
  rcases family_descends (prefixWord ++ tailWord_312204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312221 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_312221 : Nat := 118140960795 + 312221 * 2 ^ 59
def prefixEnd_312221 : Nat := 4983230072969 + 3 ^ 40 * 312221 * 2
def baseEnd_312221 : Nat := 142506171935580593423669

theorem tailTrace_312221 : CollatzResearch.WordTrace tailWord_312221 prefixEnd_312221 142506171935580593423669 := by
  unfold tailWord_312221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11387635401884114946640517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7591756934589409964427011 11387635401884114946640517)
  ·
    refine ⟨2135181637853271552495097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11387635401884114946640517 2135181637853271552495097)
    ·
      refine ⟨1601386228389953664371323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2135181637853271552495097 1601386228389953664371323)
      ·
        refine ⟨2402079342584930496556985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601386228389953664371323 2402079342584930496556985)
        ·
          refine ⟨1801559506938697872417739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402079342584930496556985 1801559506938697872417739)
          ·
            refine ⟨2702339260408046808626609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801559506938697872417739 2702339260408046808626609)
            ·
              refine ⟨2026754445306035106469957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702339260408046808626609 2026754445306035106469957)
              ·
                refine ⟨380016458494881582463117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2026754445306035106469957 380016458494881582463117)
                ·
                  refine ⟨142506171935580593423669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380016458494881582463117 142506171935580593423669)
                  ·
                    rfl

theorem cell20_312221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_312221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312221 prefixEnd_312221 := by exact prefixLift 312221
  have htrace : WordTrace (prefixWord ++ tailWord_312221) baseStart_312221 baseEnd_312221 := by
    simpa [prefixWord, tailWord_312221, baseEnd_312221] using wordTrace_append hprefix tailTrace_312221
  have hstable : (prefixWord ++ tailWord_312221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312221).length < 2 ^ (prefixWord ++ tailWord_312221).sum := by decide
  have hdescent : baseEnd_312221 < baseStart_312221 := by decide
  rcases family_descends (prefixWord ++ tailWord_312221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312269 : List Nat := [1, 6, 3, 1, 9]
def baseStart_312269 : Nat := 118140960795 + 312269 * 2 ^ 59
def prefixEnd_312269 : Nat := 4983230072969 + 3 ^ 40 * 312269 * 2
def baseEnd_312269 : Nat := 1759605931401305676833

theorem tailTrace_312269 : CollatzResearch.WordTrace tailWord_312269 prefixEnd_312269 1759605931401305676833 := by
  unfold tailWord_312269
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389386105710219144387861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7592924070473479429591907 11389386105710219144387861)
  ·
    refine ⟨533877473705166522393181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11389386105710219144387861 533877473705166522393181)
    ·
      refine ⟨200204052639437445897443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 533877473705166522393181 200204052639437445897443)
      ·
        refine ⟨300306078959156168846165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200204052639437445897443 300306078959156168846165)
        ·
          refine ⟨1759605931401305676833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 300306078959156168846165 1759605931401305676833)
          ·
            rfl

theorem cell20_312269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 9].length) (baseStart_312269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312269 prefixEnd_312269 := by exact prefixLift 312269
  have htrace : WordTrace (prefixWord ++ tailWord_312269) baseStart_312269 baseEnd_312269 := by
    simpa [prefixWord, tailWord_312269, baseEnd_312269] using wordTrace_append hprefix tailTrace_312269
  have hstable : (prefixWord ++ tailWord_312269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312269).length < 2 ^ (prefixWord ++ tailWord_312269).sum := by decide
  have hdescent : baseEnd_312269 < baseStart_312269 := by decide
  rcases family_descends (prefixWord ++ tailWord_312269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312276 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_312276 : Nat := 118140960795 + 312276 * 2 ^ 59
def prefixEnd_312276 : Nat := 4983230072969 + 3 ^ 40 * 312276 * 2
def baseEnd_312276 : Nat := 142531275434244846590111

theorem tailTrace_312276 : CollatzResearch.WordTrace tailWord_312276 prefixEnd_312276 142531275434244846590111 := by
  unfold tailWord_312276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694820708342429669946341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7593094277789906226595121 5694820708342429669946341)
  ·
    refine ⟨1067778882814205563114939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5694820708342429669946341 1067778882814205563114939)
    ·
      refine ⟨1601668324221308344672409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067778882814205563114939 1601668324221308344672409)
      ·
        refine ⟨1201251243165981258504307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1601668324221308344672409 1201251243165981258504307)
        ·
          refine ⟨1801876864748971887756461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201251243165981258504307 1801876864748971887756461)
          ·
            refine ⟨675703824280864457908673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1801876864748971887756461 675703824280864457908673)
            ·
              refine ⟨506777868210648343431505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675703824280864457908673 506777868210648343431505)
              ·
                refine ⟨380083401157986257573629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506777868210648343431505 380083401157986257573629)
                ·
                  refine ⟨142531275434244846590111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380083401157986257573629 142531275434244846590111)
                  ·
                    rfl

theorem cell20_312276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_312276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312276 prefixEnd_312276 := by exact prefixLift 312276
  have htrace : WordTrace (prefixWord ++ tailWord_312276) baseStart_312276 baseEnd_312276 := by
    simpa [prefixWord, tailWord_312276, baseEnd_312276] using wordTrace_append hprefix tailTrace_312276
  have hstable : (prefixWord ++ tailWord_312276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312276).length < 2 ^ (prefixWord ++ tailWord_312276).sum := by decide
  have hdescent : baseEnd_312276 < baseStart_312276 := by decide
  rcases family_descends (prefixWord ++ tailWord_312276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312321 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 2]
def baseStart_312321 : Nat := 118140960795 + 312321 * 2 ^ 59
def prefixEnd_312321 : Nat := 4983230072969 + 3 ^ 40 * 312321 * 2
def baseEnd_312321 : Nat := 142551814660424690089927

theorem tailTrace_312321 : CollatzResearch.WordTrace tailWord_312321 prefixEnd_312321 142551814660424690089927 := by
  unfold tailWord_312321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11391282701521832025280817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7594188467681221350187211 11391282701521832025280817)
  ·
    refine ⟨8543462026141374018960613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11391282701521832025280817 8543462026141374018960613)
    ·
      refine ⟨1601899129901507628555115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8543462026141374018960613 1601899129901507628555115)
      ·
        refine ⟨2402848694852261442832673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601899129901507628555115 2402848694852261442832673)
        ·
          refine ⟨1802136521139196082124505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402848694852261442832673 1802136521139196082124505)
          ·
            refine ⟨1351602390854397061593379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802136521139196082124505 1351602390854397061593379)
            ·
              refine ⟨2027403586281595592390069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351602390854397061593379 2027403586281595592390069)
              ·
                refine ⟨190069086213899586786569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2027403586281595592390069 190069086213899586786569)
                ·
                  refine ⟨142551814660424690089927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190069086213899586786569 142551814660424690089927)
                  ·
                    rfl

theorem cell20_312321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_312321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312321 prefixEnd_312321 := by exact prefixLift 312321
  have htrace : WordTrace (prefixWord ++ tailWord_312321) baseStart_312321 baseEnd_312321 := by
    simpa [prefixWord, tailWord_312321, baseEnd_312321] using wordTrace_append hprefix tailTrace_312321
  have hstable : (prefixWord ++ tailWord_312321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312321).length < 2 ^ (prefixWord ++ tailWord_312321).sum := by decide
  have hdescent : baseEnd_312321 < baseStart_312321 := by decide
  rcases family_descends (prefixWord ++ tailWord_312321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312325 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_312325 : Nat := 118140960795 + 312325 * 2 ^ 59
def prefixEnd_312325 : Nat := 4983230072969 + 3 ^ 40 * 312325 * 2
def baseEnd_312325 : Nat := 142553640369418453956577

theorem tailTrace_312325 : CollatzResearch.WordTrace tailWord_312325 prefixEnd_312325 142553640369418453956577 := by
  unfold tailWord_312325
  simp only [CollatzResearch.WordTrace]
  refine ⟨11391428593507340708426429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7594285729004893805617619 11391428593507340708426429)
  ·
    refine ⟨4271785722565252765659911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11391428593507340708426429 4271785722565252765659911)
    ·
      refine ⟨6407678583847879148489867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271785722565252765659911 6407678583847879148489867)
      ·
        refine ⟨9611517875771818722734801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6407678583847879148489867 9611517875771818722734801)
        ·
          refine ⟨7208638406828864042051101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9611517875771818722734801 7208638406828864042051101)
          ·
            refine ⟨2703239402560824015769163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7208638406828864042051101 2703239402560824015769163)
            ·
              refine ⟨4054859103841236023653745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703239402560824015769163 4054859103841236023653745)
              ·
                refine ⟨3041144327880927017740309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054859103841236023653745 3041144327880927017740309)
                ·
                  refine ⟨142553640369418453956577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3041144327880927017740309 142553640369418453956577)
                  ·
                    rfl

theorem cell20_312325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_312325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312325 prefixEnd_312325 := by exact prefixLift 312325
  have htrace : WordTrace (prefixWord ++ tailWord_312325) baseStart_312325 baseEnd_312325 := by
    simpa [prefixWord, tailWord_312325, baseEnd_312325] using wordTrace_append hprefix tailTrace_312325
  have hstable : (prefixWord ++ tailWord_312325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312325).length < 2 ^ (prefixWord ++ tailWord_312325).sum := by decide
  have hdescent : baseEnd_312325 < baseStart_312325 := by decide
  rcases family_descends (prefixWord ++ tailWord_312325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312359 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_312359 : Nat := 118140960795 + 312359 * 2 ^ 59
def prefixEnd_312359 : Nat := 4983230072969 + 3 ^ 40 * 312359 * 2
def baseEnd_312359 : Nat := 142569158895865446823105

theorem tailTrace_312359 : CollatzResearch.WordTrace tailWord_312359 prefixEnd_312359 142569158895865446823105 := by
  unfold tailWord_312359
  simp only [CollatzResearch.WordTrace]
  refine ⟨11392668675384164515164131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7595112450256109676776087 11392668675384164515164131)
  ·
    refine ⟨17089003013076246772746197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11392668675384164515164131 17089003013076246772746197)
    ·
      refine ⟨400523508118974533736239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17089003013076246772746197 400523508118974533736239)
      ·
        refine ⟨600785262178461800604359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400523508118974533736239 600785262178461800604359)
        ·
          refine ⟨901177893267692700906539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600785262178461800604359 901177893267692700906539)
          ·
            refine ⟨1351766839901539051359809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901177893267692700906539 1351766839901539051359809)
            ·
              refine ⟨1013825129926154288519857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351766839901539051359809 1013825129926154288519857)
              ·
                refine ⟨760368847444615716389893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013825129926154288519857 760368847444615716389893)
                ·
                  refine ⟨142569158895865446823105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760368847444615716389893 142569158895865446823105)
                  ·
                    rfl

theorem cell20_312359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_312359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312359 prefixEnd_312359 := by exact prefixLift 312359
  have htrace : WordTrace (prefixWord ++ tailWord_312359) baseStart_312359 baseEnd_312359 := by
    simpa [prefixWord, tailWord_312359, baseEnd_312359] using wordTrace_append hprefix tailTrace_312359
  have hstable : (prefixWord ++ tailWord_312359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312359).length < 2 ^ (prefixWord ++ tailWord_312359).sum := by decide
  have hdescent : baseEnd_312359 < baseStart_312359 := by decide
  rcases family_descends (prefixWord ++ tailWord_312359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312362 : List Nat := [3, 1, 4, 1, 4, 1, 2, 4]
def baseStart_312362 : Nat := 118140960795 + 312362 * 2 ^ 59
def prefixEnd_312362 : Nat := 4983230072969 + 3 ^ 40 * 312362 * 2
def baseEnd_312362 : Nat := 47523509392536923241031

theorem tailTrace_312362 : CollatzResearch.WordTrace tailWord_312362 prefixEnd_312362 47523509392536923241031 := by
  unfold tailWord_312362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848194523593324006880835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7595185396248864018348893 2848194523593324006880835)
  ·
    refine ⟨4272291785389986010321253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848194523593324006880835 4272291785389986010321253)
    ·
      refine ⟨801054709760622376935235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4272291785389986010321253 801054709760622376935235)
      ·
        refine ⟨1201582064640933565402853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801054709760622376935235 1201582064640933565402853)
        ·
          refine ⟨225296637120175043513035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1201582064640933565402853 225296637120175043513035)
          ·
            refine ⟨337944955680262565269553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225296637120175043513035 337944955680262565269553)
            ·
              refine ⟨253458716760196923952165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337944955680262565269553 253458716760196923952165)
              ·
                refine ⟨47523509392536923241031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253458716760196923952165 47523509392536923241031)
                ·
                  rfl

theorem cell20_312362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_312362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312362 prefixEnd_312362 := by exact prefixLift 312362
  have htrace : WordTrace (prefixWord ++ tailWord_312362) baseStart_312362 baseEnd_312362 := by
    simpa [prefixWord, tailWord_312362, baseEnd_312362] using wordTrace_append hprefix tailTrace_312362
  have hstable : (prefixWord ++ tailWord_312362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312362).length < 2 ^ (prefixWord ++ tailWord_312362).sum := by decide
  have hdescent : baseEnd_312362 < baseStart_312362 := by decide
  rcases family_descends (prefixWord ++ tailWord_312362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312363 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_312363 : Nat := 118140960795 + 312363 * 2 ^ 59
def prefixEnd_312363 : Nat := 4983230072969 + 3 ^ 40 * 312363 * 2
def baseEnd_312363 : Nat := 142570984604859210689755

theorem tailTrace_312363 : CollatzResearch.WordTrace tailWord_312363 prefixEnd_312363 142570984604859210689755 := by
  unfold tailWord_312363
  simp only [CollatzResearch.WordTrace]
  refine ⟨11392814567369673198309743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7595209711579782132206495 11392814567369673198309743)
  ·
    refine ⟨17089221851054509797464615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11392814567369673198309743 17089221851054509797464615)
    ·
      refine ⟨25633832776581764696196923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17089221851054509797464615 25633832776581764696196923)
      ·
        refine ⟨38450749164872647044295385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25633832776581764696196923 38450749164872647044295385)
        ·
          refine ⟨28838061873654485283221539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38450749164872647044295385 28838061873654485283221539)
          ·
            refine ⟨43257092810481727924832309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28838061873654485283221539 43257092810481727924832309)
            ·
              refine ⟨4055352450982661992953029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43257092810481727924832309 4055352450982661992953029)
              ·
                refine ⟨760378584559249123678693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4055352450982661992953029 760378584559249123678693)
                ·
                  refine ⟨142570984604859210689755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760378584559249123678693 142570984604859210689755)
                  ·
                    rfl

theorem cell20_312363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_312363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312363 prefixEnd_312363 := by exact prefixLift 312363
  have htrace : WordTrace (prefixWord ++ tailWord_312363) baseStart_312363 baseEnd_312363 := by
    simpa [prefixWord, tailWord_312363, baseEnd_312363] using wordTrace_append hprefix tailTrace_312363
  have hstable : (prefixWord ++ tailWord_312363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312363).length < 2 ^ (prefixWord ++ tailWord_312363).sum := by decide
  have hdescent : baseEnd_312363 < baseStart_312363 := by decide
  rcases family_descends (prefixWord ++ tailWord_312363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312376 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_312376 : Nat := 118140960795 + 312376 * 2 ^ 59
def prefixEnd_312376 : Nat := 4983230072969 + 3 ^ 40 * 312376 * 2
def baseEnd_312376 : Nat := 142576918159088943256369

theorem tailTrace_312376 : CollatzResearch.WordTrace tailWord_312376 prefixEnd_312376 142576918159088943256369 := by
  unfold tailWord_312376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696644358161288209266491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7595525810881717612355321 5696644358161288209266491)
  ·
    refine ⟨8544966537241932313899737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5696644358161288209266491 8544966537241932313899737)
    ·
      refine ⟨6408724902931449235424803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8544966537241932313899737 6408724902931449235424803)
      ·
        refine ⟨9613087354397173853137205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408724902931449235424803 9613087354397173853137205)
        ·
          refine ⟨901226939474735048731613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9613087354397173853137205 901226939474735048731613)
          ·
            refine ⟨337960102303025643274355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 901226939474735048731613 337960102303025643274355)
            ·
              refine ⟨506940153454538464911533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337960102303025643274355 506940153454538464911533)
              ·
                refine ⟨190102557545451924341825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506940153454538464911533 190102557545451924341825)
                ·
                  refine ⟨142576918159088943256369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190102557545451924341825 142576918159088943256369)
                  ·
                    rfl

theorem cell20_312376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_312376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312376 prefixEnd_312376 := by exact prefixLift 312376
  have htrace : WordTrace (prefixWord ++ tailWord_312376) baseStart_312376 baseEnd_312376 := by
    simpa [prefixWord, tailWord_312376, baseEnd_312376] using wordTrace_append hprefix tailTrace_312376
  have hstable : (prefixWord ++ tailWord_312376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312376).length < 2 ^ (prefixWord ++ tailWord_312376).sum := by decide
  have hdescent : baseEnd_312376 < baseStart_312376 := by decide
  rcases family_descends (prefixWord ++ tailWord_312376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312390 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_312390 : Nat := 118140960795 + 312390 * 2 ^ 59
def prefixEnd_312390 : Nat := 4983230072969 + 3 ^ 40 * 312390 * 2
def baseEnd_312390 : Nat := 142583308140567116789645

theorem tailTrace_312390 : CollatzResearch.WordTrace tailWord_312390 prefixEnd_312390 142583308140567116789645 := by
  unfold tailWord_312390
  simp only [CollatzResearch.WordTrace]
  refine ⟨356056229320995525298207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7595866225514571206361749 356056229320995525298207)
  ·
    refine ⟨534084343981493287947311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356056229320995525298207 534084343981493287947311)
    ·
      refine ⟨801126515972239931920967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534084343981493287947311 801126515972239931920967)
      ·
        refine ⟨1201689773958359897881451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801126515972239931920967 1201689773958359897881451)
        ·
          refine ⟨1802534660937539846822177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201689773958359897881451 1802534660937539846822177)
          ·
            refine ⟨1351900995703154885116633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802534660937539846822177 1351900995703154885116633)
            ·
              refine ⟨1013925746777366163837475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351900995703154885116633 1013925746777366163837475)
              ·
                refine ⟨1520888620166049245756213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013925746777366163837475 1520888620166049245756213)
                ·
                  refine ⟨142583308140567116789645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1520888620166049245756213 142583308140567116789645)
                  ·
                    rfl

theorem cell20_312390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_312390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312390 prefixEnd_312390 := by exact prefixLift 312390
  have htrace : WordTrace (prefixWord ++ tailWord_312390) baseStart_312390 baseEnd_312390 := by
    simpa [prefixWord, tailWord_312390, baseEnd_312390] using wordTrace_append hprefix tailTrace_312390
  have hstable : (prefixWord ++ tailWord_312390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312390).length < 2 ^ (prefixWord ++ tailWord_312390).sum := by decide
  have hdescent : baseEnd_312390 < baseStart_312390 := by decide
  rcases family_descends (prefixWord ++ tailWord_312390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312394 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_312394 : Nat := 118140960795 + 312394 * 2 ^ 59
def prefixEnd_312394 : Nat := 4983230072969 + 3 ^ 40 * 312394 * 2
def baseEnd_312394 : Nat := 142585133849560880656295

theorem tailTrace_312394 : CollatzResearch.WordTrace tailWord_312394 prefixEnd_312394 142585133849560880656295 := by
  unfold tailWord_312394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848486307564341373172059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7595963486838243661792157 2848486307564341373172059)
  ·
    refine ⟨4272729461346512059758089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848486307564341373172059 4272729461346512059758089)
    ·
      refine ⟨3204547096009884044818567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4272729461346512059758089 3204547096009884044818567)
      ·
        refine ⟨4806820644014826067227851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204547096009884044818567 4806820644014826067227851)
        ·
          refine ⟨7210230966022239100841777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806820644014826067227851 7210230966022239100841777)
          ·
            refine ⟨5407673224516679325631333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7210230966022239100841777 5407673224516679325631333)
            ·
              refine ⟨1013938729596877373555875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5407673224516679325631333 1013938729596877373555875)
              ·
                refine ⟨1520908094395316060333813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013938729596877373555875 1520908094395316060333813)
                ·
                  refine ⟨142585133849560880656295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1520908094395316060333813 142585133849560880656295)
                  ·
                    rfl

theorem cell20_312394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_312394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312394 prefixEnd_312394 := by exact prefixLift 312394
  have htrace : WordTrace (prefixWord ++ tailWord_312394) baseStart_312394 baseEnd_312394 := by
    simpa [prefixWord, tailWord_312394, baseEnd_312394] using wordTrace_append hprefix tailTrace_312394
  have hstable : (prefixWord ++ tailWord_312394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312394).length < 2 ^ (prefixWord ++ tailWord_312394).sum := by decide
  have hdescent : baseEnd_312394 < baseStart_312394 := by decide
  rcases family_descends (prefixWord ++ tailWord_312394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312397 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_312397 : Nat := 118140960795 + 312397 * 2 ^ 59
def prefixEnd_312397 : Nat := 4983230072969 + 3 ^ 40 * 312397 * 2
def baseEnd_312397 : Nat := 142586503131306203556283

theorem tailTrace_312397 : CollatzResearch.WordTrace tailWord_312397 prefixEnd_312397 142586503131306203556283 := by
  unfold tailWord_312397
  simp only [CollatzResearch.WordTrace]
  refine ⟨11394054649246497005047445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7596036432830998003364963 11394054649246497005047445)
  ·
    refine ⟨534096311683429547111599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11394054649246497005047445 534096311683429547111599)
    ·
      refine ⟨801144467525144320667399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534096311683429547111599 801144467525144320667399)
      ·
        refine ⟨1201716701287716481001099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801144467525144320667399 1201716701287716481001099)
        ·
          refine ⟨1802575051931574721501649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201716701287716481001099 1802575051931574721501649)
          ·
            refine ⟨1351931288948681041126237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802575051931574721501649 1351931288948681041126237)
            ·
              refine ⟨506974233355755390422339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351931288948681041126237 506974233355755390422339)
              ·
                refine ⟨760461350033633085633509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506974233355755390422339 760461350033633085633509)
                ·
                  refine ⟨142586503131306203556283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760461350033633085633509 142586503131306203556283)
                  ·
                    rfl

theorem cell20_312397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_312397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312397 prefixEnd_312397 := by exact prefixLift 312397
  have htrace : WordTrace (prefixWord ++ tailWord_312397) baseStart_312397 baseEnd_312397 := by
    simpa [prefixWord, tailWord_312397, baseEnd_312397] using wordTrace_append hprefix tailTrace_312397
  have hstable : (prefixWord ++ tailWord_312397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312397).length < 2 ^ (prefixWord ++ tailWord_312397).sum := by decide
  have hdescent : baseEnd_312397 < baseStart_312397 := by decide
  rcases family_descends (prefixWord ++ tailWord_312397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312449 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_312449 : Nat := 118140960795 + 312449 * 2 ^ 59
def prefixEnd_312449 : Nat := 4983230072969 + 3 ^ 40 * 312449 * 2
def baseEnd_312449 : Nat := 142610237348225133822737

theorem tailTrace_312449 : CollatzResearch.WordTrace tailWord_312449 prefixEnd_312449 142610237348225133822737 := by
  unfold tailWord_312449
  simp only [CollatzResearch.WordTrace]
  refine ⟨11395951245058109885940401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7597300830038739923960267 11395951245058109885940401)
  ·
    refine ⟨8546963433793582414455301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11395951245058109885940401 8546963433793582414455301)
    ·
      refine ⟨1602555643836296702710369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8546963433793582414455301 1602555643836296702710369)
      ·
        refine ⟨1201916732877222527032777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1602555643836296702710369 1201916732877222527032777)
        ·
          refine ⟨901437549657916895274583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201916732877222527032777 901437549657916895274583)
          ·
            refine ⟨1352156324486875342911875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901437549657916895274583 1352156324486875342911875)
            ·
              refine ⟨2028234486730313014367813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352156324486875342911875 2028234486730313014367813)
              ·
                refine ⟨380293966261933690193965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2028234486730313014367813 380293966261933690193965)
                ·
                  refine ⟨142610237348225133822737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380293966261933690193965 142610237348225133822737)
                  ·
                    rfl

theorem cell20_312449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_312449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312449 prefixEnd_312449 := by exact prefixLift 312449
  have htrace : WordTrace (prefixWord ++ tailWord_312449) baseStart_312449 baseEnd_312449 := by
    simpa [prefixWord, tailWord_312449, baseEnd_312449] using wordTrace_append hprefix tailTrace_312449
  have hstable : (prefixWord ++ tailWord_312449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312449).length < 2 ^ (prefixWord ++ tailWord_312449).sum := by decide
  have hdescent : baseEnd_312449 < baseStart_312449 := by decide
  rcases family_descends (prefixWord ++ tailWord_312449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312452 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_312452 : Nat := 118140960795 + 312452 * 2 ^ 59
def prefixEnd_312452 : Nat := 4983230072969 + 3 ^ 40 * 312452 * 2
def baseEnd_312452 : Nat := 142611606629970456722725

theorem tailTrace_312452 : CollatzResearch.WordTrace tailWord_312452 prefixEnd_312452 142611606629970456722725 := by
  unfold tailWord_312452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698030332023620699149805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7597373776031494265533073 5698030332023620699149805)
  ·
    refine ⟨2136761374508857762181177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5698030332023620699149805 2136761374508857762181177)
    ·
      refine ⟨1602571030881643321635883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2136761374508857762181177 1602571030881643321635883)
      ·
        refine ⟨2403856546322464982453825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602571030881643321635883 2403856546322464982453825)
        ·
          refine ⟨1802892409741848736840369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403856546322464982453825 1802892409741848736840369)
          ·
            refine ⟨1352169307306386552630277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802892409741848736840369 1352169307306386552630277)
            ·
              refine ⟨253531745119947478618177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1352169307306386552630277 253531745119947478618177)
              ·
                refine ⟨190148808839960608963633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253531745119947478618177 190148808839960608963633)
                ·
                  refine ⟨142611606629970456722725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190148808839960608963633 142611606629970456722725)
                  ·
                    rfl

theorem cell20_312452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_312452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312452 prefixEnd_312452 := by exact prefixLift 312452
  have htrace : WordTrace (prefixWord ++ tailWord_312452) baseStart_312452 baseEnd_312452 := by
    simpa [prefixWord, tailWord_312452, baseEnd_312452] using wordTrace_append hprefix tailTrace_312452
  have hstable : (prefixWord ++ tailWord_312452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312452).length < 2 ^ (prefixWord ++ tailWord_312452).sum := by decide
  have hdescent : baseEnd_312452 < baseStart_312452 := by decide
  rcases family_descends (prefixWord ++ tailWord_312452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312490 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_312490 : Nat := 118140960795 + 312490 * 2 ^ 59
def prefixEnd_312490 : Nat := 4983230072969 + 3 ^ 40 * 312490 * 2
def baseEnd_312490 : Nat := 142628950865411213455903

theorem tailTrace_312490 : CollatzResearch.WordTrace tailWord_312490 prefixEnd_312490 142628950865411213455903 := by
  unfold tailWord_312490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849361659477393472045731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7598297758606382592121949 2849361659477393472045731)
  ·
    refine ⟨4274042489216090208068597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849361659477393472045731 4274042489216090208068597)
    ·
      refine ⟨400691483364008457006431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4274042489216090208068597 400691483364008457006431)
      ·
        refine ⟨601037225046012685509647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400691483364008457006431 601037225046012685509647)
        ·
          refine ⟨901555837569019028264471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601037225046012685509647 901555837569019028264471)
          ·
            refine ⟨1352333756353528542396707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901555837569019028264471 1352333756353528542396707)
            ·
              refine ⟨2028500634530292813595061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352333756353528542396707 2028500634530292813595061)
              ·
                refine ⟨190171934487214951274537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2028500634530292813595061 190171934487214951274537)
                ·
                  refine ⟨142628950865411213455903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190171934487214951274537 142628950865411213455903)
                  ·
                    rfl

theorem cell20_312490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_312490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312490 prefixEnd_312490 := by exact prefixLift 312490
  have htrace : WordTrace (prefixWord ++ tailWord_312490) baseStart_312490 baseEnd_312490 := by
    simpa [prefixWord, tailWord_312490, baseEnd_312490] using wordTrace_append hprefix tailTrace_312490
  have hstable : (prefixWord ++ tailWord_312490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312490).length < 2 ^ (prefixWord ++ tailWord_312490).sum := by decide
  have hdescent : baseEnd_312490 < baseStart_312490 := by decide
  rcases family_descends (prefixWord ++ tailWord_312490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312577 : List Nat := [1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_312577 : Nat := 118140960795 + 312577 * 2 ^ 59
def prefixEnd_312577 : Nat := 4983230072969 + 3 ^ 40 * 312577 * 2
def baseEnd_312577 : Nat := 47556220012008525851849

theorem tailTrace_312577 : CollatzResearch.WordTrace tailWord_312577 prefixEnd_312577 47556220012008525851849 := by
  unfold tailWord_312577
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400619788594387746599985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7600413192396258497733323 11400619788594387746599985)
  ·
    refine ⟨8550464841445790809949989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11400619788594387746599985 8550464841445790809949989)
    ·
      refine ⟨1603212157771085776865623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8550464841445790809949989 1603212157771085776865623)
      ·
        refine ⟨2404818236656628665298435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603212157771085776865623 2404818236656628665298435)
        ·
          refine ⟨3607227354984942997947653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404818236656628665298435 3607227354984942997947653)
          ·
            refine ⟨676355129059676812115185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3607227354984942997947653 676355129059676812115185)
            ·
              refine ⟨507266346794757609086389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676355129059676812115185 507266346794757609086389)
              ·
                refine ⟨47556220012008525851849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 507266346794757609086389 47556220012008525851849)
                ·
                  rfl

theorem cell20_312577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_312577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312577 prefixEnd_312577 := by exact prefixLift 312577
  have htrace : WordTrace (prefixWord ++ tailWord_312577) baseStart_312577 baseEnd_312577 := by
    simpa [prefixWord, tailWord_312577, baseEnd_312577] using wordTrace_append hprefix tailTrace_312577
  have hstable : (prefixWord ++ tailWord_312577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312577).length < 2 ^ (prefixWord ++ tailWord_312577).sum := by decide
  have hdescent : baseEnd_312577 < baseStart_312577 := by decide
  rcases family_descends (prefixWord ++ tailWord_312577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312580 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_312580 : Nat := 118140960795 + 312580 * 2 ^ 59
def prefixEnd_312580 : Nat := 4983230072969 + 3 ^ 40 * 312580 * 2
def baseEnd_312580 : Nat := 142670029317770900455535

theorem tailTrace_312580 : CollatzResearch.WordTrace tailWord_312580 prefixEnd_312580 142670029317770900455535 := by
  unfold tailWord_312580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5700364603791759629479597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7600486138389012839306129 5700364603791759629479597)
  ·
    refine ⟨2137636726421909861054849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5700364603791759629479597 2137636726421909861054849)
    ·
      refine ⟨1603227544816432395791137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2137636726421909861054849 1603227544816432395791137)
      ·
        refine ⟨1202420658612324296843353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603227544816432395791137 1202420658612324296843353)
        ·
          refine ⟨901815493959243222632515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202420658612324296843353 901815493959243222632515)
          ·
            refine ⟨1352723240938864833948773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901815493959243222632515 1352723240938864833948773)
            ·
              refine ⟨253635607676037156365395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1352723240938864833948773 253635607676037156365395)
              ·
                refine ⟨380453411514055734548093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253635607676037156365395 380453411514055734548093)
                ·
                  refine ⟨142670029317770900455535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380453411514055734548093 142670029317770900455535)
                  ·
                    rfl

theorem cell20_312580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_312580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312580 prefixEnd_312580 := by exact prefixLift 312580
  have htrace : WordTrace (prefixWord ++ tailWord_312580) baseStart_312580 baseEnd_312580 := by
    simpa [prefixWord, tailWord_312580, baseEnd_312580] using wordTrace_append hprefix tailTrace_312580
  have hstable : (prefixWord ++ tailWord_312580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312580).length < 2 ^ (prefixWord ++ tailWord_312580).sum := by decide
  have hdescent : baseEnd_312580 < baseStart_312580 := by decide
  rcases family_descends (prefixWord ++ tailWord_312580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312615 : List Nat := [1, 1, 8, 10]
def baseStart_312615 : Nat := 118140960795 + 312615 * 2 ^ 59
def prefixEnd_312615 : Nat := 4983230072969 + 3 ^ 40 * 312615 * 2
def baseEnd_312615 : Nat := 587185202763235943575

theorem tailTrace_312615 : CollatzResearch.WordTrace tailWord_312615 prefixEnd_312615 587185202763235943575 := by
  unfold tailWord_312615
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402005762456720236483299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7601337174971146824322199 11402005762456720236483299)
  ·
    refine ⟨17103008643685080354724949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11402005762456720236483299 17103008643685080354724949)
    ·
      refine ⟨200425882543184535406933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 17103008643685080354724949 200425882543184535406933)
      ·
        refine ⟨587185202763235943575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 200425882543184535406933 587185202763235943575)
        ·
          rfl

theorem cell20_312615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 10].length) (baseStart_312615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312615 prefixEnd_312615 := by exact prefixLift 312615
  have htrace : WordTrace (prefixWord ++ tailWord_312615) baseStart_312615 baseEnd_312615 := by
    simpa [prefixWord, tailWord_312615, baseEnd_312615] using wordTrace_append hprefix tailTrace_312615
  have hstable : (prefixWord ++ tailWord_312615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312615).length < 2 ^ (prefixWord ++ tailWord_312615).sum := by decide
  have hdescent : baseEnd_312615 < baseStart_312615 := by decide
  rcases family_descends (prefixWord ++ tailWord_312615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312618 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_312618 : Nat := 118140960795 + 312618 * 2 ^ 59
def prefixEnd_312618 : Nat := 4983230072969 + 3 ^ 40 * 312618 * 2
def baseEnd_312618 : Nat := 142687373553211657188713

theorem tailTrace_312618 : CollatzResearch.WordTrace tailWord_312618 prefixEnd_312618 142687373553211657188713 := by
  unfold tailWord_312618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850528795361462937210627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7601410120963901165895005 2850528795361462937210627)
  ·
    refine ⟨4275793193042194405815941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850528795361462937210627 4275793193042194405815941)
    ·
      refine ⟨801711223695411451090489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4275793193042194405815941 801711223695411451090489)
      ·
        refine ⟨601283417771558588317867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801711223695411451090489 601283417771558588317867)
        ·
          refine ⟨901925126657337882476801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601283417771558588317867 901925126657337882476801)
          ·
            refine ⟨676443844993003411857601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901925126657337882476801 676443844993003411857601)
            ·
              refine ⟨507332883744752558893201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676443844993003411857601 507332883744752558893201)
              ·
                refine ⟨380499662808564419169901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507332883744752558893201 380499662808564419169901)
                ·
                  refine ⟨142687373553211657188713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380499662808564419169901 142687373553211657188713)
                  ·
                    rfl

theorem cell20_312618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_312618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312618 prefixEnd_312618 := by exact prefixLift 312618
  have htrace : WordTrace (prefixWord ++ tailWord_312618) baseStart_312618 baseEnd_312618 := by
    simpa [prefixWord, tailWord_312618, baseEnd_312618] using wordTrace_append hprefix tailTrace_312618
  have hstable : (prefixWord ++ tailWord_312618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312618).length < 2 ^ (prefixWord ++ tailWord_312618).sum := by decide
  have hdescent : baseEnd_312618 < baseStart_312618 := by decide
  rcases family_descends (prefixWord ++ tailWord_312618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312621 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 2]
def baseStart_312621 : Nat := 118140960795 + 312621 * 2 ^ 59
def prefixEnd_312621 : Nat := 4983230072969 + 3 ^ 40 * 312621 * 2
def baseEnd_312621 : Nat := 142688742834956980088701

theorem tailTrace_312621 : CollatzResearch.WordTrace tailWord_312621 prefixEnd_312621 142688742834956980088701 := by
  unfold tailWord_312621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402224600434983261201717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7601483066956655507467811 11402224600434983261201717)
  ·
    refine ⟨1068958556290779680737661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11402224600434983261201717 1068958556290779680737661)
    ·
      refine ⟨400859458609042380276623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1068958556290779680737661 400859458609042380276623)
      ·
        refine ⟨601289187913563570414935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400859458609042380276623 601289187913563570414935)
        ·
          refine ⟨901933781870345355622403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601289187913563570414935 901933781870345355622403)
          ·
            refine ⟨1352900672805518033433605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901933781870345355622403 1352900672805518033433605)
            ·
              refine ⟨253668876151034631268801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1352900672805518033433605 253668876151034631268801)
              ·
                refine ⟨190251657113275973451601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253668876151034631268801 190251657113275973451601)
                ·
                  refine ⟨142688742834956980088701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190251657113275973451601 142688742834956980088701)
                  ·
                    rfl

theorem cell20_312621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_312621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312621 prefixEnd_312621 := by exact prefixLift 312621
  have htrace : WordTrace (prefixWord ++ tailWord_312621) baseStart_312621 baseEnd_312621 := by
    simpa [prefixWord, tailWord_312621, baseEnd_312621] using wordTrace_append hprefix tailTrace_312621
  have hstable : (prefixWord ++ tailWord_312621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312621).length < 2 ^ (prefixWord ++ tailWord_312621).sum := by decide
  have hdescent : baseEnd_312621 < baseStart_312621 := by decide
  rcases family_descends (prefixWord ++ tailWord_312621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312625 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 2]
def baseStart_312625 : Nat := 118140960795 + 312625 * 2 ^ 59
def prefixEnd_312625 : Nat := 4983230072969 + 3 ^ 40 * 312625 * 2
def baseEnd_312625 : Nat := 142690568543950743955351

theorem tailTrace_312625 : CollatzResearch.WordTrace tailWord_312625 prefixEnd_312625 142690568543950743955351 := by
  unfold tailWord_312625
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402370492420491944347329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7601580328280327962898219 11402370492420491944347329)
  ·
    refine ⟨8551777869315368958260497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11402370492420491944347329 8551777869315368958260497)
    ·
      refine ⟨6413833401986526718695373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8551777869315368958260497 6413833401986526718695373)
      ·
        refine ⟨2405187525744947519510765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6413833401986526718695373 2405187525744947519510765)
        ·
          refine ⟨901945322154355319816537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2405187525744947519510765 901945322154355319816537)
          ·
            refine ⟨676458991615766489862403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901945322154355319816537 676458991615766489862403)
            ·
              refine ⟨1014688487423649734793605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676458991615766489862403 1014688487423649734793605)
              ·
                refine ⟨190254091391934325273801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1014688487423649734793605 190254091391934325273801)
                ·
                  refine ⟨142690568543950743955351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190254091391934325273801 142690568543950743955351)
                  ·
                    rfl

theorem cell20_312625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_312625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312625 prefixEnd_312625 := by exact prefixLift 312625
  have htrace : WordTrace (prefixWord ++ tailWord_312625) baseStart_312625 baseEnd_312625 := by
    simpa [prefixWord, tailWord_312625, baseEnd_312625] using wordTrace_append hprefix tailTrace_312625
  have hstable : (prefixWord ++ tailWord_312625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312625).length < 2 ^ (prefixWord ++ tailWord_312625).sum := by decide
  have hdescent : baseEnd_312625 < baseStart_312625 := by decide
  rcases family_descends (prefixWord ++ tailWord_312625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312643 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_312643 : Nat := 118140960795 + 312643 * 2 ^ 59
def prefixEnd_312643 : Nat := 4983230072969 + 3 ^ 40 * 312643 * 2
def baseEnd_312643 : Nat := 142698784234422681355277

theorem tailTrace_312643 : CollatzResearch.WordTrace tailWord_312643 prefixEnd_312643 142698784234422681355277 := by
  unfold tailWord_312643
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403027006355281018502583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7602018004236854012335055 11403027006355281018502583)
  ·
    refine ⟨17104540509532921527753875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11403027006355281018502583 17104540509532921527753875)
    ·
      refine ⟨25656810764299382291630813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17104540509532921527753875 25656810764299382291630813)
      ·
        refine ⟨9621304036612268359361555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25656810764299382291630813 9621304036612268359361555)
        ·
          refine ⟨14431956054918402539042333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621304036612268359361555 14431956054918402539042333)
          ·
            refine ⟨5411983520594400952140875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14431956054918402539042333 5411983520594400952140875)
            ·
              refine ⟨8117975280891601428211313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411983520594400952140875 8117975280891601428211313)
              ·
                refine ⟨6088481460668701071158485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117975280891601428211313 6088481460668701071158485)
                ·
                  refine ⟨142698784234422681355277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6088481460668701071158485 142698784234422681355277)
                  ·
                    rfl

theorem cell20_312643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_312643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312643 prefixEnd_312643 := by exact prefixLift 312643
  have htrace : WordTrace (prefixWord ++ tailWord_312643) baseStart_312643 baseEnd_312643 := by
    simpa [prefixWord, tailWord_312643, baseEnd_312643] using wordTrace_append hprefix tailTrace_312643
  have hstable : (prefixWord ++ tailWord_312643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312643).length < 2 ^ (prefixWord ++ tailWord_312643).sum := by decide
  have hdescent : baseEnd_312643 < baseStart_312643 := by decide
  rcases family_descends (prefixWord ++ tailWord_312643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312660 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_312660 : Nat := 118140960795 + 312660 * 2 ^ 59
def prefixEnd_312660 : Nat := 4983230072969 + 3 ^ 40 * 312660 * 2
def baseEnd_312660 : Nat := 142706543497646177788541

theorem tailTrace_312660 : CollatzResearch.WordTrace tailWord_312660 prefixEnd_312660 142706543497646177788541 := by
  unfold tailWord_312660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701823523646846460935717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7602431364862461947914289 5701823523646846460935717)
  ·
    refine ⟨1069091910683783711425447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5701823523646846460935717 1069091910683783711425447)
    ·
      refine ⟨1603637866025675567138171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069091910683783711425447 1603637866025675567138171)
      ·
        refine ⟨2405456799038513350707257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603637866025675567138171 2405456799038513350707257)
        ·
          refine ⟨1804092599278885013030443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405456799038513350707257 1804092599278885013030443)
          ·
            refine ⟨2706138898918327519545665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804092599278885013030443 2706138898918327519545665)
            ·
              refine ⟨2029604174188745639659249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706138898918327519545665 2029604174188745639659249)
              ·
                refine ⟨1522203130641559229744437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029604174188745639659249 1522203130641559229744437)
                ·
                  refine ⟨142706543497646177788541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522203130641559229744437 142706543497646177788541)
                  ·
                    rfl

theorem cell20_312660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_312660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312660 prefixEnd_312660 := by exact prefixLift 312660
  have htrace : WordTrace (prefixWord ++ tailWord_312660) baseStart_312660 baseEnd_312660 := by
    simpa [prefixWord, tailWord_312660, baseEnd_312660] using wordTrace_append hprefix tailTrace_312660
  have hstable : (prefixWord ++ tailWord_312660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312660).length < 2 ^ (prefixWord ++ tailWord_312660).sum := by decide
  have hdescent : baseEnd_312660 < baseStart_312660 := by decide
  rcases family_descends (prefixWord ++ tailWord_312660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312663 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 2]
def baseStart_312663 : Nat := 118140960795 + 312663 * 2 ^ 59
def prefixEnd_312663 : Nat := 4983230072969 + 3 ^ 40 * 312663 * 2
def baseEnd_312663 : Nat := 142707912779391500688529

theorem tailTrace_312663 : CollatzResearch.WordTrace tailWord_312663 prefixEnd_312663 142707912779391500688529 := by
  unfold tailWord_312663
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403756466282824434230643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7602504310855216289487095 11403756466282824434230643)
  ·
    refine ⟨17105634699424236651345965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11403756466282824434230643 17105634699424236651345965)
    ·
      refine ⟨6414613012284088744254737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17105634699424236651345965 6414613012284088744254737)
      ·
        refine ⟨4810959759213066558191053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6414613012284088744254737 4810959759213066558191053)
        ·
          refine ⟨1804109909704899959321645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4810959759213066558191053 1804109909704899959321645)
          ·
            refine ⟨676541216139337484745617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804109909704899959321645 676541216139337484745617)
            ·
              refine ⟨507405912104503113559213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676541216139337484745617 507405912104503113559213)
              ·
                refine ⟨190277217039188667584705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507405912104503113559213 190277217039188667584705)
                ·
                  refine ⟨142707912779391500688529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190277217039188667584705 142707912779391500688529)
                  ·
                    rfl

theorem cell20_312663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2].length) (baseStart_312663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312663 prefixEnd_312663 := by exact prefixLift 312663
  have htrace : WordTrace (prefixWord ++ tailWord_312663) baseStart_312663 baseEnd_312663 := by
    simpa [prefixWord, tailWord_312663, baseEnd_312663] using wordTrace_append hprefix tailTrace_312663
  have hstable : (prefixWord ++ tailWord_312663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312663).length < 2 ^ (prefixWord ++ tailWord_312663).sum := by decide
  have hdescent : baseEnd_312663 < baseStart_312663 := by decide
  rcases family_descends (prefixWord ++ tailWord_312663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312669 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 3]
def baseStart_312669 : Nat := 118140960795 + 312669 * 2 ^ 59
def prefixEnd_312669 : Nat := 4983230072969 + 3 ^ 40 * 312669 * 2
def baseEnd_312669 : Nat := 142710651342882146488505

theorem tailTrace_312669 : CollatzResearch.WordTrace tailWord_312669 prefixEnd_312669 142710651342882146488505 := by
  unfold tailWord_312669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403975304261087458949061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7602650202840724972632707 11403975304261087458949061)
  ·
    refine ⟨2138245369548953898552949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11403975304261087458949061 2138245369548953898552949)
    ·
      refine ⟨200460503395214427989339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2138245369548953898552949 200460503395214427989339)
      ·
        refine ⟨300690755092821641984009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200460503395214427989339 300690755092821641984009)
        ·
          refine ⟨225518066319616231488007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300690755092821641984009 225518066319616231488007)
          ·
            refine ⟨338277099479424347232011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225518066319616231488007 338277099479424347232011)
            ·
              refine ⟨507415649219136520848017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338277099479424347232011 507415649219136520848017)
              ·
                refine ⟨380561736914352390636013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507415649219136520848017 380561736914352390636013)
                ·
                  refine ⟨142710651342882146488505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380561736914352390636013 142710651342882146488505)
                  ·
                    rfl

theorem cell20_312669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_312669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312669 prefixEnd_312669 := by exact prefixLift 312669
  have htrace : WordTrace (prefixWord ++ tailWord_312669) baseStart_312669 baseEnd_312669 := by
    simpa [prefixWord, tailWord_312669, baseEnd_312669] using wordTrace_append hprefix tailTrace_312669
  have hstable : (prefixWord ++ tailWord_312669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312669).length < 2 ^ (prefixWord ++ tailWord_312669).sum := by decide
  have hdescent : baseEnd_312669 < baseStart_312669 := by decide
  rcases family_descends (prefixWord ++ tailWord_312669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312684 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_312684 : Nat := 118140960795 + 312684 * 2 ^ 59
def prefixEnd_312684 : Nat := 4983230072969 + 3 ^ 40 * 312684 * 2
def baseEnd_312684 : Nat := 142717497751608760988443

theorem tailTrace_312684 : CollatzResearch.WordTrace tailWord_312684 prefixEnd_312684 142717497751608760988443 := by
  unfold tailWord_312684
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702261199603372510372553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7603014932804496680496737 5702261199603372510372553)
  ·
    refine ⟨4276695899702529382779415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5702261199603372510372553 4276695899702529382779415)
    ·
      refine ⟨6415043849553794074169123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276695899702529382779415 6415043849553794074169123)
      ·
        refine ⟨9622565774330691111253685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415043849553794074169123 9622565774330691111253685)
        ·
          refine ⟨902115541343502291680033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9622565774330691111253685 902115541343502291680033)
          ·
            refine ⟨676586656007626718760025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902115541343502291680033 676586656007626718760025)
            ·
              refine ⟨507439992005720039070019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676586656007626718760025 507439992005720039070019)
              ·
                refine ⟨761159988008580058605029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507439992005720039070019 761159988008580058605029)
                ·
                  refine ⟨142717497751608760988443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761159988008580058605029 142717497751608760988443)
                  ·
                    rfl

theorem cell20_312684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_312684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312684 prefixEnd_312684 := by exact prefixLift 312684
  have htrace : WordTrace (prefixWord ++ tailWord_312684) baseStart_312684 baseEnd_312684 := by
    simpa [prefixWord, tailWord_312684, baseEnd_312684] using wordTrace_append hprefix tailTrace_312684
  have hstable : (prefixWord ++ tailWord_312684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312684).length < 2 ^ (prefixWord ++ tailWord_312684).sum := by decide
  have hdescent : baseEnd_312684 < baseStart_312684 := by decide
  rcases family_descends (prefixWord ++ tailWord_312684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312708 : List Nat := [2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_312708 : Nat := 118140960795 + 312708 * 2 ^ 59
def prefixEnd_312708 : Nat := 4983230072969 + 3 ^ 40 * 312708 * 2
def baseEnd_312708 : Nat := 47576150668523781396115

theorem tailTrace_312708 : CollatzResearch.WordTrace tailWord_312708 prefixEnd_312708 47576150668523781396115 := by
  unfold tailWord_312708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702698875559898559809389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7603598500746531413079185 5702698875559898559809389)
  ·
    refine ⟨2138512078334961959928521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5702698875559898559809389 2138512078334961959928521)
    ·
      refine ⟨1603884058751221469946391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2138512078334961959928521 1603884058751221469946391)
      ·
        refine ⟨2405826088126832204919587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603884058751221469946391 2405826088126832204919587)
        ·
          refine ⟨3608739132190248307379381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405826088126832204919587 3608739132190248307379381)
          ·
            refine ⟨338319293642835778816817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3608739132190248307379381 338319293642835778816817)
            ·
              refine ⟨253739470232126834112613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338319293642835778816817 253739470232126834112613)
              ·
                refine ⟨47576150668523781396115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253739470232126834112613 47576150668523781396115)
                ·
                  rfl

theorem cell20_312708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_312708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312708 prefixEnd_312708 := by exact prefixLift 312708
  have htrace : WordTrace (prefixWord ++ tailWord_312708) baseStart_312708 baseEnd_312708 := by
    simpa [prefixWord, tailWord_312708, baseEnd_312708] using wordTrace_append hprefix tailTrace_312708
  have hstable : (prefixWord ++ tailWord_312708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312708).length < 2 ^ (prefixWord ++ tailWord_312708).sum := by decide
  have hdescent : baseEnd_312708 < baseStart_312708 := by decide
  rcases family_descends (prefixWord ++ tailWord_312708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312736 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_312736 : Nat := 118140960795 + 312736 * 2 ^ 59
def prefixEnd_312736 : Nat := 4983230072969 + 3 ^ 40 * 312736 * 2
def baseEnd_312736 : Nat := 142741231968527691254897

theorem tailTrace_312736 : CollatzResearch.WordTrace tailWord_312736 prefixEnd_312736 142741231968527691254897 := by
  unfold tailWord_312736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703209497509178950819031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7604279330012238601092041 5703209497509178950819031)
  ·
    refine ⟨8554814246263768426228547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5703209497509178950819031 8554814246263768426228547)
    ·
      refine ⟨12832221369395652639342821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8554814246263768426228547 12832221369395652639342821)
      ·
        refine ⟨2406041506761684869876779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12832221369395652639342821 2406041506761684869876779)
        ·
          refine ⟨3609062260142527304815169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406041506761684869876779 3609062260142527304815169)
          ·
            refine ⟨2706796695106895478611377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3609062260142527304815169 2706796695106895478611377)
            ·
              refine ⟨2030097521330171608958533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706796695106895478611377 2030097521330171608958533)
              ·
                refine ⟨380643285249407176679725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2030097521330171608958533 380643285249407176679725)
                ·
                  refine ⟨142741231968527691254897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380643285249407176679725 142741231968527691254897)
                  ·
                    rfl

theorem cell20_312736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_312736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312736 prefixEnd_312736 := by exact prefixLift 312736
  have htrace : WordTrace (prefixWord ++ tailWord_312736) baseStart_312736 baseEnd_312736 := by
    simpa [prefixWord, tailWord_312736, baseEnd_312736] using wordTrace_append hprefix tailTrace_312736
  have hstable : (prefixWord ++ tailWord_312736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312736).length < 2 ^ (prefixWord ++ tailWord_312736).sum := by decide
  have hdescent : baseEnd_312736 < baseStart_312736 := by decide
  rcases family_descends (prefixWord ++ tailWord_312736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312739 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 2]
def baseStart_312739 : Nat := 118140960795 + 312739 * 2 ^ 59
def prefixEnd_312739 : Nat := 4983230072969 + 3 ^ 40 * 312739 * 2
def baseEnd_312739 : Nat := 142742601250273014154885

theorem tailTrace_312739 : CollatzResearch.WordTrace tailWord_312739 prefixEnd_312739 142742601250273014154885 := by
  unfold tailWord_312739
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406528414007489413997271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7604352276004992942664847 11406528414007489413997271)
  ·
    refine ⟨17109792621011234120995907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11406528414007489413997271 17109792621011234120995907)
    ·
      refine ⟨25664688931516851181493861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17109792621011234120995907 25664688931516851181493861)
      ·
        refine ⟨4812129174659409596530099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25664688931516851181493861 4812129174659409596530099)
        ·
          refine ⟨7218193761989114394795149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812129174659409596530099 7218193761989114394795149)
          ·
            refine ⟨2706822660745917898048181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7218193761989114394795149 2706822660745917898048181)
            ·
              refine ⟨253764624444929802942017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2706822660745917898048181 253764624444929802942017)
              ·
                refine ⟨190323468333697352206513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253764624444929802942017 190323468333697352206513)
                ·
                  refine ⟨142742601250273014154885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190323468333697352206513 142742601250273014154885)
                  ·
                    rfl

theorem cell20_312739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2].length) (baseStart_312739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312739 prefixEnd_312739 := by exact prefixLift 312739
  have htrace : WordTrace (prefixWord ++ tailWord_312739) baseStart_312739 baseEnd_312739 := by
    simpa [prefixWord, tailWord_312739, baseEnd_312739] using wordTrace_append hprefix tailTrace_312739
  have hstable : (prefixWord ++ tailWord_312739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312739).length < 2 ^ (prefixWord ++ tailWord_312739).sum := by decide
  have hdescent : baseEnd_312739 < baseStart_312739 := by decide
  rcases family_descends (prefixWord ++ tailWord_312739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312749 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 3]
def baseStart_312749 : Nat := 118140960795 + 312749 * 2 ^ 59
def prefixEnd_312749 : Nat := 4983230072969 + 3 ^ 40 * 312749 * 2
def baseEnd_312749 : Nat := 142747165522757423821511

theorem tailTrace_312749 : CollatzResearch.WordTrace tailWord_312749 prefixEnd_312749 142747165522757423821511 := by
  unfold tailWord_312749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406893143971261121861301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7604595429314174081240867 11406893143971261121861301)
  ·
    refine ⟨1069396232247305730174497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11406893143971261121861301 1069396232247305730174497)
    ·
      refine ⟨802047174185479297630873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1069396232247305730174497 802047174185479297630873)
      ·
        refine ⟨601535380639109473223155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 802047174185479297630873 601535380639109473223155)
        ·
          refine ⟨902303070958664209834733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601535380639109473223155 902303070958664209834733)
          ·
            refine ⟨338363651609499078688025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 902303070958664209834733 338363651609499078688025)
            ·
              refine ⟨253772738707124309016019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338363651609499078688025 253772738707124309016019)
              ·
                refine ⟨380659108060686463524029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253772738707124309016019 380659108060686463524029)
                ·
                  refine ⟨142747165522757423821511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380659108060686463524029 142747165522757423821511)
                  ·
                    rfl

theorem cell20_312749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_312749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312749 prefixEnd_312749 := by exact prefixLift 312749
  have htrace : WordTrace (prefixWord ++ tailWord_312749) baseStart_312749 baseEnd_312749 := by
    simpa [prefixWord, tailWord_312749, baseEnd_312749] using wordTrace_append hprefix tailTrace_312749
  have hstable : (prefixWord ++ tailWord_312749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312749).length < 2 ^ (prefixWord ++ tailWord_312749).sum := by decide
  have hdescent : baseEnd_312749 < baseStart_312749 := by decide
  rcases family_descends (prefixWord ++ tailWord_312749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312788 : List Nat := [2, 4, 1, 2, 11]
def baseStart_312788 : Nat := 118140960795 + 312788 * 2 ^ 59
def prefixEnd_312788 : Nat := 4983230072969 + 3 ^ 40 * 312788 * 2
def baseEnd_312788 : Nat := 1762530446733908907671

theorem tailTrace_312788 : CollatzResearch.WordTrace tailWord_312788 prefixEnd_312788 1762530446733908907671 := by
  unfold tailWord_312788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704157795414985391265509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7605543727219980521687345 5704157795414985391265509)
  ·
    refine ⟨1069529586640309760862283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5704157795414985391265509 1069529586640309760862283)
    ·
      refine ⟨1604294379960464641293425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069529586640309760862283 1604294379960464641293425)
      ·
        refine ⟨1203220784970348480970069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1604294379960464641293425 1203220784970348480970069)
        ·
          refine ⟨1762530446733908907671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1203220784970348480970069 1762530446733908907671)
          ·
            rfl

theorem cell20_312788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 11].length) (baseStart_312788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312788 prefixEnd_312788 := by exact prefixLift 312788
  have htrace : WordTrace (prefixWord ++ tailWord_312788) baseStart_312788 baseEnd_312788 := by
    simpa [prefixWord, tailWord_312788, baseEnd_312788] using wordTrace_append hprefix tailTrace_312788
  have hstable : (prefixWord ++ tailWord_312788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312788).length < 2 ^ (prefixWord ++ tailWord_312788).sum := by decide
  have hdescent : baseEnd_312788 < baseStart_312788 := by decide
  rcases family_descends (prefixWord ++ tailWord_312788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312794 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_312794 : Nat := 118140960795 + 312794 * 2 ^ 59
def prefixEnd_312794 : Nat := 4983230072969 + 3 ^ 40 * 312794 * 2
def baseEnd_312794 : Nat := 142767704748937267321327

theorem tailTrace_312794 : CollatzResearch.WordTrace tailWord_312794 prefixEnd_312794 142767704748937267321327 := by
  unfold tailWord_312794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852133607202058451812359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7605689619205489204832957 2852133607202058451812359)
  ·
    refine ⟨4278200410803087677718539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852133607202058451812359 4278200410803087677718539)
    ·
      refine ⟨6417300616204631516577809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278200410803087677718539 6417300616204631516577809)
      ·
        refine ⟨4812975462153473637433357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6417300616204631516577809 4812975462153473637433357)
        ·
          refine ⟨1804865798307552614037509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4812975462153473637433357 1804865798307552614037509)
          ·
            refine ⟨338412337182666115132033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1804865798307552614037509 338412337182666115132033)
            ·
              refine ⟨253809252886999586349025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338412337182666115132033 253809252886999586349025)
              ·
                refine ⟨190356939665249689761769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253809252886999586349025 190356939665249689761769)
                ·
                  refine ⟨142767704748937267321327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190356939665249689761769 142767704748937267321327)
                  ·
                    rfl

theorem cell20_312794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_312794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312794 prefixEnd_312794 := by exact prefixLift 312794
  have htrace : WordTrace (prefixWord ++ tailWord_312794) baseStart_312794 baseEnd_312794 := by
    simpa [prefixWord, tailWord_312794, baseEnd_312794] using wordTrace_append hprefix tailTrace_312794
  have hstable : (prefixWord ++ tailWord_312794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312794).length < 2 ^ (prefixWord ++ tailWord_312794).sum := by decide
  have hdescent : baseEnd_312794 < baseStart_312794 := by decide
  rcases family_descends (prefixWord ++ tailWord_312794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312805 : List Nat := [1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_312805 : Nat := 118140960795 + 312805 * 2 ^ 59
def prefixEnd_312805 : Nat := 4983230072969 + 3 ^ 40 * 312805 * 2
def baseEnd_312805 : Nat := 47590908482890039318205

theorem tailTrace_312805 : CollatzResearch.WordTrace tailWord_312805 prefixEnd_312805 47590908482890039318205 := by
  unfold tailWord_312805
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408935631768382685899869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7605957087845588457266579 11408935631768382685899869)
  ·
    refine ⟨4278350861913143507212451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11408935631768382685899869 4278350861913143507212451)
    ·
      refine ⟨6417526292869715260818677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278350861913143507212451 6417526292869715260818677)
      ·
        refine ⟨601643089956535805701751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6417526292869715260818677 601643089956535805701751)
        ·
          refine ⟨902464634934803708552627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601643089956535805701751 902464634934803708552627)
          ·
            refine ⟨1353696952402205562828941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902464634934803708552627 1353696952402205562828941)
            ·
              refine ⟨507636357150827086060853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1353696952402205562828941 507636357150827086060853)
              ·
                refine ⟨47590908482890039318205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 507636357150827086060853 47590908482890039318205)
                ·
                  rfl

theorem cell20_312805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_312805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312805 prefixEnd_312805 := by exact prefixLift 312805
  have htrace : WordTrace (prefixWord ++ tailWord_312805) baseStart_312805 baseEnd_312805 := by
    simpa [prefixWord, tailWord_312805, baseEnd_312805] using wordTrace_append hprefix tailTrace_312805
  have hstable : (prefixWord ++ tailWord_312805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312805).length < 2 ^ (prefixWord ++ tailWord_312805).sum := by decide
  have hdescent : baseEnd_312805 < baseStart_312805 := by decide
  rcases family_descends (prefixWord ++ tailWord_312805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312822 : List Nat := [5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_312822 : Nat := 118140960795 + 312822 * 2 ^ 59
def prefixEnd_312822 : Nat := 4983230072969 + 3 ^ 40 * 312822 * 2
def baseEnd_312822 : Nat := 47593494903964538129293

theorem tailTrace_312822 : CollatzResearch.WordTrace tailWord_312822 prefixEnd_312822 47593494903964538129293 := by
  unfold tailWord_312822
  simp only [CollatzResearch.WordTrace]
  refine ⟨713097229544174661829295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7606370448471196392845813 713097229544174661829295)
  ·
    refine ⟨1069645844316261992743943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713097229544174661829295 1069645844316261992743943)
    ·
      refine ⟨1604468766474392989115915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069645844316261992743943 1604468766474392989115915)
      ·
        refine ⟨2406703149711589483673873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604468766474392989115915 2406703149711589483673873)
        ·
          refine ⟨1805027362283692112755405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406703149711589483673873 1805027362283692112755405)
          ·
            refine ⟨676885260856384542283277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1805027362283692112755405 676885260856384542283277)
            ·
              refine ⟨253831972821144203356229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676885260856384542283277 253831972821144203356229)
              ·
                refine ⟨47593494903964538129293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253831972821144203356229 47593494903964538129293)
                ·
                  rfl

theorem cell20_312822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_312822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312822 prefixEnd_312822 := by exact prefixLift 312822
  have htrace : WordTrace (prefixWord ++ tailWord_312822) baseStart_312822 baseEnd_312822 := by
    simpa [prefixWord, tailWord_312822, baseEnd_312822] using wordTrace_append hprefix tailTrace_312822
  have hstable : (prefixWord ++ tailWord_312822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312822).length < 2 ^ (prefixWord ++ tailWord_312822).sum := by decide
  have hdescent : baseEnd_312822 < baseStart_312822 := by decide
  rcases family_descends (prefixWord ++ tailWord_312822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312846 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_312846 : Nat := 118140960795 + 312846 * 2 ^ 59
def prefixEnd_312846 : Nat := 4983230072969 + 3 ^ 40 * 312846 * 2
def baseEnd_312846 : Nat := 142791438965856197587781

theorem tailTrace_312846 : CollatzResearch.WordTrace tailWord_312846 prefixEnd_312846 142791438965856197587781 := by
  unfold tailWord_312846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426303878077480836017799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7606954016413231125428261 1426303878077480836017799)
  ·
    refine ⟨2139455817116221254026699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426303878077480836017799 2139455817116221254026699)
    ·
      refine ⟨3209183725674331881040049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139455817116221254026699 3209183725674331881040049)
      ·
        refine ⟨2406887794255748910780037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209183725674331881040049 2406887794255748910780037)
        ·
          refine ⟨451291461422952920771257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2406887794255748910780037 451291461422952920771257)
          ·
            refine ⟨338468596067214690578443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451291461422952920771257 338468596067214690578443)
            ·
              refine ⟨507702894100822035867665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338468596067214690578443 507702894100822035867665)
              ·
                refine ⟨380777170575616526900749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507702894100822035867665 380777170575616526900749)
                ·
                  refine ⟨142791438965856197587781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380777170575616526900749 142791438965856197587781)
                  ·
                    rfl

theorem cell20_312846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_312846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312846 prefixEnd_312846 := by exact prefixLift 312846
  have htrace : WordTrace (prefixWord ++ tailWord_312846) baseStart_312846 baseEnd_312846 := by
    simpa [prefixWord, tailWord_312846, baseEnd_312846] using wordTrace_append hprefix tailTrace_312846
  have hstable : (prefixWord ++ tailWord_312846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312846).length < 2 ^ (prefixWord ++ tailWord_312846).sum := by decide
  have hdescent : baseEnd_312846 < baseStart_312846 := by decide
  rcases family_descends (prefixWord ++ tailWord_312846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312954 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_312954 : Nat := 118140960795 + 312954 * 2 ^ 59
def prefixEnd_312954 : Nat := 4983230072969 + 3 ^ 40 * 312954 * 2
def baseEnd_312954 : Nat := 142840733108687821987339

theorem tailTrace_312954 : CollatzResearch.WordTrace tailWord_312954 prefixEnd_312954 142840733108687821987339 := by
  unfold tailWord_312954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853592527057145283268479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7609580072152387422049277 2853592527057145283268479)
  ·
    refine ⟨4280388790585717924902719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853592527057145283268479 4280388790585717924902719)
    ·
      refine ⟨6420583185878576887354079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280388790585717924902719 6420583185878576887354079)
      ·
        refine ⟨9630874778817865331031119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6420583185878576887354079 9630874778817865331031119)
        ·
          refine ⟨14446312168226797996546679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9630874778817865331031119 14446312168226797996546679)
          ·
            refine ⟨21669468252340196994820019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14446312168226797996546679 21669468252340196994820019)
            ·
              refine ⟨32504202378510295492230029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21669468252340196994820019 32504202378510295492230029)
              ·
                refine ⟨12189075891941360809586261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32504202378510295492230029 12189075891941360809586261)
                ·
                  refine ⟨142840733108687821987339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12189075891941360809586261 142840733108687821987339)
                  ·
                    rfl

theorem cell20_312954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_312954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312954 prefixEnd_312954 := by exact prefixLift 312954
  have htrace : WordTrace (prefixWord ++ tailWord_312954) baseStart_312954 baseEnd_312954 := by
    simpa [prefixWord, tailWord_312954, baseEnd_312954] using wordTrace_append hprefix tailTrace_312954
  have hstable : (prefixWord ++ tailWord_312954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312954).length < 2 ^ (prefixWord ++ tailWord_312954).sum := by decide
  have hdescent : baseEnd_312954 < baseStart_312954 := by decide
  rcases family_descends (prefixWord ++ tailWord_312954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312967 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 2]
def baseStart_312967 : Nat := 118140960795 + 312967 * 2 ^ 59
def prefixEnd_312967 : Nat := 4983230072969 + 3 ^ 40 * 312967 * 2
def baseEnd_312967 : Nat := 142846666662917554553953

theorem tailTrace_312967 : CollatzResearch.WordTrace tailWord_312967 prefixEnd_312967 142846666662917554553953 := by
  unfold tailWord_312967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414844257181484353297155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7609896171454322902198103 11414844257181484353297155)
  ·
    refine ⟨17122266385772226529945733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11414844257181484353297155 17122266385772226529945733)
    ·
      refine ⟨3210424947332292474364825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17122266385772226529945733 3210424947332292474364825)
      ·
        refine ⟨2407818710499219355773619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3210424947332292474364825 2407818710499219355773619)
        ·
          refine ⟨3611728065748829033660429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407818710499219355773619 3611728065748829033660429)
          ·
            refine ⟨1354398024655810887622661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3611728065748829033660429 1354398024655810887622661)
            ·
              refine ⟨253949629622964541429249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1354398024655810887622661 253949629622964541429249)
              ·
                refine ⟨190462222217223406071937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253949629622964541429249 190462222217223406071937)
                ·
                  refine ⟨142846666662917554553953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190462222217223406071937 142846666662917554553953)
                  ·
                    rfl

theorem cell20_312967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2].length) (baseStart_312967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312967 prefixEnd_312967 := by exact prefixLift 312967
  have htrace : WordTrace (prefixWord ++ tailWord_312967) baseStart_312967 baseEnd_312967 := by
    simpa [prefixWord, tailWord_312967, baseEnd_312967] using wordTrace_append hprefix tailTrace_312967
  have hstable : (prefixWord ++ tailWord_312967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312967).length < 2 ^ (prefixWord ++ tailWord_312967).sum := by decide
  have hdescent : baseEnd_312967 < baseStart_312967 := by decide
  rcases family_descends (prefixWord ++ tailWord_312967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312988 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_312988 : Nat := 118140960795 + 312988 * 2 ^ 59
def prefixEnd_312988 : Nat := 4983230072969 + 3 ^ 40 * 312988 * 2
def baseEnd_312988 : Nat := 142856251635134814853867

theorem tailTrace_312988 : CollatzResearch.WordTrace tailWord_312988 prefixEnd_312988 142856251635134814853867 := by
  unfold tailWord_312988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707805095052702469905809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7610406793403603293207745 5707805095052702469905809)
  ·
    refine ⟨4280853821289526852429357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5707805095052702469905809 4280853821289526852429357)
    ·
      refine ⟨1605320182983572569661009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4280853821289526852429357 1605320182983572569661009)
      ·
        refine ⟨1203990137237679427245757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605320182983572569661009 1203990137237679427245757)
        ·
          refine ⟨451496301464129785217159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1203990137237679427245757 451496301464129785217159)
          ·
            refine ⟨677244452196194677825739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451496301464129785217159 677244452196194677825739)
            ·
              refine ⟨1015866678294292016738609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677244452196194677825739 1015866678294292016738609)
              ·
                refine ⟨761900008720719012553957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015866678294292016738609 761900008720719012553957)
                ·
                  refine ⟨142856251635134814853867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761900008720719012553957 142856251635134814853867)
                  ·
                    rfl

theorem cell20_312988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_312988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_312988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_312988 prefixEnd_312988 := by exact prefixLift 312988
  have htrace : WordTrace (prefixWord ++ tailWord_312988) baseStart_312988 baseEnd_312988 := by
    simpa [prefixWord, tailWord_312988, baseEnd_312988] using wordTrace_append hprefix tailTrace_312988
  have hstable : (prefixWord ++ tailWord_312988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312988).length < 2 ^ (prefixWord ++ tailWord_312988).sum := by decide
  have hdescent : baseEnd_312988 < baseStart_312988 := by decide
  rcases family_descends (prefixWord ++ tailWord_312988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313005 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 2]
def baseStart_313005 : Nat := 118140960795 + 313005 * 2 ^ 59
def prefixEnd_313005 : Nat := 4983230072969 + 3 ^ 40 * 313005 * 2
def baseEnd_313005 : Nat := 142864010898358311287131

theorem tailTrace_313005 : CollatzResearch.WordTrace tailWord_313005 prefixEnd_313005 142864010898358311287131 := by
  unfold tailWord_313005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416230231043816843180469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7610820154029211228786979 11416230231043816843180469)
  ·
    refine ⟨1070271584160357829048169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11416230231043816843180469 1070271584160357829048169)
    ·
      refine ⟨802703688120268371786127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1070271584160357829048169 802703688120268371786127)
      ·
        refine ⟨1204055532180402557679191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802703688120268371786127 1204055532180402557679191)
        ·
          refine ⟨1806083298270603836518787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204055532180402557679191 1806083298270603836518787)
          ·
            refine ⟨2709124947405905754778181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806083298270603836518787 2709124947405905754778181)
            ·
              refine ⟨507960927638607329020909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2709124947405905754778181 507960927638607329020909)
              ·
                refine ⟨190485347864477748382841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507960927638607329020909 190485347864477748382841)
                ·
                  refine ⟨142864010898358311287131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190485347864477748382841 142864010898358311287131)
                  ·
                    rfl

theorem cell20_313005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_313005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313005 prefixEnd_313005 := by exact prefixLift 313005
  have htrace : WordTrace (prefixWord ++ tailWord_313005) baseStart_313005 baseEnd_313005 := by
    simpa [prefixWord, tailWord_313005, baseEnd_313005] using wordTrace_append hprefix tailTrace_313005
  have hstable : (prefixWord ++ tailWord_313005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313005).length < 2 ^ (prefixWord ++ tailWord_313005).sum := by decide
  have hdescent : baseEnd_313005 < baseStart_313005 := by decide
  rcases family_descends (prefixWord ++ tailWord_313005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313023 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_313023 : Nat := 118140960795 + 313023 * 2 ^ 59
def prefixEnd_313023 : Nat := 4983230072969 + 3 ^ 40 * 313023 * 2
def baseEnd_313023 : Nat := 142872226588830248687057

theorem tailTrace_313023 : CollatzResearch.WordTrace tailWord_313023 prefixEnd_313023 142872226588830248687057 := by
  unfold tailWord_313023
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416886744978605917335723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7611257829985737278223815 11416886744978605917335723)
  ·
    refine ⟨17125330117467908876003585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416886744978605917335723 17125330117467908876003585)
    ·
      refine ⟨12843997588100931657002689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17125330117467908876003585 12843997588100931657002689)
      ·
        refine ⟨9632998191075698742752017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12843997588100931657002689 9632998191075698742752017)
        ·
          refine ⟨7224748643306774057064013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9632998191075698742752017 7224748643306774057064013)
          ·
            refine ⟨2709280741240040271399005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7224748643306774057064013 2709280741240040271399005)
            ·
              refine ⟨1015980277965015101774627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2709280741240040271399005 1015980277965015101774627)
              ·
                refine ⟨1523970416947522652661941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015980277965015101774627 1523970416947522652661941)
                ·
                  refine ⟨142872226588830248687057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1523970416947522652661941 142872226588830248687057)
                  ·
                    rfl

theorem cell20_313023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_313023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313023 prefixEnd_313023 := by exact prefixLift 313023
  have htrace : WordTrace (prefixWord ++ tailWord_313023) baseStart_313023 baseEnd_313023 := by
    simpa [prefixWord, tailWord_313023, baseEnd_313023] using wordTrace_append hprefix tailTrace_313023
  have hstable : (prefixWord ++ tailWord_313023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313023).length < 2 ^ (prefixWord ++ tailWord_313023).sum := by decide
  have hdescent : baseEnd_313023 < baseStart_313023 := by decide
  rcases family_descends (prefixWord ++ tailWord_313023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313036 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_313036 : Nat := 118140960795 + 313036 * 2 ^ 59
def prefixEnd_313036 : Nat := 4983230072969 + 3 ^ 40 * 313036 * 2
def baseEnd_313036 : Nat := 142878160143059981253671

theorem tailTrace_313036 : CollatzResearch.WordTrace tailWord_313036 prefixEnd_313036 142878160143059981253671 := by
  unfold tailWord_313036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708680446965754568779481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7611573929287672758372641 5708680446965754568779481)
  ·
    refine ⟨4281510335224315926584611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5708680446965754568779481 4281510335224315926584611)
    ·
      refine ⟨6422265502836473889876917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281510335224315926584611 6422265502836473889876917)
      ·
        refine ⟨602087390890919427175961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6422265502836473889876917 602087390890919427175961)
        ·
          refine ⟨451565543168189570381971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602087390890919427175961 451565543168189570381971)
          ·
            refine ⟨677348314752284355572957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451565543168189570381971 677348314752284355572957)
            ·
              refine ⟨254005618032106633339859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677348314752284355572957 254005618032106633339859)
              ·
                refine ⟨381008427048159950009789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254005618032106633339859 381008427048159950009789)
                ·
                  refine ⟨142878160143059981253671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381008427048159950009789 142878160143059981253671)
                  ·
                    rfl

theorem cell20_313036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_313036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313036 prefixEnd_313036 := by exact prefixLift 313036
  have htrace : WordTrace (prefixWord ++ tailWord_313036) baseStart_313036 baseEnd_313036 := by
    simpa [prefixWord, tailWord_313036, baseEnd_313036] using wordTrace_append hprefix tailTrace_313036
  have hstable : (prefixWord ++ tailWord_313036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313036).length < 2 ^ (prefixWord ++ tailWord_313036).sum := by decide
  have hdescent : baseEnd_313036 < baseStart_313036 := by decide
  rcases family_descends (prefixWord ++ tailWord_313036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313046 : List Nat := [5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_313046 : Nat := 118140960795 + 313046 * 2 ^ 59
def prefixEnd_313046 : Nat := 4983230072969 + 3 ^ 40 * 313046 * 2
def baseEnd_313046 : Nat := 47627574805181463640099

theorem tailTrace_313046 : CollatzResearch.WordTrace tailWord_313046 prefixEnd_313046 47627574805181463640099 := by
  unfold tailWord_313046
  simp only [CollatzResearch.WordTrace]
  refine ⟨713607851493455052838937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7611817082596853896948661 713607851493455052838937)
  ·
    refine ⟨535205888620091289629203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 713607851493455052838937 535205888620091289629203)
    ·
      refine ⟨802808832930136934443805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535205888620091289629203 802808832930136934443805)
      ·
        refine ⟨301053312348801350416427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 802808832930136934443805 301053312348801350416427)
        ·
          refine ⟨451579968523202025624641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301053312348801350416427 451579968523202025624641)
          ·
            refine ⟨338684976392401519218481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451579968523202025624641 338684976392401519218481)
            ·
              refine ⟨254013732294301139413861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338684976392401519218481 254013732294301139413861)
              ·
                refine ⟨47627574805181463640099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254013732294301139413861 47627574805181463640099)
                ·
                  rfl

theorem cell20_313046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_313046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313046 prefixEnd_313046 := by exact prefixLift 313046
  have htrace : WordTrace (prefixWord ++ tailWord_313046) baseStart_313046 baseEnd_313046 := by
    simpa [prefixWord, tailWord_313046, baseEnd_313046] using wordTrace_append hprefix tailTrace_313046
  have hstable : (prefixWord ++ tailWord_313046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313046).length < 2 ^ (prefixWord ++ tailWord_313046).sum := by decide
  have hdescent : baseEnd_313046 < baseStart_313046 := by decide
  rcases family_descends (prefixWord ++ tailWord_313046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313061 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_313061 : Nat := 118140960795 + 313061 * 2 ^ 59
def prefixEnd_313061 : Nat := 4983230072969 + 3 ^ 40 * 313061 * 2
def baseEnd_313061 : Nat := 142889570824271005420235

theorem tailTrace_313061 : CollatzResearch.WordTrace tailWord_313061 prefixEnd_313061 142889570824271005420235 := by
  unfold tailWord_313061
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418272718840938407219037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7612181812560625604812691 11418272718840938407219037)
  ·
    refine ⟨4281852269565351902707139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11418272718840938407219037 4281852269565351902707139)
    ·
      refine ⟨6422778404348027854060709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281852269565351902707139 6422778404348027854060709)
      ·
        refine ⟨1204270950815255222636383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6422778404348027854060709 1204270950815255222636383)
        ·
          refine ⟨1806406426222882833954575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204270950815255222636383 1806406426222882833954575)
          ·
            refine ⟨2709609639334324250931863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806406426222882833954575 2709609639334324250931863)
            ·
              refine ⟨4064414459001486376397795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709609639334324250931863 4064414459001486376397795)
              ·
                refine ⟨6096621688502229564596693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064414459001486376397795 6096621688502229564596693)
                ·
                  refine ⟨142889570824271005420235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6096621688502229564596693 142889570824271005420235)
                  ·
                    rfl

theorem cell20_313061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_313061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313061 prefixEnd_313061 := by exact prefixLift 313061
  have htrace : WordTrace (prefixWord ++ tailWord_313061) baseStart_313061 baseEnd_313061 := by
    simpa [prefixWord, tailWord_313061, baseEnd_313061] using wordTrace_append hprefix tailTrace_313061
  have hstable : (prefixWord ++ tailWord_313061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313061).length < 2 ^ (prefixWord ++ tailWord_313061).sum := by decide
  have hdescent : baseEnd_313061 < baseStart_313061 := by decide
  rcases family_descends (prefixWord ++ tailWord_313061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313068 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_313068 : Nat := 118140960795 + 313068 * 2 ^ 59
def prefixEnd_313068 : Nat := 4983230072969 + 3 ^ 40 * 313068 * 2
def baseEnd_313068 : Nat := 142892765815010092186873

theorem tailTrace_313068 : CollatzResearch.WordTrace tailWord_313068 prefixEnd_313068 142892765815010092186873 := by
  unfold tailWord_313068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709264014907789301361929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7612352019877052401815905 5709264014907789301361929)
  ·
    refine ⟨4281948011180841976021447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5709264014907789301361929 4281948011180841976021447)
    ·
      refine ⟨6422922016771262964032171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281948011180841976021447 6422922016771262964032171)
      ·
        refine ⟨9634383025156894446048257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422922016771262964032171 9634383025156894446048257)
        ·
          refine ⟨7225787268867670834536193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634383025156894446048257 7225787268867670834536193)
          ·
            refine ⟨5419340451650753125902145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7225787268867670834536193 5419340451650753125902145)
            ·
              refine ⟨4064505338738064844426609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419340451650753125902145 4064505338738064844426609)
              ·
                refine ⟨3048379004053548633319957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064505338738064844426609 3048379004053548633319957)
                ·
                  refine ⟨142892765815010092186873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3048379004053548633319957 142892765815010092186873)
                  ·
                    rfl

theorem cell20_313068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_313068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313068 prefixEnd_313068 := by exact prefixLift 313068
  have htrace : WordTrace (prefixWord ++ tailWord_313068) baseStart_313068 baseEnd_313068 := by
    simpa [prefixWord, tailWord_313068, baseEnd_313068] using wordTrace_append hprefix tailTrace_313068
  have hstable : (prefixWord ++ tailWord_313068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313068).length < 2 ^ (prefixWord ++ tailWord_313068).sum := by decide
  have hdescent : baseEnd_313068 < baseStart_313068 := by decide
  rcases family_descends (prefixWord ++ tailWord_313068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313075 : List Nat := [1, 1, 1, 2, 2, 3, 10]
def baseStart_313075 : Nat := 118140960795 + 313075 * 2 ^ 59
def prefixEnd_313075 : Nat := 4983230072969 + 3 ^ 40 * 313075 * 2
def baseEnd_313075 : Nat := 15877328978416575439279

theorem tailTrace_313075 : CollatzResearch.WordTrace tailWord_313075 prefixEnd_313075 15877328978416575439279 := by
  unfold tailWord_313075
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418783340790218798228679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7612522227193479198819119 11418783340790218798228679)
  ·
    refine ⟨17128175011185328197343019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11418783340790218798228679 17128175011185328197343019)
    ·
      refine ⟨25692262516777992296014529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17128175011185328197343019 25692262516777992296014529)
      ·
        refine ⟨19269196887583494222010897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25692262516777992296014529 19269196887583494222010897)
        ·
          refine ⟨14451897665687620666508173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19269196887583494222010897 14451897665687620666508173)
          ·
            refine ⟨5419461624632857749940565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14451897665687620666508173 5419461624632857749940565)
            ·
              refine ⟨15877328978416575439279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5419461624632857749940565 15877328978416575439279)
              ·
                rfl

theorem cell20_313075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_313075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313075 prefixEnd_313075 := by exact prefixLift 313075
  have htrace : WordTrace (prefixWord ++ tailWord_313075) baseStart_313075 baseEnd_313075 := by
    simpa [prefixWord, tailWord_313075, baseEnd_313075] using wordTrace_append hprefix tailTrace_313075
  have hstable : (prefixWord ++ tailWord_313075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313075).length < 2 ^ (prefixWord ++ tailWord_313075).sum := by decide
  have hdescent : baseEnd_313075 < baseStart_313075 := by decide
  rcases family_descends (prefixWord ++ tailWord_313075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313078 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_313078 : Nat := 118140960795 + 313078 * 2 ^ 59
def prefixEnd_313078 : Nat := 4983230072969 + 3 ^ 40 * 313078 * 2
def baseEnd_313078 : Nat := 142897330087494501853499

theorem tailTrace_313078 : CollatzResearch.WordTrace tailWord_313078 prefixEnd_313078 142897330087494501853499 := by
  unfold tailWord_313078
  simp only [CollatzResearch.WordTrace]
  refine ⟨713680797486209394411743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7612595173186233540391925 713680797486209394411743)
  ·
    refine ⟨1070521196229314091617615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713680797486209394411743 1070521196229314091617615)
    ·
      refine ⟨1605781794343971137426423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070521196229314091617615 1605781794343971137426423)
      ·
        refine ⟨2408672691515956706139635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605781794343971137426423 2408672691515956706139635)
        ·
          refine ⟨3613009037273935059209453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408672691515956706139635 3613009037273935059209453)
          ·
            refine ⟨1354878388977725647203545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3613009037273935059209453 1354878388977725647203545)
            ·
              refine ⟨1016158791733294235402659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354878388977725647203545 1016158791733294235402659)
              ·
                refine ⟨1524238187599941353103989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016158791733294235402659 1524238187599941353103989)
                ·
                  refine ⟨142897330087494501853499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524238187599941353103989 142897330087494501853499)
                  ·
                    rfl

theorem cell20_313078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_313078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313078 prefixEnd_313078 := by exact prefixLift 313078
  have htrace : WordTrace (prefixWord ++ tailWord_313078) baseStart_313078 baseEnd_313078 := by
    simpa [prefixWord, tailWord_313078, baseEnd_313078] using wordTrace_append hprefix tailTrace_313078
  have hstable : (prefixWord ++ tailWord_313078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313078).length < 2 ^ (prefixWord ++ tailWord_313078).sum := by decide
  have hdescent : baseEnd_313078 < baseStart_313078 := by decide
  rcases family_descends (prefixWord ++ tailWord_313078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313092 : List Nat := [2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_313092 : Nat := 118140960795 + 313092 * 2 ^ 59
def prefixEnd_313092 : Nat := 4983230072969 + 3 ^ 40 * 313092 * 2
def baseEnd_313092 : Nat := 47634573356324225128925

theorem tailTrace_313092 : CollatzResearch.WordTrace tailWord_313092 prefixEnd_313092 47634573356324225128925 := by
  unfold tailWord_313092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709701690864315350798765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7612935587819087134398353 5709701690864315350798765)
  ·
    refine ⟨2141138134074118256549537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5709701690864315350798765 2141138134074118256549537)
    ·
      refine ⟨1605853600555588692412153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2141138134074118256549537 1605853600555588692412153)
      ·
        refine ⟨1204390200416691519309115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605853600555588692412153 1204390200416691519309115)
        ·
          refine ⟨1806585300625037278963673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204390200416691519309115 1806585300625037278963673)
          ·
            refine ⟨1354938975468777959222755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806585300625037278963673 1354938975468777959222755)
            ·
              refine ⟨2032408463203166938834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354938975468777959222755 2032408463203166938834133)
              ·
                refine ⟨47634573356324225128925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2032408463203166938834133 47634573356324225128925)
                ·
                  rfl

theorem cell20_313092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_313092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313092 prefixEnd_313092 := by exact prefixLift 313092
  have htrace : WordTrace (prefixWord ++ tailWord_313092) baseStart_313092 baseEnd_313092 := by
    simpa [prefixWord, tailWord_313092, baseEnd_313092] using wordTrace_append hprefix tailTrace_313092
  have hstable : (prefixWord ++ tailWord_313092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313092).length < 2 ^ (prefixWord ++ tailWord_313092).sum := by decide
  have hdescent : baseEnd_313092 < baseStart_313092 := by decide
  rcases family_descends (prefixWord ++ tailWord_313092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313095 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_313095 : Nat := 118140960795 + 313095 * 2 ^ 59
def prefixEnd_313095 : Nat := 4983230072969 + 3 ^ 40 * 313095 * 2
def baseEnd_313095 : Nat := 142905089350717998286763

theorem tailTrace_313095 : CollatzResearch.WordTrace tailWord_313095 prefixEnd_313095 142905089350717998286763 := by
  unfold tailWord_313095
  simp only [CollatzResearch.WordTrace]
  refine ⟨11419512800717762213956739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7613008533811841475971159 11419512800717762213956739)
  ·
    refine ⟨17129269201076643320935109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11419512800717762213956739 17129269201076643320935109)
    ·
      refine ⟨3211737975201870622675333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17129269201076643320935109 3211737975201870622675333)
      ·
        refine ⟨602200870350350741751625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3211737975201870622675333 602200870350350741751625)
        ·
          refine ⟨451650652762763056313719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602200870350350741751625 451650652762763056313719)
          ·
            refine ⟨677475979144144584470579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451650652762763056313719 677475979144144584470579)
            ·
              refine ⟨1016213968716216876705869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677475979144144584470579 1016213968716216876705869)
              ·
                refine ⟨381080238268581328764701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016213968716216876705869 381080238268581328764701)
                ·
                  refine ⟨142905089350717998286763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381080238268581328764701 142905089350717998286763)
                  ·
                    rfl

theorem cell20_313095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_313095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313095 prefixEnd_313095 := by exact prefixLift 313095
  have htrace : WordTrace (prefixWord ++ tailWord_313095) baseStart_313095 baseEnd_313095 := by
    simpa [prefixWord, tailWord_313095, baseEnd_313095] using wordTrace_append hprefix tailTrace_313095
  have hstable : (prefixWord ++ tailWord_313095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313095).length < 2 ^ (prefixWord ++ tailWord_313095).sum := by decide
  have hdescent : baseEnd_313095 < baseStart_313095 := by decide
  rcases family_descends (prefixWord ++ tailWord_313095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313178 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_313178 : Nat := 118140960795 + 313178 * 2 ^ 59
def prefixEnd_313178 : Nat := 4983230072969 + 3 ^ 40 * 313178 * 2
def baseEnd_313178 : Nat := 142942972812338598519757

theorem tailTrace_313178 : CollatzResearch.WordTrace tailWord_313178 prefixEnd_313178 142942972812338598519757 := by
  unfold tailWord_313178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855635014854266847307047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7615026706278044926152125 2855635014854266847307047)
  ·
    refine ⟨4283452522281400270960571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2855635014854266847307047 4283452522281400270960571)
    ·
      refine ⟨6425178783422100406440857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283452522281400270960571 6425178783422100406440857)
      ·
        refine ⟨4818884087566575304830643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6425178783422100406440857 4818884087566575304830643)
        ·
          refine ⟨7228326131349862957245965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4818884087566575304830643 7228326131349862957245965)
          ·
            refine ⟨2710622299256198608967237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7228326131349862957245965 2710622299256198608967237)
            ·
              refine ⟨508241681110537239181357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2710622299256198608967237 508241681110537239181357)
              ·
                refine ⟨190590630416451464693009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508241681110537239181357 190590630416451464693009)
                ·
                  refine ⟨142942972812338598519757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190590630416451464693009 142942972812338598519757)
                  ·
                    rfl

theorem cell20_313178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_313178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313178 prefixEnd_313178 := by exact prefixLift 313178
  have htrace : WordTrace (prefixWord ++ tailWord_313178) baseStart_313178 baseEnd_313178 := by
    simpa [prefixWord, tailWord_313178, baseEnd_313178] using wordTrace_append hprefix tailTrace_313178
  have hstable : (prefixWord ++ tailWord_313178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313178).length < 2 ^ (prefixWord ++ tailWord_313178).sum := by decide
  have hdescent : baseEnd_313178 < baseStart_313178 := by decide
  rcases family_descends (prefixWord ++ tailWord_313178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313188 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_313188 : Nat := 118140960795 + 313188 * 2 ^ 59
def prefixEnd_313188 : Nat := 4983230072969 + 3 ^ 40 * 313188 * 2
def baseEnd_313188 : Nat := 142947537084823008186383

theorem tailTrace_313188 : CollatzResearch.WordTrace tailWord_313188 prefixEnd_313188 142947537084823008186383 := by
  unfold tailWord_313188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5711452394690419548546109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7615269859587226064728145 5711452394690419548546109)
  ·
    refine ⟨2141794648008907330704791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5711452394690419548546109 2141794648008907330704791)
    ·
      refine ⟨3212691972013360996057187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141794648008907330704791 3212691972013360996057187)
      ·
        refine ⟨4819037958020041494085781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212691972013360996057187 4819037958020041494085781)
        ·
          refine ⟨225892404282189445035271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4819037958020041494085781 225892404282189445035271)
          ·
            refine ⟨338838606423284167552907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225892404282189445035271 338838606423284167552907)
            ·
              refine ⟨508257909634926251329361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338838606423284167552907 508257909634926251329361)
              ·
                refine ⟨381193432226194688497021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508257909634926251329361 381193432226194688497021)
                ·
                  refine ⟨142947537084823008186383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381193432226194688497021 142947537084823008186383)
                  ·
                    rfl

theorem cell20_313188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_313188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313188 prefixEnd_313188 := by exact prefixLift 313188
  have htrace : WordTrace (prefixWord ++ tailWord_313188) baseStart_313188 baseEnd_313188 := by
    simpa [prefixWord, tailWord_313188, baseEnd_313188] using wordTrace_append hprefix tailTrace_313188
  have hstable : (prefixWord ++ tailWord_313188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313188).length < 2 ^ (prefixWord ++ tailWord_313188).sum := by decide
  have hdescent : baseEnd_313188 < baseStart_313188 := by decide
  rcases family_descends (prefixWord ++ tailWord_313188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313240 : List Nat := [2, 1, 2, 6, 2, 1, 6]
def baseStart_313240 : Nat := 118140960795 + 313240 * 2 ^ 59
def prefixEnd_313240 : Nat := 4983230072969 + 3 ^ 40 * 313240 * 2
def baseEnd_313240 : Nat := 15885696811304659828093

theorem tailTrace_313240 : CollatzResearch.WordTrace tailWord_313240 prefixEnd_313240 15885696811304659828093 := by
  unfold tailWord_313240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712400692596225988992587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7616534256794967985323449 5712400692596225988992587)
  ·
    refine ⟨8568601038894338983488881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5712400692596225988992587 8568601038894338983488881)
    ·
      refine ⟨6426450779170754237616661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8568601038894338983488881 6426450779170754237616661)
      ·
        refine ⟨301239880273629104888281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6426450779170754237616661 301239880273629104888281)
        ·
          refine ⟨225929910205221828666211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301239880273629104888281 225929910205221828666211)
          ·
            refine ⟨338894865307832742999317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225929910205221828666211 338894865307832742999317)
            ·
              refine ⟨15885696811304659828093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 338894865307832742999317 15885696811304659828093)
              ·
                rfl

theorem cell20_313240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 6].length) (baseStart_313240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313240 prefixEnd_313240 := by exact prefixLift 313240
  have htrace : WordTrace (prefixWord ++ tailWord_313240) baseStart_313240 baseEnd_313240 := by
    simpa [prefixWord, tailWord_313240, baseEnd_313240] using wordTrace_append hprefix tailTrace_313240
  have hstable : (prefixWord ++ tailWord_313240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313240).length < 2 ^ (prefixWord ++ tailWord_313240).sum := by decide
  have hdescent : baseEnd_313240 < baseStart_313240 := by decide
  rcases family_descends (prefixWord ++ tailWord_313240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313244 : List Nat := [2, 2, 3, 3, 1, 1, 8]
def baseStart_313244 : Nat := 118140960795 + 313244 * 2 ^ 59
def prefixEnd_313244 : Nat := 4983230072969 + 3 ^ 40 * 313244 * 2
def baseEnd_313244 : Nat := 15885899667859522479943

theorem tailTrace_313244 : CollatzResearch.WordTrace tailWord_313244 prefixEnd_313244 15885899667859522479943 := by
  unfold tailWord_313244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712473638588980330565393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7616631518118640440753857 5712473638588980330565393)
  ·
    refine ⟨4284355228941735247924045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5712473638588980330565393 4284355228941735247924045)
    ·
      refine ⟨1606633210853150717971517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4284355228941735247924045 1606633210853150717971517)
      ·
        refine ⟨602487454069931519239319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1606633210853150717971517 602487454069931519239319)
        ·
          refine ⟨903731181104897278858979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602487454069931519239319 903731181104897278858979)
          ·
            refine ⟨1355596771657345918288469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903731181104897278858979 1355596771657345918288469)
            ·
              refine ⟨15885899667859522479943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1355596771657345918288469 15885899667859522479943)
              ·
                rfl

theorem cell20_313244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_313244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313244 prefixEnd_313244 := by exact prefixLift 313244
  have htrace : WordTrace (prefixWord ++ tailWord_313244) baseStart_313244 baseEnd_313244 := by
    simpa [prefixWord, tailWord_313244, baseEnd_313244] using wordTrace_append hprefix tailTrace_313244
  have hstable : (prefixWord ++ tailWord_313244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313244).length < 2 ^ (prefixWord ++ tailWord_313244).sum := by decide
  have hdescent : baseEnd_313244 < baseStart_313244 := by decide
  rcases family_descends (prefixWord ++ tailWord_313244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313250 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_313250 : Nat := 118140960795 + 313250 * 2 ^ 59
def prefixEnd_313250 : Nat := 4983230072969 + 3 ^ 40 * 313250 * 2
def baseEnd_313250 : Nat := 142975835574226348119463

theorem tailTrace_313250 : CollatzResearch.WordTrace tailWord_313250 prefixEnd_313250 142975835574226348119463 := by
  unfold tailWord_313250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856291528789055921462301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7616777410104149123899469 2856291528789055921462301)
  ·
    refine ⟨1071109323295895970548363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2856291528789055921462301 1071109323295895970548363)
    ·
      refine ⟨1606663984943843955822545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071109323295895970548363 1606663984943843955822545)
      ·
        refine ⟨1204997988707882966866909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1606663984943843955822545 1204997988707882966866909)
        ·
          refine ⟨451874245765456112575091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1204997988707882966866909 451874245765456112575091)
          ·
            refine ⟨677811368648184168862637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451874245765456112575091 677811368648184168862637)
            ·
              refine ⟨254179263243069063323489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677811368648184168862637 254179263243069063323489)
              ·
                refine ⟨190634447432301797492617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254179263243069063323489 190634447432301797492617)
                ·
                  refine ⟨142975835574226348119463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190634447432301797492617 142975835574226348119463)
                  ·
                    rfl

theorem cell20_313250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_313250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313250 prefixEnd_313250 := by exact prefixLift 313250
  have htrace : WordTrace (prefixWord ++ tailWord_313250) baseStart_313250 baseEnd_313250 := by
    simpa [prefixWord, tailWord_313250, baseEnd_313250] using wordTrace_append hprefix tailTrace_313250
  have hstable : (prefixWord ++ tailWord_313250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313250).length < 2 ^ (prefixWord ++ tailWord_313250).sum := by decide
  have hdescent : baseEnd_313250 < baseStart_313250 := by decide
  rcases family_descends (prefixWord ++ tailWord_313250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313251 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_313251 : Nat := 118140960795 + 313251 * 2 ^ 59
def prefixEnd_313251 : Nat := 4983230072969 + 3 ^ 40 * 313251 * 2
def baseEnd_313251 : Nat := 142976292001474789086125

theorem tailTrace_313251 : CollatzResearch.WordTrace tailWord_313251 prefixEnd_313251 142976292001474789086125 := by
  unfold tailWord_313251
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425202588152600856635607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7616801725435067237757071 11425202588152600856635607)
  ·
    refine ⟨17137803882228901284953411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11425202588152600856635607 17137803882228901284953411)
    ·
      refine ⟨25706705823343351927430117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17137803882228901284953411 25706705823343351927430117)
      ·
        refine ⟨4820007341876878486393147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25706705823343351927430117 4820007341876878486393147)
        ·
          refine ⟨7230011012815317729589721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820007341876878486393147 7230011012815317729589721)
          ·
            refine ⟨5422508259611488297192291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230011012815317729589721 5422508259611488297192291)
            ·
              refine ⟨8133762389417232445788437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422508259611488297192291 8133762389417232445788437)
              ·
                refine ⟨381270112003932770896333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8133762389417232445788437 381270112003932770896333)
                ·
                  refine ⟨142976292001474789086125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381270112003932770896333 142976292001474789086125)
                  ·
                    rfl

theorem cell20_313251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_313251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313251 prefixEnd_313251 := by exact prefixLift 313251
  have htrace : WordTrace (prefixWord ++ tailWord_313251) baseStart_313251 baseEnd_313251 := by
    simpa [prefixWord, tailWord_313251, baseEnd_313251] using wordTrace_append hprefix tailTrace_313251
  have hstable : (prefixWord ++ tailWord_313251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313251).length < 2 ^ (prefixWord ++ tailWord_313251).sum := by decide
  have hdescent : baseEnd_313251 < baseStart_313251 := by decide
  rcases family_descends (prefixWord ++ tailWord_313251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313302 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_313302 : Nat := 118140960795 + 313302 * 2 ^ 59
def prefixEnd_313302 : Nat := 4983230072969 + 3 ^ 40 * 313302 * 2
def baseEnd_313302 : Nat := 142999569791145278385917

theorem tailTrace_313302 : CollatzResearch.WordTrace tailWord_313302 prefixEnd_313302 142999569791145278385917 := by
  unfold tailWord_313302
  simp only [CollatzResearch.WordTrace]
  refine ⟨714191419435489785421385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7618041807311891044494773 714191419435489785421385)
  ·
    refine ⟨535643564576617339066039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714191419435489785421385 535643564576617339066039)
    ·
      refine ⟨803465346864926008599059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535643564576617339066039 803465346864926008599059)
      ·
        refine ⟨1205198020297389012898589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803465346864926008599059 1205198020297389012898589)
        ·
          refine ⟨451949257611520879836971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1205198020297389012898589 451949257611520879836971)
          ·
            refine ⟨677923886417281319755457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451949257611520879836971 677923886417281319755457)
            ·
              refine ⟨508442914812960989816593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677923886417281319755457 508442914812960989816593)
              ·
                refine ⟨381332186109720742362445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508442914812960989816593 381332186109720742362445)
                ·
                  refine ⟨142999569791145278385917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381332186109720742362445 142999569791145278385917)
                  ·
                    rfl

theorem cell20_313302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_313302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313302 prefixEnd_313302 := by exact prefixLift 313302
  have htrace : WordTrace (prefixWord ++ tailWord_313302) baseStart_313302 baseEnd_313302 := by
    simpa [prefixWord, tailWord_313302, baseEnd_313302] using wordTrace_append hprefix tailTrace_313302
  have hstable : (prefixWord ++ tailWord_313302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313302).length < 2 ^ (prefixWord ++ tailWord_313302).sum := by decide
  have hdescent : baseEnd_313302 < baseStart_313302 := by decide
  rcases family_descends (prefixWord ++ tailWord_313302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313309 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 2]
def baseStart_313309 : Nat := 118140960795 + 313309 * 2 ^ 59
def prefixEnd_313309 : Nat := 4983230072969 + 3 ^ 40 * 313309 * 2
def baseEnd_313309 : Nat := 143002764781884365152555

theorem tailTrace_313309 : CollatzResearch.WordTrace tailWord_313309 prefixEnd_313309 143002764781884365152555 := by
  unfold tailWord_313309
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427318021942476762246981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7618212014628317841497987 11427318021942476762246981)
  ·
    refine ⟨2142622129114214392921309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11427318021942476762246981 2142622129114214392921309)
    ·
      refine ⟨803483298417830397345491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2142622129114214392921309 803483298417830397345491)
      ·
        refine ⟨1205224947626745596018237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803483298417830397345491 1205224947626745596018237)
        ·
          refine ⟨451959355360029598506839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1205224947626745596018237 451959355360029598506839)
          ·
            refine ⟨677939033040044397760259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451959355360029598506839 677939033040044397760259)
            ·
              refine ⟨1016908549560066596640389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677939033040044397760259 1016908549560066596640389)
              ·
                refine ⟨190670353042512486870073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1016908549560066596640389 190670353042512486870073)
                ·
                  refine ⟨143002764781884365152555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190670353042512486870073 143002764781884365152555)
                  ·
                    rfl

theorem cell20_313309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_313309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313309 prefixEnd_313309 := by exact prefixLift 313309
  have htrace : WordTrace (prefixWord ++ tailWord_313309) baseStart_313309 baseEnd_313309 := by
    simpa [prefixWord, tailWord_313309, baseEnd_313309] using wordTrace_append hprefix tailTrace_313309
  have hstable : (prefixWord ++ tailWord_313309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313309).length < 2 ^ (prefixWord ++ tailWord_313309).sum := by decide
  have hdescent : baseEnd_313309 < baseStart_313309 := by decide
  rcases family_descends (prefixWord ++ tailWord_313309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313327 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_313327 : Nat := 118140960795 + 313327 * 2 ^ 59
def prefixEnd_313327 : Nat := 4983230072969 + 3 ^ 40 * 313327 * 2
def baseEnd_313327 : Nat := 143010980472356302552481

theorem tailTrace_313327 : CollatzResearch.WordTrace tailWord_313327 prefixEnd_313327 143010980472356302552481 := by
  unfold tailWord_313327
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427974535877265836402235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7618649690584843890934823 11427974535877265836402235)
  ·
    refine ⟨17141961803815898754603353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11427974535877265836402235 17141961803815898754603353)
    ·
      refine ⟨12856471352861924065952515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17141961803815898754603353 12856471352861924065952515)
      ·
        refine ⟨19284707029292886098928773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12856471352861924065952515 19284707029292886098928773)
        ·
          refine ⟨3615882567992416143549145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19284707029292886098928773 3615882567992416143549145)
          ·
            refine ⟨2711911925994312107661859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615882567992416143549145 2711911925994312107661859)
            ·
              refine ⟨4067867888991468161492789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711911925994312107661859 4067867888991468161492789)
              ·
                refine ⟨381362614592950140139949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4067867888991468161492789 381362614592950140139949)
                ·
                  refine ⟨143010980472356302552481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381362614592950140139949 143010980472356302552481)
                  ·
                    rfl

theorem cell20_313327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_313327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313327 prefixEnd_313327 := by exact prefixLift 313327
  have htrace : WordTrace (prefixWord ++ tailWord_313327) baseStart_313327 baseEnd_313327 := by
    simpa [prefixWord, tailWord_313327, baseEnd_313327] using wordTrace_append hprefix tailTrace_313327
  have hstable : (prefixWord ++ tailWord_313327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313327).length < 2 ^ (prefixWord ++ tailWord_313327).sum := by decide
  have hdescent : baseEnd_313327 < baseStart_313327 := by decide
  rcases family_descends (prefixWord ++ tailWord_313327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313341 : List Nat := [1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_313341 : Nat := 118140960795 + 313341 * 2 ^ 59
def prefixEnd_313341 : Nat := 4983230072969 + 3 ^ 40 * 313341 * 2
def baseEnd_313341 : Nat := 47672456817944825361919

theorem tailTrace_313341 : CollatzResearch.WordTrace tailWord_313341 prefixEnd_313341 47672456817944825361919 := by
  unfold tailWord_313341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428485157826546227411877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7618990105217697484941251 11428485157826546227411877)
  ·
    refine ⟨2142840967092477417639727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11428485157826546227411877 2142840967092477417639727)
    ·
      refine ⟨3214261450638716126459591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142840967092477417639727 3214261450638716126459591)
      ·
        refine ⟨4821392175958074189689387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214261450638716126459591 4821392175958074189689387)
        ·
          refine ⟨7232088263937111284534081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821392175958074189689387 7232088263937111284534081)
          ·
            refine ⟨5424066197952833463400561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7232088263937111284534081 5424066197952833463400561)
            ·
              refine ⟨4068049648464625097550421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5424066197952833463400561 4068049648464625097550421)
              ·
                refine ⟨47672456817944825361919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4068049648464625097550421 47672456817944825361919)
                ·
                  rfl

theorem cell20_313341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_313341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313341 prefixEnd_313341 := by exact prefixLift 313341
  have htrace : WordTrace (prefixWord ++ tailWord_313341) baseStart_313341 baseEnd_313341 := by
    simpa [prefixWord, tailWord_313341, baseEnd_313341] using wordTrace_append hprefix tailTrace_313341
  have hstable : (prefixWord ++ tailWord_313341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313341).length < 2 ^ (prefixWord ++ tailWord_313341).sum := by decide
  have hdescent : baseEnd_313341 < baseStart_313341 := by decide
  rcases family_descends (prefixWord ++ tailWord_313341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313379 : List Nat := [1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_313379 : Nat := 118140960795 + 313379 * 2 ^ 59
def prefixEnd_313379 : Nat := 4983230072969 + 3 ^ 40 * 313379 * 2
def baseEnd_313379 : Nat := 47678238229758410939645

theorem tailTrace_313379 : CollatzResearch.WordTrace tailWord_313379 prefixEnd_313379 47678238229758410939645 := by
  unfold tailWord_313379
  simp only [CollatzResearch.WordTrace]
  refine ⟨11429871131688878717295191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7619914087792585811530127 11429871131688878717295191)
  ·
    refine ⟨17144806697533318075942787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11429871131688878717295191 17144806697533318075942787)
    ·
      refine ⟨25717210046299977113914181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17144806697533318075942787 25717210046299977113914181)
      ·
        refine ⟨4821976883681245708858909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25717210046299977113914181 4821976883681245708858909)
        ·
          refine ⟨1808241331380467140822091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4821976883681245708858909 1808241331380467140822091)
          ·
            refine ⟨2712361997070700711233137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808241331380467140822091 2712361997070700711233137)
            ·
              refine ⟨2034271497803025533424853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712361997070700711233137 2034271497803025533424853)
              ·
                refine ⟨47678238229758410939645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2034271497803025533424853 47678238229758410939645)
                ·
                  rfl

theorem cell20_313379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_313379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313379 prefixEnd_313379 := by exact prefixLift 313379
  have htrace : WordTrace (prefixWord ++ tailWord_313379) baseStart_313379 baseEnd_313379 := by
    simpa [prefixWord, tailWord_313379, baseEnd_313379] using wordTrace_append hprefix tailTrace_313379
  have hstable : (prefixWord ++ tailWord_313379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313379).length < 2 ^ (prefixWord ++ tailWord_313379).sum := by decide
  have hdescent : baseEnd_313379 < baseStart_313379 := by decide
  rcases family_descends (prefixWord ++ tailWord_313379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313430 : List Nat := [5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_313430 : Nat := 118140960795 + 313430 * 2 ^ 59
def prefixEnd_313430 : Nat := 4983230072969 + 3 ^ 40 * 313430 * 2
def baseEnd_313430 : Nat := 47685997492981907372909

theorem tailTrace_313430 : CollatzResearch.WordTrace tailWord_313430 prefixEnd_313430 47685997492981907372909 := by
  unfold tailWord_313430
  simp only [CollatzResearch.WordTrace]
  refine ⟨714483203406507151712609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7621154169669409618267829 714483203406507151712609)
  ·
    refine ⟨535862402554880363784457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714483203406507151712609 535862402554880363784457)
    ·
      refine ⟨401896801916160272838343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535862402554880363784457 401896801916160272838343)
      ·
        refine ⟨602845202874240409257515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401896801916160272838343 602845202874240409257515)
        ·
          refine ⟨904267804311360613886273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602845202874240409257515 904267804311360613886273)
          ·
            refine ⟨678200853233520460414705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904267804311360613886273 678200853233520460414705)
            ·
              refine ⟨508650639925140345311029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678200853233520460414705 508650639925140345311029)
              ·
                refine ⟨47685997492981907372909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508650639925140345311029 47685997492981907372909)
                ·
                  rfl

theorem cell20_313430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_313430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313430 prefixEnd_313430 := by exact prefixLift 313430
  have htrace : WordTrace (prefixWord ++ tailWord_313430) baseStart_313430 baseEnd_313430 := by
    simpa [prefixWord, tailWord_313430, baseEnd_313430] using wordTrace_append hprefix tailTrace_313430
  have hstable : (prefixWord ++ tailWord_313430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313430).length < 2 ^ (prefixWord ++ tailWord_313430).sum := by decide
  have hdescent : baseEnd_313430 < baseStart_313430 := by decide
  rcases family_descends (prefixWord ++ tailWord_313430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313437 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_313437 : Nat := 118140960795 + 313437 * 2 ^ 59
def prefixEnd_313437 : Nat := 4983230072969 + 3 ^ 40 * 313437 * 2
def baseEnd_313437 : Nat := 143061187469684808885365

theorem tailTrace_313437 : CollatzResearch.WordTrace tailWord_313437 prefixEnd_313437 143061187469684808885365 := by
  unfold tailWord_313437
  simp only [CollatzResearch.WordTrace]
  refine ⟨11431986565478754622906565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7621324376985836415271043 11431986565478754622906565)
  ·
    refine ⟨2143497481027266491794981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11431986565478754622906565 2143497481027266491794981)
    ·
      refine ⟨401905777692612467211559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2143497481027266491794981 401905777692612467211559)
      ·
        refine ⟨602858666538918700817339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401905777692612467211559 602858666538918700817339)
        ·
          refine ⟨904287999808378051226009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602858666538918700817339 904287999808378051226009)
          ·
            refine ⟨678215999856283538419507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904287999808378051226009 678215999856283538419507)
            ·
              refine ⟨1017323999784425307629261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678215999856283538419507 1017323999784425307629261)
              ·
                refine ⟨381496499919159490360973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017323999784425307629261 381496499919159490360973)
                ·
                  refine ⟨143061187469684808885365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381496499919159490360973 143061187469684808885365)
                  ·
                    rfl

theorem cell20_313437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_313437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313437 prefixEnd_313437 := by exact prefixLift 313437
  have htrace : WordTrace (prefixWord ++ tailWord_313437) baseStart_313437 baseEnd_313437 := by
    simpa [prefixWord, tailWord_313437, baseEnd_313437] using wordTrace_append hprefix tailTrace_313437
  have hstable : (prefixWord ++ tailWord_313437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313437).length < 2 ^ (prefixWord ++ tailWord_313437).sum := by decide
  have hdescent : baseEnd_313437 < baseStart_313437 := by decide
  rcases family_descends (prefixWord ++ tailWord_313437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313455 : List Nat := [1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_313455 : Nat := 118140960795 + 313455 * 2 ^ 59
def prefixEnd_313455 : Nat := 4983230072969 + 3 ^ 40 * 313455 * 2
def baseEnd_313455 : Nat := 47689801053385582095097

theorem tailTrace_313455 : CollatzResearch.WordTrace tailWord_313455 prefixEnd_313455 47689801053385582095097 := by
  unfold tailWord_313455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11432643079413543697061819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7621762052942362464707879 11432643079413543697061819)
  ·
    refine ⟨17148964619120315545592729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11432643079413543697061819 17148964619120315545592729)
    ·
      refine ⟨12861723464340236659194547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17148964619120315545592729 12861723464340236659194547)
      ·
        refine ⟨19292585196510354988791821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12861723464340236659194547 19292585196510354988791821)
        ·
          refine ⟨7234719448691383120796933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19292585196510354988791821 7234719448691383120796933)
          ·
            refine ⟨1356509896629634335149425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7234719448691383120796933 1356509896629634335149425)
            ·
              refine ⟨1017382422472225751362069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356509896629634335149425 1017382422472225751362069)
              ·
                refine ⟨47689801053385582095097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1017382422472225751362069 47689801053385582095097)
                ·
                  rfl

theorem cell20_313455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_313455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313455 prefixEnd_313455 := by exact prefixLift 313455
  have htrace : WordTrace (prefixWord ++ tailWord_313455) baseStart_313455 baseEnd_313455 := by
    simpa [prefixWord, tailWord_313455, baseEnd_313455] using wordTrace_append hprefix tailTrace_313455
  have hstable : (prefixWord ++ tailWord_313455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313455).length < 2 ^ (prefixWord ++ tailWord_313455).sum := by decide
  have hdescent : baseEnd_313455 < baseStart_313455 := by decide
  rcases family_descends (prefixWord ++ tailWord_313455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313479 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_313479 : Nat := 118140960795 + 313479 * 2 ^ 59
def prefixEnd_313479 : Nat := 4983230072969 + 3 ^ 40 * 313479 * 2
def baseEnd_313479 : Nat := 143080357414119329485193

theorem tailTrace_313479 : CollatzResearch.WordTrace tailWord_313479 prefixEnd_313479 143080357414119329485193 := by
  unfold tailWord_313479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433518431326595795935491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7622345620884397197290327 11433518431326595795935491)
  ·
    refine ⟨17150277646989893693903237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11433518431326595795935491 17150277646989893693903237)
    ·
      refine ⟨3215677058810605067606857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17150277646989893693903237 3215677058810605067606857)
      ·
        refine ⟨2411757794107953800705143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3215677058810605067606857 2411757794107953800705143)
        ·
          refine ⟨3617636691161930701057715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411757794107953800705143 3617636691161930701057715)
          ·
            refine ⟨5426455036742896051586573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617636691161930701057715 5426455036742896051586573)
            ·
              refine ⟨2034920638778586019344965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5426455036742896051586573 2034920638778586019344965)
              ·
                refine ⟨381547619770984878627181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034920638778586019344965 381547619770984878627181)
                ·
                  refine ⟨143080357414119329485193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381547619770984878627181 143080357414119329485193)
                  ·
                    rfl

theorem cell20_313479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_313479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313479 prefixEnd_313479 := by exact prefixLift 313479
  have htrace : WordTrace (prefixWord ++ tailWord_313479) baseStart_313479 baseEnd_313479 := by
    simpa [prefixWord, tailWord_313479, baseEnd_313479] using wordTrace_append hprefix tailTrace_313479
  have hstable : (prefixWord ++ tailWord_313479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313479).length < 2 ^ (prefixWord ++ tailWord_313479).sum := by decide
  have hdescent : baseEnd_313479 < baseStart_313479 := by decide
  rcases family_descends (prefixWord ++ tailWord_313479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313482 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_313482 : Nat := 118140960795 + 313482 * 2 ^ 59
def prefixEnd_313482 : Nat := 4983230072969 + 3 ^ 40 * 313482 * 2
def baseEnd_313482 : Nat := 143081726695864652385181

theorem tailTrace_313482 : CollatzResearch.WordTrace tailWord_313482 prefixEnd_313482 143081726695864652385181 := by
  unfold tailWord_313482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858406962578931827073675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7622418566877151538863133 2858406962578931827073675)
  ·
    refine ⟨4287610443868397740610513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2858406962578931827073675 4287610443868397740610513)
    ·
      refine ⟨3215707832901298305457885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4287610443868397740610513 3215707832901298305457885)
      ·
        refine ⟨1205890437337986864546707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3215707832901298305457885 1205890437337986864546707)
        ·
          refine ⟨1808835656006980296820061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205890437337986864546707 1808835656006980296820061)
          ·
            refine ⟨678313371002617611307523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1808835656006980296820061 678313371002617611307523)
            ·
              refine ⟨1017470056503926416961285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678313371002617611307523 1017470056503926416961285)
              ·
                refine ⟨190775635594486203180241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1017470056503926416961285 190775635594486203180241)
                ·
                  refine ⟨143081726695864652385181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190775635594486203180241 143081726695864652385181)
                  ·
                    rfl

theorem cell20_313482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_313482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313482 prefixEnd_313482 := by exact prefixLift 313482
  have htrace : WordTrace (prefixWord ++ tailWord_313482) baseStart_313482 baseEnd_313482 := by
    simpa [prefixWord, tailWord_313482, baseEnd_313482] using wordTrace_append hprefix tailTrace_313482
  have hstable : (prefixWord ++ tailWord_313482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313482).length < 2 ^ (prefixWord ++ tailWord_313482).sum := by decide
  have hdescent : baseEnd_313482 < baseStart_313482 := by decide
  rcases family_descends (prefixWord ++ tailWord_313482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313503 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_313503 : Nat := 118140960795 + 313503 * 2 ^ 59
def prefixEnd_313503 : Nat := 4983230072969 + 3 ^ 40 * 313503 * 2
def baseEnd_313503 : Nat := 143091311668081912685095

theorem tailTrace_313503 : CollatzResearch.WordTrace tailWord_313503 prefixEnd_313503 143091311668081912685095 := by
  unfold tailWord_313503
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434393783239647894809163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7622929188826431929872775 11434393783239647894809163)
  ·
    refine ⟨17151590674859471842213745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11434393783239647894809163 17151590674859471842213745)
    ·
      refine ⟨12863693006144603881660309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17151590674859471842213745 12863693006144603881660309)
      ·
        refine ⟨602985609663028306952827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12863693006144603881660309 602985609663028306952827)
        ·
          refine ⟨904478414494542460429241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602985609663028306952827 904478414494542460429241)
          ·
            refine ⟨678358810870906845321931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904478414494542460429241 678358810870906845321931)
            ·
              refine ⟨1017538216306360267982897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678358810870906845321931 1017538216306360267982897)
              ·
                refine ⟨763153662229770200987173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017538216306360267982897 763153662229770200987173)
                ·
                  refine ⟨143091311668081912685095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763153662229770200987173 143091311668081912685095)
                  ·
                    rfl

theorem cell20_313503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_313503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313503 prefixEnd_313503 := by exact prefixLift 313503
  have htrace : WordTrace (prefixWord ++ tailWord_313503) baseStart_313503 baseEnd_313503 := by
    simpa [prefixWord, tailWord_313503, baseEnd_313503] using wordTrace_append hprefix tailTrace_313503
  have hstable : (prefixWord ++ tailWord_313503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313503).length < 2 ^ (prefixWord ++ tailWord_313503).sum := by decide
  have hdescent : baseEnd_313503 < baseStart_313503 := by decide
  rcases family_descends (prefixWord ++ tailWord_313503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313534 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_313534 : Nat := 118140960795 + 313534 * 2 ^ 59
def prefixEnd_313534 : Nat := 4983230072969 + 3 ^ 40 * 313534 * 2
def baseEnd_313534 : Nat := 143105460912783582651635

theorem tailTrace_313534 : CollatzResearch.WordTrace tailWord_313534 prefixEnd_313534 143105460912783582651635 := by
  unfold tailWord_313534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429440555765917523648457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7623682964084893459458437 1429440555765917523648457)
  ·
    refine ⟨1072080416824438142736343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1429440555765917523648457 1072080416824438142736343)
    ·
      refine ⟨1608120625236657214104515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072080416824438142736343 1608120625236657214104515)
      ·
        refine ⟨2412180937854985821156773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608120625236657214104515 2412180937854985821156773)
        ·
          refine ⟨452283925847809841466895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2412180937854985821156773 452283925847809841466895)
          ·
            refine ⟨678425888771714762200343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452283925847809841466895 678425888771714762200343)
            ·
              refine ⟨1017638833157572143300515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678425888771714762200343 1017638833157572143300515)
              ·
                refine ⟨1526458249736358214950773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017638833157572143300515 1526458249736358214950773)
                ·
                  refine ⟨143105460912783582651635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1526458249736358214950773 143105460912783582651635)
                  ·
                    rfl

theorem cell20_313534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_313534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313534 prefixEnd_313534 := by exact prefixLift 313534
  have htrace : WordTrace (prefixWord ++ tailWord_313534) baseStart_313534 baseEnd_313534 := by
    simpa [prefixWord, tailWord_313534, baseEnd_313534] using wordTrace_append hprefix tailTrace_313534
  have hstable : (prefixWord ++ tailWord_313534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313534).length < 2 ^ (prefixWord ++ tailWord_313534).sum := by decide
  have hdescent : baseEnd_313534 < baseStart_313534 := by decide
  rcases family_descends (prefixWord ++ tailWord_313534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313541 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 2]
def baseStart_313541 : Nat := 118140960795 + 313541 * 2 ^ 59
def prefixEnd_313541 : Nat := 4983230072969 + 3 ^ 40 * 313541 * 2
def baseEnd_313541 : Nat := 143108655903522669418273

theorem tailTrace_313541 : CollatzResearch.WordTrace tailWord_313541 prefixEnd_313541 143108655903522669418273 := by
  unfold tailWord_313541
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435779757101980384692477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7623853171401320256461651 11435779757101980384692477)
  ·
    refine ⟨4288417408913242644259679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11435779757101980384692477 4288417408913242644259679)
    ·
      refine ⟨6432626113369863966389519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4288417408913242644259679 6432626113369863966389519)
      ·
        refine ⟨9648939170054795949584279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6432626113369863966389519 9648939170054795949584279)
        ·
          refine ⟨14473408755082193924376419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648939170054795949584279 14473408755082193924376419)
          ·
            refine ⟨21710113132623290886564629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14473408755082193924376419 21710113132623290886564629)
            ·
              refine ⟨1017661553091716760307717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21710113132623290886564629 1017661553091716760307717)
              ·
                refine ⟨190811541204696892557697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1017661553091716760307717 190811541204696892557697)
                ·
                  refine ⟨143108655903522669418273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190811541204696892557697 143108655903522669418273)
                  ·
                    rfl

theorem cell20_313541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_313541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313541 prefixEnd_313541 := by exact prefixLift 313541
  have htrace : WordTrace (prefixWord ++ tailWord_313541) baseStart_313541 baseEnd_313541 := by
    simpa [prefixWord, tailWord_313541, baseEnd_313541] using wordTrace_append hprefix tailTrace_313541
  have hstable : (prefixWord ++ tailWord_313541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313541).length < 2 ^ (prefixWord ++ tailWord_313541).sum := by decide
  have hdescent : baseEnd_313541 < baseStart_313541 := by decide
  rcases family_descends (prefixWord ++ tailWord_313541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313558 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_313558 : Nat := 118140960795 + 313558 * 2 ^ 59
def prefixEnd_313558 : Nat := 4983230072969 + 3 ^ 40 * 313558 * 2
def baseEnd_313558 : Nat := 143116415166746165851537

theorem tailTrace_313558 : CollatzResearch.WordTrace tailWord_313558 prefixEnd_313558 143116415166746165851537 := by
  unfold tailWord_313558
  simp only [CollatzResearch.WordTrace]
  refine ⟨714774987377524518003833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7624266532026928192040885 714774987377524518003833)
  ·
    refine ⟨536081240533143388502875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714774987377524518003833 536081240533143388502875)
    ·
      refine ⟨804121860799715082754313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536081240533143388502875 804121860799715082754313)
      ·
        refine ⟨603091395599786312065735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804121860799715082754313 603091395599786312065735)
        ·
          refine ⟨904637093399679468098603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603091395599786312065735 904637093399679468098603)
          ·
            refine ⟨1356955640099519202147905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904637093399679468098603 1356955640099519202147905)
            ·
              refine ⟨1017716730074639401610929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356955640099519202147905 1017716730074639401610929)
              ·
                refine ⟨763287547555979551208197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017716730074639401610929 763287547555979551208197)
                ·
                  refine ⟨143116415166746165851537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763287547555979551208197 143116415166746165851537)
                  ·
                    rfl

theorem cell20_313558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_313558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313558 prefixEnd_313558 := by exact prefixLift 313558
  have htrace : WordTrace (prefixWord ++ tailWord_313558) baseStart_313558 baseEnd_313558 := by
    simpa [prefixWord, tailWord_313558, baseEnd_313558] using wordTrace_append hprefix tailTrace_313558
  have hstable : (prefixWord ++ tailWord_313558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313558).length < 2 ^ (prefixWord ++ tailWord_313558).sum := by decide
  have hdescent : baseEnd_313558 < baseStart_313558 := by decide
  rcases family_descends (prefixWord ++ tailWord_313558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313562 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_313562 : Nat := 118140960795 + 313562 * 2 ^ 59
def prefixEnd_313562 : Nat := 4983230072969 + 3 ^ 40 * 313562 * 2
def baseEnd_313562 : Nat := 143118240875739929718187

theorem tailTrace_313562 : CollatzResearch.WordTrace tailWord_313562 prefixEnd_313562 143118240875739929718187 := by
  unfold tailWord_313562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859136422506475242801735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7624363793350600647471293 2859136422506475242801735)
  ·
    refine ⟨4288704633759712864202603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859136422506475242801735 4288704633759712864202603)
    ·
      refine ⟨6433056950639569296303905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4288704633759712864202603 6433056950639569296303905)
      ·
        refine ⟨4824792712979676972227929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6433056950639569296303905 4824792712979676972227929)
        ·
          refine ⟨3618594534734757729170947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4824792712979676972227929 3618594534734757729170947)
          ·
            refine ⟨5427891802102136593756421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618594534734757729170947 5427891802102136593756421)
            ·
              refine ⟨1017729712894150611329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5427891802102136593756421 1017729712894150611329329)
              ·
                refine ⟨763297284670612958496997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017729712894150611329329 763297284670612958496997)
                ·
                  refine ⟨143118240875739929718187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763297284670612958496997 143118240875739929718187)
                  ·
                    rfl

theorem cell20_313562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_313562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313562 prefixEnd_313562 := by exact prefixLift 313562
  have htrace : WordTrace (prefixWord ++ tailWord_313562) baseStart_313562 baseEnd_313562 := by
    simpa [prefixWord, tailWord_313562, baseEnd_313562] using wordTrace_append hprefix tailTrace_313562
  have hstable : (prefixWord ++ tailWord_313562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313562).length < 2 ^ (prefixWord ++ tailWord_313562).sum := by decide
  have hdescent : baseEnd_313562 < baseStart_313562 := by decide
  rcases family_descends (prefixWord ++ tailWord_313562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313565 : List Nat := [1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_313565 : Nat := 118140960795 + 313565 * 2 ^ 59
def prefixEnd_313565 : Nat := 4983230072969 + 3 ^ 40 * 313565 * 2
def baseEnd_313565 : Nat := 47706536719161750872725

theorem tailTrace_313565 : CollatzResearch.WordTrace tailWord_313565 prefixEnd_313565 47706536719161750872725 := by
  unfold tailWord_313565
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436655109015032483566149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7624436739343354989044099 11436655109015032483566149)
  ·
    refine ⟨2144372832940318590668653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11436655109015032483566149 2144372832940318590668653)
    ·
      refine ⟨804139812352619471500745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2144372832940318590668653 804139812352619471500745)
      ·
        refine ⟨603104859264464603625559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804139812352619471500745 603104859264464603625559)
        ·
          refine ⟨904657288896696905438339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603104859264464603625559 904657288896696905438339)
          ·
            refine ⟨1356985933345045358157509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904657288896696905438339 1356985933345045358157509)
            ·
              refine ⟨254434862502196004654533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1356985933345045358157509 254434862502196004654533)
              ·
                refine ⟨47706536719161750872725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254434862502196004654533 47706536719161750872725)
                ·
                  rfl

theorem cell20_313565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_313565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313565 prefixEnd_313565 := by exact prefixLift 313565
  have htrace : WordTrace (prefixWord ++ tailWord_313565) baseStart_313565 baseEnd_313565 := by
    simpa [prefixWord, tailWord_313565, baseEnd_313565] using wordTrace_append hprefix tailTrace_313565
  have hstable : (prefixWord ++ tailWord_313565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313565).length < 2 ^ (prefixWord ++ tailWord_313565).sum := by decide
  have hdescent : baseEnd_313565 < baseStart_313565 := by decide
  rcases family_descends (prefixWord ++ tailWord_313565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313569 : List Nat := [1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_313569 : Nat := 118140960795 + 313569 * 2 ^ 59
def prefixEnd_313569 : Nat := 4983230072969 + 3 ^ 40 * 313569 * 2
def baseEnd_313569 : Nat := 47707145288826338828275

theorem tailTrace_313569 : CollatzResearch.WordTrace tailWord_313569 prefixEnd_313569 47707145288826338828275 := by
  unfold tailWord_313569
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436801001000541166711761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7624534000667027444474507 11436801001000541166711761)
  ·
    refine ⟨8577600750750405875033821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11436801001000541166711761 8577600750750405875033821)
    ·
      refine ⟨3216600281531402203137683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8577600750750405875033821 3216600281531402203137683)
      ·
        refine ⟨4824900422297103304706525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3216600281531402203137683 4824900422297103304706525)
        ·
          refine ⟨1809337658361413739264947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4824900422297103304706525 1809337658361413739264947)
          ·
            refine ⟨2714006487542120608897421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809337658361413739264947 2714006487542120608897421)
            ·
              refine ⟨1017752432828295228336533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2714006487542120608897421 1017752432828295228336533)
              ·
                refine ⟨47707145288826338828275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1017752432828295228336533 47707145288826338828275)
                ·
                  rfl

theorem cell20_313569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_313569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313569 prefixEnd_313569 := by exact prefixLift 313569
  have htrace : WordTrace (prefixWord ++ tailWord_313569) baseStart_313569 baseEnd_313569 := by
    simpa [prefixWord, tailWord_313569, baseEnd_313569] using wordTrace_append hprefix tailTrace_313569
  have hstable : (prefixWord ++ tailWord_313569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313569).length < 2 ^ (prefixWord ++ tailWord_313569).sum := by decide
  have hdescent : baseEnd_313569 < baseStart_313569 := by decide
  rcases family_descends (prefixWord ++ tailWord_313569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313575 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 2]
def baseStart_313575 : Nat := 118140960795 + 313575 * 2 ^ 59
def prefixEnd_313575 : Nat := 4983230072969 + 3 ^ 40 * 313575 * 2
def baseEnd_313575 : Nat := 143124174429969662284801

theorem tailTrace_313575 : CollatzResearch.WordTrace tailWord_313575 prefixEnd_313575 143124174429969662284801 := by
  unfold tailWord_313575
  simp only [CollatzResearch.WordTrace]
  refine ⟨11437019838978804191430179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7624679892652536127620119 11437019838978804191430179)
  ·
    refine ⟨17155529758468206287145269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11437019838978804191430179 17155529758468206287145269)
    ·
      refine ⟨1608330914856394339419869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17155529758468206287145269 1608330914856394339419869)
      ·
        refine ⟨603124093071147877282451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1608330914856394339419869 603124093071147877282451)
        ·
          refine ⟨904686139606721815923677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603124093071147877282451 904686139606721815923677)
          ·
            refine ⟨339257302352520680971379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 904686139606721815923677 339257302352520680971379)
            ·
              refine ⟨508885953528781021457069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339257302352520680971379 508885953528781021457069)
              ·
                refine ⟨190832232573292883046401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508885953528781021457069 190832232573292883046401)
                ·
                  refine ⟨143124174429969662284801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190832232573292883046401 143124174429969662284801)
                  ·
                    rfl

theorem cell20_313575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2].length) (baseStart_313575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313575 prefixEnd_313575 := by exact prefixLift 313575
  have htrace : WordTrace (prefixWord ++ tailWord_313575) baseStart_313575 baseEnd_313575 := by
    simpa [prefixWord, tailWord_313575, baseEnd_313575] using wordTrace_append hprefix tailTrace_313575
  have hstable : (prefixWord ++ tailWord_313575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313575).length < 2 ^ (prefixWord ++ tailWord_313575).sum := by decide
  have hdescent : baseEnd_313575 < baseStart_313575 := by decide
  rcases family_descends (prefixWord ++ tailWord_313575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313586 : List Nat := [3, 2, 1, 3, 2, 3, 6]
def baseStart_313586 : Nat := 118140960795 + 313586 * 2 ^ 59
def prefixEnd_313586 : Nat := 4983230072969 + 3 ^ 40 * 313586 * 2
def baseEnd_313586 : Nat := 15903243903300279213121

theorem tailTrace_313586 : CollatzResearch.WordTrace tailWord_313586 prefixEnd_313586 15903243903300279213121 := by
  unfold tailWord_313586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859355260484738267520153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7624947361292635380053741 2859355260484738267520153)
  ·
    refine ⟨2144516445363553700640115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2859355260484738267520153 2144516445363553700640115)
    ·
      refine ⟨3216774668045330550960173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144516445363553700640115 3216774668045330550960173)
      ·
        refine ⟨1206290500516998956610065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3216774668045330550960173 1206290500516998956610065)
        ·
          refine ⟨904717875387749217457549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1206290500516998956610065 904717875387749217457549)
          ·
            refine ⟨339269203270405956546581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 904717875387749217457549 339269203270405956546581)
            ·
              refine ⟨15903243903300279213121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 339269203270405956546581 15903243903300279213121)
              ·
                rfl

theorem cell20_313586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_313586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313586 prefixEnd_313586 := by exact prefixLift 313586
  have htrace : WordTrace (prefixWord ++ tailWord_313586) baseStart_313586 baseEnd_313586 := by
    simpa [prefixWord, tailWord_313586, baseEnd_313586] using wordTrace_append hprefix tailTrace_313586
  have hstable : (prefixWord ++ tailWord_313586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313586).length < 2 ^ (prefixWord ++ tailWord_313586).sum := by decide
  have hdescent : baseEnd_313586 < baseStart_313586 := by decide
  rcases family_descends (prefixWord ++ tailWord_313586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313600 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_313600 : Nat := 118140960795 + 313600 * 2 ^ 59
def prefixEnd_313600 : Nat := 4983230072969 + 3 ^ 40 * 313600 * 2
def baseEnd_313600 : Nat := 143135585111180686451365

theorem tailTrace_313600 : CollatzResearch.WordTrace tailWord_313600 prefixEnd_313600 143135585111180686451365 := by
  unfold tailWord_313600
  simp only [CollatzResearch.WordTrace]
  refine ⟨5718965831944116730545127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7625287775925488974060169 5718965831944116730545127)
  ·
    refine ⟨8578448747916175095817691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5718965831944116730545127 8578448747916175095817691)
    ·
      refine ⟨12867673121874262643726537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578448747916175095817691 12867673121874262643726537)
      ·
        refine ⟨9650754841405696982794903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12867673121874262643726537 9650754841405696982794903)
        ·
          refine ⟨14476132262108545474192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9650754841405696982794903 14476132262108545474192355)
          ·
            refine ⟨21714198393162818211288533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14476132262108545474192355 21714198393162818211288533)
            ·
              refine ⟨508926524839753551827075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21714198393162818211288533 508926524839753551827075)
              ·
                refine ⟨763389787259630327740613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508926524839753551827075 763389787259630327740613)
                ·
                  refine ⟨143135585111180686451365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763389787259630327740613 143135585111180686451365)
                  ·
                    rfl

theorem cell20_313600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_313600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313600 prefixEnd_313600 := by exact prefixLift 313600
  have htrace : WordTrace (prefixWord ++ tailWord_313600) baseStart_313600 baseEnd_313600 := by
    simpa [prefixWord, tailWord_313600, baseEnd_313600] using wordTrace_append hprefix tailTrace_313600
  have hstable : (prefixWord ++ tailWord_313600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313600).length < 2 ^ (prefixWord ++ tailWord_313600).sum := by decide
  have hdescent : baseEnd_313600 < baseStart_313600 := by decide
  rcases family_descends (prefixWord ++ tailWord_313600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313610 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_313610 : Nat := 118140960795 + 313610 * 2 ^ 59
def prefixEnd_313610 : Nat := 4983230072969 + 3 ^ 40 * 313610 * 2
def baseEnd_313610 : Nat := 143140149383665096117991

theorem tailTrace_313610 : CollatzResearch.WordTrace tailWord_313610 prefixEnd_313610 143140149383665096117991 := by
  unfold tailWord_313610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859574098463001292238571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7625530929234670112636189 2859574098463001292238571)
  ·
    refine ⟨4289361147694501938357857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859574098463001292238571 4289361147694501938357857)
    ·
      refine ⟨3217020860770876453768393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4289361147694501938357857 3217020860770876453768393)
      ·
        refine ⟨2412765645578157340326295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217020860770876453768393 2412765645578157340326295)
        ·
          refine ⟨3619148468367236010489443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412765645578157340326295 3619148468367236010489443)
          ·
            refine ⟨5428722702550854015734165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619148468367236010489443 5428722702550854015734165)
            ·
              refine ⟨254471376682071281987539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5428722702550854015734165 254471376682071281987539)
              ·
                refine ⟨381707065023106922981309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254471376682071281987539 381707065023106922981309)
                ·
                  refine ⟨143140149383665096117991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381707065023106922981309 143140149383665096117991)
                  ·
                    rfl

theorem cell20_313610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_313610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313610 prefixEnd_313610 := by exact prefixLift 313610
  have htrace : WordTrace (prefixWord ++ tailWord_313610) baseStart_313610 baseEnd_313610 := by
    simpa [prefixWord, tailWord_313610, baseEnd_313610] using wordTrace_append hprefix tailTrace_313610
  have hstable : (prefixWord ++ tailWord_313610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313610).length < 2 ^ (prefixWord ++ tailWord_313610).sum := by decide
  have hdescent : baseEnd_313610 < baseStart_313610 := by decide
  rcases family_descends (prefixWord ++ tailWord_313610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313662 : List Nat := [4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_313662 : Nat := 118140960795 + 313662 * 2 ^ 59
def prefixEnd_313662 : Nat := 4983230072969 + 3 ^ 40 * 313662 * 2
def baseEnd_313662 : Nat := 47721294533528008794815

theorem tailTrace_313662 : CollatzResearch.WordTrace tailWord_313662 prefixEnd_313662 47721294533528008794815 := by
  unfold tailWord_313662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430024123707952256230905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7626795326442412033231493 1430024123707952256230905)
  ·
    refine ⟨1072518092780964192173179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1430024123707952256230905 1072518092780964192173179)
    ·
      refine ⟨1608777139171446288259769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072518092780964192173179 1608777139171446288259769)
      ·
        refine ⟨1206582854378584716194827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1608777139171446288259769 1206582854378584716194827)
        ·
          refine ⟨1809874281567877074292241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206582854378584716194827 1809874281567877074292241)
          ·
            refine ⟨1357405711175907805719181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809874281567877074292241 1357405711175907805719181)
            ·
              refine ⟨509027141690965427144693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1357405711175907805719181 509027141690965427144693)
              ·
                refine ⟨47721294533528008794815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509027141690965427144693 47721294533528008794815)
                ·
                  rfl

theorem cell20_313662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_313662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313662 prefixEnd_313662 := by exact prefixLift 313662
  have htrace : WordTrace (prefixWord ++ tailWord_313662) baseStart_313662 baseEnd_313662 := by
    simpa [prefixWord, tailWord_313662, baseEnd_313662] using wordTrace_append hprefix tailTrace_313662
  have hstable : (prefixWord ++ tailWord_313662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313662).length < 2 ^ (prefixWord ++ tailWord_313662).sum := by decide
  have hdescent : baseEnd_313662 < baseStart_313662 := by decide
  rcases family_descends (prefixWord ++ tailWord_313662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313676 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_313676 : Nat := 118140960795 + 313676 * 2 ^ 59
def prefixEnd_313676 : Nat := 4983230072969 + 3 ^ 40 * 313676 * 2
def baseEnd_313676 : Nat := 143170273582062199917721

theorem tailTrace_313676 : CollatzResearch.WordTrace tailWord_313676 prefixEnd_313676 143170273582062199917721 := by
  unfold tailWord_313676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720351805806449220428441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7627135741075265627237921 5720351805806449220428441)
  ·
    refine ⟨4290263854354836915321331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5720351805806449220428441 4290263854354836915321331)
    ·
      refine ⟨6435395781532255372981997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4290263854354836915321331 6435395781532255372981997)
      ·
        refine ⟨2413273418074595764868249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6435395781532255372981997 2413273418074595764868249)
        ·
          refine ⟨1809955063555946823651187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413273418074595764868249 1809955063555946823651187)
          ·
            refine ⟨2714932595333920235476781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809955063555946823651187 2714932595333920235476781)
            ·
              refine ⟨1018099723250220088303793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2714932595333920235476781 1018099723250220088303793)
              ·
                refine ⟨763574792437665066227845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018099723250220088303793 763574792437665066227845)
                ·
                  refine ⟨143170273582062199917721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763574792437665066227845 143170273582062199917721)
                  ·
                    rfl

theorem cell20_313676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_313676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313676 prefixEnd_313676 := by exact prefixLift 313676
  have htrace : WordTrace (prefixWord ++ tailWord_313676) baseStart_313676 baseEnd_313676 := by
    simpa [prefixWord, tailWord_313676, baseEnd_313676] using wordTrace_append hprefix tailTrace_313676
  have hstable : (prefixWord ++ tailWord_313676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313676).length < 2 ^ (prefixWord ++ tailWord_313676).sum := by decide
  have hdescent : baseEnd_313676 < baseStart_313676 := by decide
  rcases family_descends (prefixWord ++ tailWord_313676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313690 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_313690 : Nat := 118140960795 + 313690 * 2 ^ 59
def prefixEnd_313690 : Nat := 4983230072969 + 3 ^ 40 * 313690 * 2
def baseEnd_313690 : Nat := 143176663563540373450997

theorem tailTrace_313690 : CollatzResearch.WordTrace tailWord_313690 prefixEnd_313690 143176663563540373450997 := by
  unfold tailWord_313690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860303558390544707966631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7627476155708119221244349 2860303558390544707966631)
  ·
    refine ⟨4290455337585817061949947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860303558390544707966631 4290455337585817061949947)
    ·
      refine ⟨6435683006378725592924921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4290455337585817061949947 6435683006378725592924921)
      ·
        refine ⟨4826762254784044194693691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6435683006378725592924921 4826762254784044194693691)
        ·
          refine ⟨7240143382176066292040537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826762254784044194693691 7240143382176066292040537)
          ·
            refine ⟨5430107536632049719030403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240143382176066292040537 5430107536632049719030403)
            ·
              refine ⟨8145161304948074578545605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430107536632049719030403 8145161304948074578545605)
              ·
                refine ⟨1527217744677763983477301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8145161304948074578545605 1527217744677763983477301)
                ·
                  refine ⟨143176663563540373450997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1527217744677763983477301 143176663563540373450997)
                  ·
                    rfl

theorem cell20_313690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_313690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313690 prefixEnd_313690 := by exact prefixLift 313690
  have htrace : WordTrace (prefixWord ++ tailWord_313690) baseStart_313690 baseEnd_313690 := by
    simpa [prefixWord, tailWord_313690, baseEnd_313690] using wordTrace_append hprefix tailTrace_313690
  have hstable : (prefixWord ++ tailWord_313690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313690).length < 2 ^ (prefixWord ++ tailWord_313690).sum := by decide
  have hdescent : baseEnd_313690 < baseStart_313690 := by decide
  rcases family_descends (prefixWord ++ tailWord_313690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313714 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_313714 : Nat := 118140960795 + 313714 * 2 ^ 59
def prefixEnd_313714 : Nat := 4983230072969 + 3 ^ 40 * 313714 * 2
def baseEnd_313714 : Nat := 143187617817502956650899

theorem tailTrace_313714 : CollatzResearch.WordTrace tailWord_313714 prefixEnd_313714 143187617817502956650899 := by
  unfold tailWord_313714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860522396368807732685049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7628059723650153953826797 2860522396368807732685049)
  ·
    refine ⟨2145391797276605799513787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2860522396368807732685049 2145391797276605799513787)
    ·
      refine ⟨3218087695914908699270681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145391797276605799513787 3218087695914908699270681)
      ·
        refine ⟨2413565771936181524453011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3218087695914908699270681 2413565771936181524453011)
        ·
          refine ⟨3620348657904272286679517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413565771936181524453011 3620348657904272286679517)
          ·
            refine ⟨1357630746714102107504819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3620348657904272286679517 1357630746714102107504819)
            ·
              refine ⟨2036446120071153161257229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357630746714102107504819 2036446120071153161257229)
              ·
                refine ⟨763667295026682435471461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036446120071153161257229 763667295026682435471461)
                ·
                  refine ⟨143187617817502956650899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763667295026682435471461 143187617817502956650899)
                  ·
                    rfl

theorem cell20_313714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_313714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313714 prefixEnd_313714 := by exact prefixLift 313714
  have htrace : WordTrace (prefixWord ++ tailWord_313714) baseStart_313714 baseEnd_313714 := by
    simpa [prefixWord, tailWord_313714, baseEnd_313714] using wordTrace_append hprefix tailTrace_313714
  have hstable : (prefixWord ++ tailWord_313714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313714).length < 2 ^ (prefixWord ++ tailWord_313714).sum := by decide
  have hdescent : baseEnd_313714 < baseStart_313714 := by decide
  rcases family_descends (prefixWord ++ tailWord_313714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313783 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_313783 : Nat := 118140960795 + 313783 * 2 ^ 59
def prefixEnd_313783 : Nat := 4983230072969 + 3 ^ 40 * 313783 * 2
def baseEnd_313783 : Nat := 143219111297645383350617

theorem tailTrace_313783 : CollatzResearch.WordTrace tailWord_313783 prefixEnd_313783 143219111297645383350617 := by
  unfold tailWord_313783
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444606222225255715002003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7629737481483503810001335 11444606222225255715002003)
  ·
    refine ⟨17166909333337883572503005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11444606222225255715002003 17166909333337883572503005)
    ·
      refine ⟨6437591000001706339688627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17166909333337883572503005 6437591000001706339688627)
      ·
        refine ⟨9656386500002559509532941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437591000001706339688627 9656386500002559509532941)
        ·
          refine ⟨3621144937500959816074853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9656386500002559509532941 3621144937500959816074853)
          ·
            refine ⟨678964675781429965514035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3621144937500959816074853 678964675781429965514035)
            ·
              refine ⟨1018447013672144948271053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678964675781429965514035 1018447013672144948271053)
              ·
                refine ⟨381917630127054355601645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1018447013672144948271053 381917630127054355601645)
                ·
                  refine ⟨143219111297645383350617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381917630127054355601645 143219111297645383350617)
                  ·
                    rfl

theorem cell20_313783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_313783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313783 prefixEnd_313783 := by exact prefixLift 313783
  have htrace : WordTrace (prefixWord ++ tailWord_313783) baseStart_313783 baseEnd_313783 := by
    simpa [prefixWord, tailWord_313783, baseEnd_313783] using wordTrace_append hprefix tailTrace_313783
  have hstable : (prefixWord ++ tailWord_313783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313783).length < 2 ^ (prefixWord ++ tailWord_313783).sum := by decide
  have hdescent : baseEnd_313783 < baseStart_313783 := by decide
  rcases family_descends (prefixWord ++ tailWord_313783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313790 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_313790 : Nat := 118140960795 + 313790 * 2 ^ 59
def prefixEnd_313790 : Nat := 4983230072969 + 3 ^ 40 * 313790 * 2
def baseEnd_313790 : Nat := 143222306288384470117255

theorem tailTrace_313790 : CollatzResearch.WordTrace tailWord_313790 prefixEnd_313790 143222306288384470117255 := by
  unfold tailWord_313790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430607691649986988813353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7629907688799930607004549 1430607691649986988813353)
  ·
    refine ⟨1072955768737490241610015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1430607691649986988813353 1072955768737490241610015)
    ·
      refine ⟨1609433653106235362415023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072955768737490241610015 1609433653106235362415023)
      ·
        refine ⟨2414150479659353043622535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609433653106235362415023 2414150479659353043622535)
        ·
          refine ⟨3621225719489029565433803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414150479659353043622535 3621225719489029565433803)
          ·
            refine ⟨5431838579233544348150705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621225719489029565433803 5431838579233544348150705)
            ·
              refine ⟨4073878934425158261113029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5431838579233544348150705 4073878934425158261113029)
              ·
                refine ⟨763852300204717173958693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4073878934425158261113029 763852300204717173958693)
                ·
                  refine ⟨143222306288384470117255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763852300204717173958693 143222306288384470117255)
                  ·
                    rfl

theorem cell20_313790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_313790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313790 prefixEnd_313790 := by exact prefixLift 313790
  have htrace : WordTrace (prefixWord ++ tailWord_313790) baseStart_313790 baseEnd_313790 := by
    simpa [prefixWord, tailWord_313790, baseEnd_313790] using wordTrace_append hprefix tailTrace_313790
  have hstable : (prefixWord ++ tailWord_313790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313790).length < 2 ^ (prefixWord ++ tailWord_313790).sum := by decide
  have hdescent : baseEnd_313790 < baseStart_313790 := by decide
  rcases family_descends (prefixWord ++ tailWord_313790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313849 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_313849 : Nat := 118140960795 + 313849 * 2 ^ 59
def prefixEnd_313849 : Nat := 4983230072969 + 3 ^ 40 * 313849 * 2
def baseEnd_313849 : Nat := 143249235496042487150347

theorem tailTrace_313849 : CollatzResearch.WordTrace tailWord_313849 prefixEnd_313849 143249235496042487150347 := by
  unfold tailWord_313849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447013439986148986904601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7631342293324099324603067 11447013439986148986904601)
  ·
    refine ⟨8585260079989611740178451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11447013439986148986904601 8585260079989611740178451)
    ·
      refine ⟨12877890119984417610267677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8585260079989611740178451 12877890119984417610267677)
      ·
        refine ⟨4829208794994156603850379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12877890119984417610267677 4829208794994156603850379)
        ·
          refine ⟨7243813192491234905775569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829208794994156603850379 7243813192491234905775569)
          ·
            refine ⟨5432859894368426179331677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7243813192491234905775569 5432859894368426179331677)
            ·
              refine ⟨2037322460388159817249379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5432859894368426179331677 2037322460388159817249379)
              ·
                refine ⟨3055983690582239725874069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037322460388159817249379 3055983690582239725874069)
                ·
                  refine ⟨143249235496042487150347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3055983690582239725874069 143249235496042487150347)
                  ·
                    rfl

theorem cell20_313849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_313849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313849 prefixEnd_313849 := by exact prefixLift 313849
  have htrace : WordTrace (prefixWord ++ tailWord_313849) baseStart_313849 baseEnd_313849 := by
    simpa [prefixWord, tailWord_313849, baseEnd_313849] using wordTrace_append hprefix tailTrace_313849
  have hstable : (prefixWord ++ tailWord_313849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313849).length < 2 ^ (prefixWord ++ tailWord_313849).sum := by decide
  have hdescent : baseEnd_313849 < baseStart_313849 := by decide
  rcases family_descends (prefixWord ++ tailWord_313849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313869 : List Nat := [1, 7, 1, 1, 1, 2, 7]
def baseStart_313869 : Nat := 118140960795 + 313869 * 2 ^ 59
def prefixEnd_313869 : Nat := 4983230072969 + 3 ^ 40 * 313869 * 2
def baseEnd_313869 : Nat := 15917596004556811831511

theorem tailTrace_313869 : CollatzResearch.WordTrace tailWord_313869 prefixEnd_313869 15917596004556811831511 := by
  unfold tailWord_313869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447742899913692402632661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7631828599942461601755107 11447742899913692402632661)
  ·
    refine ⟨268306474216727165686703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11447742899913692402632661 268306474216727165686703)
    ·
      refine ⟨402459711325090748530055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268306474216727165686703 402459711325090748530055)
      ·
        refine ⟨603689566987636122795083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402459711325090748530055 603689566987636122795083)
        ·
          refine ⟨905534350481454184192625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603689566987636122795083 905534350481454184192625)
          ·
            refine ⟨679150762861090638144469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905534350481454184192625 679150762861090638144469)
            ·
              refine ⟨15917596004556811831511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 679150762861090638144469 15917596004556811831511)
              ·
                rfl

theorem cell20_313869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_313869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313869 prefixEnd_313869 := by exact prefixLift 313869
  have htrace : WordTrace (prefixWord ++ tailWord_313869) baseStart_313869 baseEnd_313869 := by
    simpa [prefixWord, tailWord_313869, baseEnd_313869] using wordTrace_append hprefix tailTrace_313869
  have hstable : (prefixWord ++ tailWord_313869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313869).length < 2 ^ (prefixWord ++ tailWord_313869).sum := by decide
  have hdescent : baseEnd_313869 < baseStart_313869 := by decide
  rcases family_descends (prefixWord ++ tailWord_313869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313876 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_313876 : Nat := 118140960795 + 313876 * 2 ^ 59
def prefixEnd_313876 : Nat := 4983230072969 + 3 ^ 40 * 313876 * 2
def baseEnd_313876 : Nat := 143261559031750393250237

theorem tailTrace_313876 : CollatzResearch.WordTrace tailWord_313876 prefixEnd_313876 143261559031750393250237 := by
  unfold tailWord_313876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723999105444166299068741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7631998807258888398758321 5723999105444166299068741)
  ·
    refine ⟨1073249832270781181075389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5723999105444166299068741 1073249832270781181075389)
    ·
      refine ⟨402468687101542942903271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1073249832270781181075389 402468687101542942903271)
      ·
        refine ⟨603703030652314414354907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402468687101542942903271 603703030652314414354907)
        ·
          refine ⟨905554545978471621532361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603703030652314414354907 905554545978471621532361)
          ·
            refine ⟨679165909483853716149271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905554545978471621532361 679165909483853716149271)
            ·
              refine ⟨1018748864225780574223907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679165909483853716149271 1018748864225780574223907)
              ·
                refine ⟨1528123296338670861335861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018748864225780574223907 1528123296338670861335861)
                ·
                  refine ⟨143261559031750393250237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1528123296338670861335861 143261559031750393250237)
                  ·
                    rfl

theorem cell20_313876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_313876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313876 prefixEnd_313876 := by exact prefixLift 313876
  have htrace : WordTrace (prefixWord ++ tailWord_313876) baseStart_313876 baseEnd_313876 := by
    simpa [prefixWord, tailWord_313876, baseEnd_313876] using wordTrace_append hprefix tailTrace_313876
  have hstable : (prefixWord ++ tailWord_313876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313876).length < 2 ^ (prefixWord ++ tailWord_313876).sum := by decide
  have hdescent : baseEnd_313876 < baseStart_313876 := by decide
  rcases family_descends (prefixWord ++ tailWord_313876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313924 : List Nat := [2, 3, 5, 1, 1, 2, 6]
def baseStart_313924 : Nat := 118140960795 + 313924 * 2 ^ 59
def prefixEnd_313924 : Nat := 4983230072969 + 3 ^ 40 * 313924 * 2
def baseEnd_313924 : Nat := 15920385282186173294449

theorem tailTrace_313924 : CollatzResearch.WordTrace tailWord_313924 prefixEnd_313924 15920385282186173294449 := by
  unfold tailWord_313924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724874457357218397942413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7633165943142957863923217 5724874457357218397942413)
  ·
    refine ⟨2146827921508956899228405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5724874457357218397942413 2146827921508956899228405)
    ·
      refine ⟨201265117641464709302663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2146827921508956899228405 201265117641464709302663)
      ·
        refine ⟨301897676462197063953995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201265117641464709302663 301897676462197063953995)
        ·
          refine ⟨452846514693295595930993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301897676462197063953995 452846514693295595930993)
          ·
            refine ⟨339634886019971696948245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452846514693295595930993 339634886019971696948245)
            ·
              refine ⟨15920385282186173294449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 339634886019971696948245 15920385282186173294449)
              ·
                rfl

theorem cell20_313924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 6].length) (baseStart_313924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313924 prefixEnd_313924 := by exact prefixLift 313924
  have htrace : WordTrace (prefixWord ++ tailWord_313924) baseStart_313924 baseEnd_313924 := by
    simpa [prefixWord, tailWord_313924, baseEnd_313924] using wordTrace_append hprefix tailTrace_313924
  have hstable : (prefixWord ++ tailWord_313924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313924).length < 2 ^ (prefixWord ++ tailWord_313924).sum := by decide
  have hdescent : baseEnd_313924 < baseStart_313924 := by decide
  rcases family_descends (prefixWord ++ tailWord_313924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313938 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_313938 : Nat := 118140960795 + 313938 * 2 ^ 59
def prefixEnd_313938 : Nat := 4983230072969 + 3 ^ 40 * 313938 * 2
def baseEnd_313938 : Nat := 143289857521153733183317

theorem tailTrace_313938 : CollatzResearch.WordTrace tailWord_313938 prefixEnd_313938 143289857521153733183317 := by
  unfold tailWord_313938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862564884165929296723617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7633506357775811457929645 2862564884165929296723617)
  ·
    refine ⟨2146923663124446972542713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2862564884165929296723617 2146923663124446972542713)
    ·
      refine ⟨1610192747343335229407035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2146923663124446972542713 1610192747343335229407035)
      ·
        refine ⟨2415289121015002844110553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610192747343335229407035 2415289121015002844110553)
        ·
          refine ⟨1811466840761252133082915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2415289121015002844110553 1811466840761252133082915)
          ·
            refine ⟨2717200261141878199624373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811466840761252133082915 2717200261141878199624373)
            ·
              refine ⟨254737524482051081214785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2717200261141878199624373 254737524482051081214785)
              ·
                refine ⟨191053143361538310911089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254737524482051081214785 191053143361538310911089)
                ·
                  refine ⟨143289857521153733183317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191053143361538310911089 143289857521153733183317)
                  ·
                    rfl

theorem cell20_313938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_313938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313938 prefixEnd_313938 := by exact prefixLift 313938
  have htrace : WordTrace (prefixWord ++ tailWord_313938) baseStart_313938 baseEnd_313938 := by
    simpa [prefixWord, tailWord_313938, baseEnd_313938] using wordTrace_append hprefix tailTrace_313938
  have hstable : (prefixWord ++ tailWord_313938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313938).length < 2 ^ (prefixWord ++ tailWord_313938).sum := by decide
  have hdescent : baseEnd_313938 < baseStart_313938 := by decide
  rcases family_descends (prefixWord ++ tailWord_313938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313948 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_313948 : Nat := 118140960795 + 313948 * 2 ^ 59
def prefixEnd_313948 : Nat := 4983230072969 + 3 ^ 40 * 313948 * 2
def baseEnd_313948 : Nat := 143294421793638142849943

theorem tailTrace_313948 : CollatzResearch.WordTrace tailWord_313948 prefixEnd_313948 143294421793638142849943 := by
  unfold tailWord_313948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725312133313744447379249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7633749511084992596505665 5725312133313744447379249)
  ·
    refine ⟨4293984099985308335534437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5725312133313744447379249 4293984099985308335534437)
    ·
      refine ⟨805122018747245312912707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4293984099985308335534437 805122018747245312912707)
      ·
        refine ⟨1207683028120867969369061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805122018747245312912707 1207683028120867969369061)
        ·
          refine ⟨226440567772662744256699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1207683028120867969369061 226440567772662744256699)
          ·
            refine ⟨339660851658994116385049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226440567772662744256699 339660851658994116385049)
            ·
              refine ⟨254745638744245587288787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339660851658994116385049 254745638744245587288787)
              ·
                refine ⟨382118458116368380933181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254745638744245587288787 382118458116368380933181)
                ·
                  refine ⟨143294421793638142849943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382118458116368380933181 143294421793638142849943)
                  ·
                    rfl

theorem cell20_313948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_313948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_313948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_313948 prefixEnd_313948 := by exact prefixLift 313948
  have htrace : WordTrace (prefixWord ++ tailWord_313948) baseStart_313948 baseEnd_313948 := by
    simpa [prefixWord, tailWord_313948, baseEnd_313948] using wordTrace_append hprefix tailTrace_313948
  have hstable : (prefixWord ++ tailWord_313948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313948).length < 2 ^ (prefixWord ++ tailWord_313948).sum := by decide
  have hdescent : baseEnd_313948 < baseStart_313948 := by decide
  rcases family_descends (prefixWord ++ tailWord_313948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314004 : List Nat := [2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_314004 : Nat := 118140960795 + 314004 * 2 ^ 59
def prefixEnd_314004 : Nat := 4983230072969 + 3 ^ 40 * 314004 * 2
def baseEnd_314004 : Nat := 47773327239850278994349

theorem tailTrace_314004 : CollatzResearch.WordTrace tailWord_314004 prefixEnd_314004 47773327239850278994349 := by
  unfold tailWord_314004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726333377212305229398533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7635111169616406972531377 5726333377212305229398533)
  ·
    refine ⟨1073687508227307230512225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5726333377212305229398533 1073687508227307230512225)
    ·
      refine ⟨805265631170480422884169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1073687508227307230512225 805265631170480422884169)
      ·
        refine ⟨603949223377860317163127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 805265631170480422884169 603949223377860317163127)
        ·
          refine ⟨905923835066790475744691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603949223377860317163127 905923835066790475744691)
          ·
            refine ⟨1358885752600185713617037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905923835066790475744691 1358885752600185713617037)
            ·
              refine ⟨509582157225069642606389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358885752600185713617037 509582157225069642606389)
              ·
                refine ⟨47773327239850278994349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509582157225069642606389 47773327239850278994349)
                ·
                  rfl

theorem cell20_314004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_314004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314004 prefixEnd_314004 := by exact prefixLift 314004
  have htrace : WordTrace (prefixWord ++ tailWord_314004) baseStart_314004 baseEnd_314004 := by
    simpa [prefixWord, tailWord_314004, baseEnd_314004] using wordTrace_append hprefix tailTrace_314004
  have hstable : (prefixWord ++ tailWord_314004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314004).length < 2 ^ (prefixWord ++ tailWord_314004).sum := by decide
  have hdescent : baseEnd_314004 < baseStart_314004 := by decide
  rcases family_descends (prefixWord ++ tailWord_314004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314035 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 2]
def baseStart_314035 : Nat := 118140960795 + 314035 * 2 ^ 59
def prefixEnd_314035 : Nat := 4983230072969 + 3 ^ 40 * 314035 * 2
def baseEnd_314035 : Nat := 143334130964252506949587

theorem tailTrace_314035 : CollatzResearch.WordTrace tailWord_314035 prefixEnd_314035 143334130964252506949587 := by
  unfold tailWord_314035
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453797417312302753175559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7635864944874868502117039 11453797417312302753175559)
  ·
    refine ⟨17180696125968454129763339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11453797417312302753175559 17180696125968454129763339)
    ·
      refine ⟨25771044188952681194645009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17180696125968454129763339 25771044188952681194645009)
      ·
        refine ⟨19328283141714510895983757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25771044188952681194645009 19328283141714510895983757)
        ·
          refine ⟨7248106178142941585993909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19328283141714510895983757 7248106178142941585993909)
          ·
            refine ⟨679509954200900773686929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7248106178142941585993909 679509954200900773686929)
            ·
              refine ⟨509632465650675580265197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679509954200900773686929 509632465650675580265197)
              ·
                refine ⟨191112174619003342599449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509632465650675580265197 191112174619003342599449)
                ·
                  refine ⟨143334130964252506949587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191112174619003342599449 143334130964252506949587)
                  ·
                    rfl

theorem cell20_314035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2].length) (baseStart_314035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314035 prefixEnd_314035 := by exact prefixLift 314035
  have htrace : WordTrace (prefixWord ++ tailWord_314035) baseStart_314035 baseEnd_314035 := by
    simpa [prefixWord, tailWord_314035, baseEnd_314035] using wordTrace_append hprefix tailTrace_314035
  have hstable : (prefixWord ++ tailWord_314035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314035).length < 2 ^ (prefixWord ++ tailWord_314035).sum := by decide
  have hdescent : baseEnd_314035 < baseStart_314035 := by decide
  rcases family_descends (prefixWord ++ tailWord_314035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314056 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_314056 : Nat := 118140960795 + 314056 * 2 ^ 59
def prefixEnd_314056 : Nat := 4983230072969 + 3 ^ 40 * 314056 * 2
def baseEnd_314056 : Nat := 143343715936469767249501

theorem tailTrace_314056 : CollatzResearch.WordTrace tailWord_314056 prefixEnd_314056 143343715936469767249501 := by
  unfold tailWord_314056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727281675118111669845011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7636375566824148893126681 5727281675118111669845011)
  ·
    refine ⟨8590922512677167504767517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727281675118111669845011 8590922512677167504767517)
    ·
      refine ⟨3221595942253937814287819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8590922512677167504767517 3221595942253937814287819)
      ·
        refine ⟨4832393913380906721431729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221595942253937814287819 4832393913380906721431729)
        ·
          refine ⟨3624295435035680041073797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832393913380906721431729 3624295435035680041073797)
          ·
            refine ⟨679555394069190007701337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3624295435035680041073797 679555394069190007701337)
            ·
              refine ⟨509666545551892505776003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679555394069190007701337 509666545551892505776003)
              ·
                refine ⟨764499818327838758664005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509666545551892505776003 764499818327838758664005)
                ·
                  refine ⟨143343715936469767249501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 764499818327838758664005 143343715936469767249501)
                  ·
                    rfl

theorem cell20_314056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_314056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314056 prefixEnd_314056 := by exact prefixLift 314056
  have htrace : WordTrace (prefixWord ++ tailWord_314056) baseStart_314056 baseEnd_314056 := by
    simpa [prefixWord, tailWord_314056, baseEnd_314056] using wordTrace_append hprefix tailTrace_314056
  have hstable : (prefixWord ++ tailWord_314056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314056).length < 2 ^ (prefixWord ++ tailWord_314056).sum := by decide
  have hdescent : baseEnd_314056 < baseStart_314056 := by decide
  rcases family_descends (prefixWord ++ tailWord_314056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314108 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_314108 : Nat := 118140960795 + 314108 * 2 ^ 59
def prefixEnd_314108 : Nat := 4983230072969 + 3 ^ 40 * 314108 * 2
def baseEnd_314108 : Nat := 143367450153388697515955

theorem tailTrace_314108 : CollatzResearch.WordTrace tailWord_314108 prefixEnd_314108 143367450153388697515955 := by
  unfold tailWord_314108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728229973023918110291489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7637639964031890813721985 5728229973023918110291489)
  ·
    refine ⟨4296172479767938582718617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5728229973023918110291489 4296172479767938582718617)
    ·
      refine ⟨3222129359825953937038963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4296172479767938582718617 3222129359825953937038963)
      ·
        refine ⟨4833194039738930905558445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222129359825953937038963 4833194039738930905558445)
        ·
          refine ⟨1812447764902099089584417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4833194039738930905558445 1812447764902099089584417)
          ·
            refine ⟨1359335823676574317188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812447764902099089584417 1359335823676574317188313)
            ·
              refine ⟨1019501867757430737891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359335823676574317188313 1019501867757430737891235)
              ·
                refine ⟨1529252801636146106836853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019501867757430737891235 1529252801636146106836853)
                ·
                  refine ⟨143367450153388697515955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1529252801636146106836853 143367450153388697515955)
                  ·
                    rfl

theorem cell20_314108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_314108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314108 prefixEnd_314108 := by exact prefixLift 314108
  have htrace : WordTrace (prefixWord ++ tailWord_314108) baseStart_314108 baseEnd_314108 := by
    simpa [prefixWord, tailWord_314108, baseEnd_314108] using wordTrace_append hprefix tailTrace_314108
  have hstable : (prefixWord ++ tailWord_314108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314108).length < 2 ^ (prefixWord ++ tailWord_314108).sum := by decide
  have hdescent : baseEnd_314108 < baseStart_314108 := by decide
  rcases family_descends (prefixWord ++ tailWord_314108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314163 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_314163 : Nat := 118140960795 + 314163 * 2 ^ 59
def prefixEnd_314163 : Nat := 4983230072969 + 3 ^ 40 * 314163 * 2
def baseEnd_314163 : Nat := 143392553652052950682397

theorem tailTrace_314163 : CollatzResearch.WordTrace tailWord_314163 prefixEnd_314163 143392553652052950682397 := by
  unfold tailWord_314163
  simp only [CollatzResearch.WordTrace]
  refine ⟨11458465960848580613835143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7638977307232387075890095 11458465960848580613835143)
  ·
    refine ⟨17187698941272870920752715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11458465960848580613835143 17187698941272870920752715)
    ·
      refine ⟨25781548411909306381129073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17187698941272870920752715 25781548411909306381129073)
      ·
        refine ⟨19336161308931979785846805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25781548411909306381129073 19336161308931979785846805)
        ·
          refine ⟨906382561356186552461569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19336161308931979785846805 906382561356186552461569)
          ·
            refine ⟨679786921017139914346177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906382561356186552461569 679786921017139914346177)
            ·
              refine ⟨509840190762854935759633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679786921017139914346177 509840190762854935759633)
              ·
                refine ⟨382380143072141201819725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509840190762854935759633 382380143072141201819725)
                ·
                  refine ⟨143392553652052950682397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382380143072141201819725 143392553652052950682397)
                  ·
                    rfl

theorem cell20_314163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_314163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314163 prefixEnd_314163 := by exact prefixLift 314163
  have htrace : WordTrace (prefixWord ++ tailWord_314163) baseStart_314163 baseEnd_314163 := by
    simpa [prefixWord, tailWord_314163, baseEnd_314163] using wordTrace_append hprefix tailTrace_314163
  have hstable : (prefixWord ++ tailWord_314163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314163).length < 2 ^ (prefixWord ++ tailWord_314163).sum := by decide
  have hdescent : baseEnd_314163 < baseStart_314163 := by decide
  rcases family_descends (prefixWord ++ tailWord_314163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314173 : List Nat := [1, 4, 1, 4, 3, 1, 1, 5]
def baseStart_314173 : Nat := 118140960795 + 314173 * 2 ^ 59
def prefixEnd_314173 : Nat := 4983230072969 + 3 ^ 40 * 314173 * 2
def baseEnd_314173 : Nat := 47799039308179120116341

theorem tailTrace_314173 : CollatzResearch.WordTrace tailWord_314173 prefixEnd_314173 47799039308179120116341 := by
  unfold tailWord_314173
  simp only [CollatzResearch.WordTrace]
  refine ⟨11458830690812352321699173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7639220460541568214466115 11458830690812352321699173)
  ·
    refine ⟨2148530754527316060318595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11458830690812352321699173 2148530754527316060318595)
    ·
      refine ⟨3222796131790974090477893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148530754527316060318595 3222796131790974090477893)
      ·
        refine ⟨604274274710807641964605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3222796131790974090477893 604274274710807641964605)
        ·
          refine ⟨226602853016552865736727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 604274274710807641964605 226602853016552865736727)
          ·
            refine ⟨339904279524829298605091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226602853016552865736727 339904279524829298605091)
            ·
              refine ⟨509856419287243947907637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339904279524829298605091 509856419287243947907637)
              ·
                refine ⟨47799039308179120116341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509856419287243947907637 47799039308179120116341)
                ·
                  rfl

theorem cell20_314173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_314173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314173 prefixEnd_314173 := by exact prefixLift 314173
  have htrace : WordTrace (prefixWord ++ tailWord_314173) baseStart_314173 baseEnd_314173 := by
    simpa [prefixWord, tailWord_314173, baseEnd_314173] using wordTrace_append hprefix tailTrace_314173
  have hstable : (prefixWord ++ tailWord_314173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314173).length < 2 ^ (prefixWord ++ tailWord_314173).sum := by decide
  have hdescent : baseEnd_314173 < baseStart_314173 := by decide
  rcases family_descends (prefixWord ++ tailWord_314173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314184 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_314184 : Nat := 118140960795 + 314184 * 2 ^ 59
def prefixEnd_314184 : Nat := 4983230072969 + 3 ^ 40 * 314184 * 2
def baseEnd_314184 : Nat := 143402138624270210982311

theorem tailTrace_314184 : CollatzResearch.WordTrace tailWord_314184 prefixEnd_314184 143402138624270210982311 := by
  unfold tailWord_314184
  simp only [CollatzResearch.WordTrace]
  refine ⟨5729615946886250600174803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7639487929181667466899737 5729615946886250600174803)
  ·
    refine ⟨8594423920329375900262205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5729615946886250600174803 8594423920329375900262205)
    ·
      refine ⟨3222908970123515962598327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8594423920329375900262205 3222908970123515962598327)
      ·
        refine ⟨4834363455185273943897491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222908970123515962598327 4834363455185273943897491)
        ·
          refine ⟨7251545182777910915846237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834363455185273943897491 7251545182777910915846237)
          ·
            refine ⟨2719329443541716593442339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7251545182777910915846237 2719329443541716593442339)
            ·
              refine ⟨4078994165312574890163509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719329443541716593442339 4078994165312574890163509)
              ·
                refine ⟨382405702998053895952829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4078994165312574890163509 382405702998053895952829)
                ·
                  refine ⟨143402138624270210982311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382405702998053895952829 143402138624270210982311)
                  ·
                    rfl

theorem cell20_314184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_314184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314184 prefixEnd_314184 := by exact prefixLift 314184
  have htrace : WordTrace (prefixWord ++ tailWord_314184) baseStart_314184 baseEnd_314184 := by
    simpa [prefixWord, tailWord_314184, baseEnd_314184] using wordTrace_append hprefix tailTrace_314184
  have hstable : (prefixWord ++ tailWord_314184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314184).length < 2 ^ (prefixWord ++ tailWord_314184).sum := by decide
  have hdescent : baseEnd_314184 < baseStart_314184 := by decide
  rcases family_descends (prefixWord ++ tailWord_314184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314204 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_314204 : Nat := 118140960795 + 314204 * 2 ^ 59
def prefixEnd_314204 : Nat := 4983230072969 + 3 ^ 40 * 314204 * 2
def baseEnd_314204 : Nat := 143411267169239030315563

theorem tailTrace_314204 : CollatzResearch.WordTrace tailWord_314204 prefixEnd_314204 143411267169239030315563 := by
  unfold tailWord_314204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5729980676850022308038833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7639974235800029744051777 5729980676850022308038833)
  ·
    refine ⟨4297485507637516731029125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5729980676850022308038833 4297485507637516731029125)
    ·
      refine ⟨805778532682034387067961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4297485507637516731029125 805778532682034387067961)
      ·
        refine ⟨604333899511525790300971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 805778532682034387067961 604333899511525790300971)
        ·
          refine ⟨906500849267288685451457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604333899511525790300971 906500849267288685451457)
          ·
            refine ⟨679875636950466514088593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906500849267288685451457 679875636950466514088593)
            ·
              refine ⟨509906727712849885566445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679875636950466514088593 509906727712849885566445)
              ·
                refine ⟨191215022892318707087417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509906727712849885566445 191215022892318707087417)
                ·
                  refine ⟨143411267169239030315563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191215022892318707087417 143411267169239030315563)
                  ·
                    rfl

theorem cell20_314204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_314204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314204 prefixEnd_314204 := by exact prefixLift 314204
  have htrace : WordTrace (prefixWord ++ tailWord_314204) baseStart_314204 baseEnd_314204 := by
    simpa [prefixWord, tailWord_314204, baseEnd_314204] using wordTrace_append hprefix tailTrace_314204
  have hstable : (prefixWord ++ tailWord_314204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314204).length < 2 ^ (prefixWord ++ tailWord_314204).sum := by decide
  have hdescent : baseEnd_314204 < baseStart_314204 := by decide
  rcases family_descends (prefixWord ++ tailWord_314204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314260 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_314260 : Nat := 118140960795 + 314260 * 2 ^ 59
def prefixEnd_314260 : Nat := 4983230072969 + 3 ^ 40 * 314260 * 2
def baseEnd_314260 : Nat := 143436827095151724448667

theorem tailTrace_314260 : CollatzResearch.WordTrace tailWord_314260 prefixEnd_314260 143436827095151724448667 := by
  unfold tailWord_314260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731001920748583090058117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7641335894331444120077489 5731001920748583090058117)
  ·
    refine ⟨1074562860140359329385897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5731001920748583090058117 1074562860140359329385897)
    ·
      refine ⟨805922145105269497039423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074562860140359329385897 805922145105269497039423)
      ·
        refine ⟨1208883217657904245559135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805922145105269497039423 1208883217657904245559135)
        ·
          refine ⟨1813324826486856368338703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208883217657904245559135 1813324826486856368338703)
          ·
            refine ⟨2719987239730284552508055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813324826486856368338703 2719987239730284552508055)
            ·
              refine ⟨4079980859595426828762083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719987239730284552508055 4079980859595426828762083)
              ·
                refine ⟨6119971289393140243143125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079980859595426828762083 6119971289393140243143125)
                ·
                  refine ⟨143436827095151724448667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6119971289393140243143125 143436827095151724448667)
                  ·
                    rfl

theorem cell20_314260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_314260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314260 prefixEnd_314260 := by exact prefixLift 314260
  have htrace : WordTrace (prefixWord ++ tailWord_314260) baseStart_314260 baseEnd_314260 := by
    simpa [prefixWord, tailWord_314260, baseEnd_314260] using wordTrace_append hprefix tailTrace_314260
  have hstable : (prefixWord ++ tailWord_314260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314260).length < 2 ^ (prefixWord ++ tailWord_314260).sum := by decide
  have hdescent : baseEnd_314260 < baseStart_314260 := by decide
  rcases family_descends (prefixWord ++ tailWord_314260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314281 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_314281 : Nat := 118140960795 + 314281 * 2 ^ 59
def prefixEnd_314281 : Nat := 4983230072969 + 3 ^ 40 * 314281 * 2
def baseEnd_314281 : Nat := 143446412067368984748581

theorem tailTrace_314281 : CollatzResearch.WordTrace tailWord_314281 prefixEnd_314281 143446412067368984748581 := by
  unfold tailWord_314281
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462769774421086766630697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7641846516280724511087131 11462769774421086766630697)
  ·
    refine ⟨8597077330815815074973023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11462769774421086766630697 8597077330815815074973023)
    ·
      refine ⟨12895615996223722612459535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597077330815815074973023 12895615996223722612459535)
      ·
        refine ⟨19343423994335583918689303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12895615996223722612459535 19343423994335583918689303)
        ·
          refine ⟨29015135991503375878033955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19343423994335583918689303 29015135991503375878033955)
          ·
            refine ⟨43522703987255063817050933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29015135991503375878033955 43522703987255063817050933)
            ·
              refine ⟨4080253498805162232848525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43522703987255063817050933 4080253498805162232848525)
              ·
                refine ⟨1530095062051935837318197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4080253498805162232848525 1530095062051935837318197)
                ·
                  refine ⟨143446412067368984748581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530095062051935837318197 143446412067368984748581)
                  ·
                    rfl

theorem cell20_314281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_314281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314281 prefixEnd_314281 := by exact prefixLift 314281
  have htrace : WordTrace (prefixWord ++ tailWord_314281) baseStart_314281 baseEnd_314281 := by
    simpa [prefixWord, tailWord_314281, baseEnd_314281] using wordTrace_append hprefix tailTrace_314281
  have hstable : (prefixWord ++ tailWord_314281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314281).length < 2 ^ (prefixWord ++ tailWord_314281).sum := by decide
  have hdescent : baseEnd_314281 < baseStart_314281 := by decide
  rcases family_descends (prefixWord ++ tailWord_314281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314298 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_314298 : Nat := 118140960795 + 314298 * 2 ^ 59
def prefixEnd_314298 : Nat := 4983230072969 + 3 ^ 40 * 314298 * 2
def baseEnd_314298 : Nat := 143454171330592481181845

theorem tailTrace_314298 : CollatzResearch.WordTrace tailWord_314298 prefixEnd_314298 143454171330592481181845 := by
  unfold tailWord_314298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865847453839874667499887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7642259876906332446666365 2865847453839874667499887)
  ·
    refine ⟨4298771180759812001249831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2865847453839874667499887 4298771180759812001249831)
    ·
      refine ⟨6448156771139718001874747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298771180759812001249831 6448156771139718001874747)
      ·
        refine ⟨9672235156709577002812121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6448156771139718001874747 9672235156709577002812121)
        ·
          refine ⟨7254176367532182752109091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9672235156709577002812121 7254176367532182752109091)
          ·
            refine ⟨10881264551298274128163637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254176367532182752109091 10881264551298274128163637)
            ·
              refine ⟨1020118551684213199515341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10881264551298274128163637 1020118551684213199515341)
              ·
                refine ⟨382544456881579949818253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020118551684213199515341 382544456881579949818253)
                ·
                  refine ⟨143454171330592481181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382544456881579949818253 143454171330592481181845)
                  ·
                    rfl

theorem cell20_314298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_314298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314298 prefixEnd_314298 := by exact prefixLift 314298
  have htrace : WordTrace (prefixWord ++ tailWord_314298) baseStart_314298 baseEnd_314298 := by
    simpa [prefixWord, tailWord_314298, baseEnd_314298] using wordTrace_append hprefix tailTrace_314298
  have hstable : (prefixWord ++ tailWord_314298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314298).length < 2 ^ (prefixWord ++ tailWord_314298).sum := by decide
  have hdescent : baseEnd_314298 < baseStart_314298 := by decide
  rcases family_descends (prefixWord ++ tailWord_314298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314335 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 2]
def baseStart_314335 : Nat := 118140960795 + 314335 * 2 ^ 59
def prefixEnd_314335 : Nat := 4983230072969 + 3 ^ 40 * 314335 * 2
def baseEnd_314335 : Nat := 143471059138784796948361

theorem tailTrace_314335 : CollatzResearch.WordTrace tailWord_314335 prefixEnd_314335 143471059138784796948361 := by
  unfold tailWord_314335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464739316225453989096459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7643159544150302659397639 11464739316225453989096459)
  ·
    refine ⟨17197108974338180983644689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464739316225453989096459 17197108974338180983644689)
    ·
      refine ⟨12897831730753635737733517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17197108974338180983644689 12897831730753635737733517)
      ·
        refine ⟨4836686899032613401650069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12897831730753635737733517 4836686899032613401650069)
        ·
          refine ⟨226719698392153753202347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4836686899032613401650069 226719698392153753202347)
          ·
            refine ⟨340079547588230629803521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226719698392153753202347 340079547588230629803521)
            ·
              refine ⟨255059660691172972352641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340079547588230629803521 255059660691172972352641)
              ·
                refine ⟨191294745518379729264481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255059660691172972352641 191294745518379729264481)
                ·
                  refine ⟨143471059138784796948361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191294745518379729264481 143471059138784796948361)
                  ·
                    rfl

theorem cell20_314335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2].length) (baseStart_314335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314335 prefixEnd_314335 := by exact prefixLift 314335
  have htrace : WordTrace (prefixWord ++ tailWord_314335) baseStart_314335 baseEnd_314335 := by
    simpa [prefixWord, tailWord_314335, baseEnd_314335] using wordTrace_append hprefix tailTrace_314335
  have hstable : (prefixWord ++ tailWord_314335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314335).length < 2 ^ (prefixWord ++ tailWord_314335).sum := by decide
  have hdescent : baseEnd_314335 < baseStart_314335 := by decide
  rcases family_descends (prefixWord ++ tailWord_314335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314391 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_314391 : Nat := 118140960795 + 314391 * 2 ^ 59
def prefixEnd_314391 : Nat := 4983230072969 + 3 ^ 40 * 314391 * 2
def baseEnd_314391 : Nat := 143496619064697491081465

theorem tailTrace_314391 : CollatzResearch.WordTrace tailWord_314391 prefixEnd_314391 143496619064697491081465 := by
  unfold tailWord_314391
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466781804022575553135027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7644521202681717035423351 11466781804022575553135027)
  ·
    refine ⟨17200172706033863329702541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11466781804022575553135027 17200172706033863329702541)
    ·
      refine ⟨6450064764762698748638453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17200172706033863329702541 6450064764762698748638453)
      ·
        refine ⟨604693571696503007684855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6450064764762698748638453 604693571696503007684855)
        ·
          refine ⟨907040357544754511527283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604693571696503007684855 907040357544754511527283)
          ·
            refine ⟨1360560536317131767290925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907040357544754511527283 1360560536317131767290925)
            ·
              refine ⟨510210201118924412734097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1360560536317131767290925 510210201118924412734097)
              ·
                refine ⟨382657650839193309550573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510210201118924412734097 382657650839193309550573)
                ·
                  refine ⟨143496619064697491081465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382657650839193309550573 143496619064697491081465)
                  ·
                    rfl

theorem cell20_314391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_314391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314391 prefixEnd_314391 := by exact prefixLift 314391
  have htrace : WordTrace (prefixWord ++ tailWord_314391) baseStart_314391 baseEnd_314391 := by
    simpa [prefixWord, tailWord_314391, baseEnd_314391] using wordTrace_append hprefix tailTrace_314391
  have hstable : (prefixWord ++ tailWord_314391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314391).length < 2 ^ (prefixWord ++ tailWord_314391).sum := by decide
  have hdescent : baseEnd_314391 < baseStart_314391 := by decide
  rcases family_descends (prefixWord ++ tailWord_314391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314422 : List Nat := [5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_314422 : Nat := 118140960795 + 314422 * 2 ^ 59
def prefixEnd_314422 : Nat := 4983230072969 + 3 ^ 40 * 314422 * 2
def baseEnd_314422 : Nat := 47836922769799720349335

theorem tailTrace_314422 : CollatzResearch.WordTrace tailWord_314422 prefixEnd_314422 47836922769799720349335 := by
  unfold tailWord_314422
  simp only [CollatzResearch.WordTrace]
  refine ⟨716744529181891740469595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7645274977940178565009013 716744529181891740469595)
  ·
    refine ⟨1075116793772837610704393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716744529181891740469595 1075116793772837610704393)
    ·
      refine ⟨806337595329628208028295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075116793772837610704393 806337595329628208028295)
      ·
        refine ⟨1209506392994442312042443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806337595329628208028295 1209506392994442312042443)
        ·
          refine ⟨1814259589491663468063665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209506392994442312042443 1814259589491663468063665)
          ·
            refine ⟨1360694692118747601047749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814259589491663468063665 1360694692118747601047749)
            ·
              refine ⟨255130254772265175196453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1360694692118747601047749 255130254772265175196453)
              ·
                refine ⟨47836922769799720349335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255130254772265175196453 47836922769799720349335)
                ·
                  rfl

theorem cell20_314422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_314422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314422 prefixEnd_314422 := by exact prefixLift 314422
  have htrace : WordTrace (prefixWord ++ tailWord_314422) baseStart_314422 baseEnd_314422 := by
    simpa [prefixWord, tailWord_314422, baseEnd_314422] using wordTrace_append hprefix tailTrace_314422
  have hstable : (prefixWord ++ tailWord_314422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314422).length < 2 ^ (prefixWord ++ tailWord_314422).sum := by decide
  have hdescent : baseEnd_314422 < baseStart_314422 := by decide
  rcases family_descends (prefixWord ++ tailWord_314422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314450 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_314450 : Nat := 118140960795 + 314450 * 2 ^ 59
def prefixEnd_314450 : Nat := 4983230072969 + 3 ^ 40 * 314450 * 2
def baseEnd_314450 : Nat := 143523548272355508114557

theorem tailTrace_314450 : CollatzResearch.WordTrace tailWord_314450 prefixEnd_314450 143523548272355508114557 := by
  unfold tailWord_314450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867233427702207157383201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7645955807205885753021869 2867233427702207157383201)
  ·
    refine ⟨2150425070776655368037401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2867233427702207157383201 2150425070776655368037401)
    ·
      refine ⟨1612818803082491526028051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150425070776655368037401 1612818803082491526028051)
      ·
        refine ⟨2419228204623737289042077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612818803082491526028051 2419228204623737289042077)
        ·
          refine ⟨907210576733901483390779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2419228204623737289042077 907210576733901483390779)
          ·
            refine ⟨1360815865100852225086169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907210576733901483390779 1360815865100852225086169)
            ·
              refine ⟨1020611898825639168814627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360815865100852225086169 1020611898825639168814627)
              ·
                refine ⟨1530917848238458753221941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020611898825639168814627 1530917848238458753221941)
                ·
                  refine ⟨143523548272355508114557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530917848238458753221941 143523548272355508114557)
                  ·
                    rfl

theorem cell20_314450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_314450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314450 prefixEnd_314450 := by exact prefixLift 314450
  have htrace : WordTrace (prefixWord ++ tailWord_314450) baseStart_314450 baseEnd_314450 := by
    simpa [prefixWord, tailWord_314450, baseEnd_314450] using wordTrace_append hprefix tailTrace_314450
  have hstable : (prefixWord ++ tailWord_314450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314450).length < 2 ^ (prefixWord ++ tailWord_314450).sum := by decide
  have hdescent : baseEnd_314450 < baseStart_314450 := by decide
  rcases family_descends (prefixWord ++ tailWord_314450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314453 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 2]
def baseStart_314453 : Nat := 118140960795 + 314453 * 2 ^ 59
def prefixEnd_314453 : Nat := 4983230072969 + 3 ^ 40 * 314453 * 2
def baseEnd_314453 : Nat := 143524917554100831014545

theorem tailTrace_314453 : CollatzResearch.WordTrace tailWord_314453 prefixEnd_314453 143524917554100831014545 := by
  unfold tailWord_314453
  simp only [CollatzResearch.WordTrace]
  refine ⟨11469043129797960141892013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7646028753198640094594675 11469043129797960141892013)
  ·
    refine ⟨4300891173674235053209505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11469043129797960141892013 4300891173674235053209505)
    ·
      refine ⟨3225668380255676289907129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4300891173674235053209505 3225668380255676289907129)
      ·
        refine ⟨2419251285191757217430347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3225668380255676289907129 2419251285191757217430347)
        ·
          refine ⟨3628876927787635826145521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419251285191757217430347 3628876927787635826145521)
          ·
            refine ⟨2721657695840726869609141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3628876927787635826145521 2721657695840726869609141)
            ·
              refine ⟨255155408985068144025857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2721657695840726869609141 255155408985068144025857)
              ·
                refine ⟨191366556738801108019393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255155408985068144025857 191366556738801108019393)
                ·
                  refine ⟨143524917554100831014545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191366556738801108019393 143524917554100831014545)
                  ·
                    rfl

theorem cell20_314453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_314453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314453 prefixEnd_314453 := by exact prefixLift 314453
  have htrace : WordTrace (prefixWord ++ tailWord_314453) baseStart_314453 baseEnd_314453 := by
    simpa [prefixWord, tailWord_314453, baseEnd_314453] using wordTrace_append hprefix tailTrace_314453
  have hstable : (prefixWord ++ tailWord_314453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314453).length < 2 ^ (prefixWord ++ tailWord_314453).sum := by decide
  have hdescent : baseEnd_314453 < baseStart_314453 := by decide
  rcases family_descends (prefixWord ++ tailWord_314453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314464 : List Nat := [2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_314464 : Nat := 118140960795 + 314464 * 2 ^ 59
def prefixEnd_314464 : Nat := 4983230072969 + 3 ^ 40 * 314464 * 2
def baseEnd_314464 : Nat := 47843312751277893882611

theorem tailTrace_314464 : CollatzResearch.WordTrace tailWord_314464 prefixEnd_314464 47843312751277893882611 := by
  unfold tailWord_314464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734722166379054510271223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7646296221838739347028297 5734722166379054510271223)
  ·
    refine ⟨8602083249568581765406835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734722166379054510271223 8602083249568581765406835)
    ·
      refine ⟨12903124874352872648110253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8602083249568581765406835 12903124874352872648110253)
      ·
        refine ⟨4838671827882327243041345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12903124874352872648110253 4838671827882327243041345)
        ·
          refine ⟨3629003870911745432281009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838671827882327243041345 3629003870911745432281009)
          ·
            refine ⟨2721752903183809074210757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629003870911745432281009 2721752903183809074210757)
            ·
              refine ⟨510328669346964201414517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2721752903183809074210757 510328669346964201414517)
              ·
                refine ⟨47843312751277893882611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 510328669346964201414517 47843312751277893882611)
                ·
                  rfl

theorem cell20_314464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_314464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314464 prefixEnd_314464 := by exact prefixLift 314464
  have htrace : WordTrace (prefixWord ++ tailWord_314464) baseStart_314464 baseEnd_314464 := by
    simpa [prefixWord, tailWord_314464, baseEnd_314464] using wordTrace_append hprefix tailTrace_314464
  have hstable : (prefixWord ++ tailWord_314464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314464).length < 2 ^ (prefixWord ++ tailWord_314464).sum := by decide
  have hdescent : baseEnd_314464 < baseStart_314464 := by decide
  rcases family_descends (prefixWord ++ tailWord_314464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314519 : List Nat := [1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_314519 : Nat := 118140960795 + 314519 * 2 ^ 59
def prefixEnd_314519 : Nat := 4983230072969 + 3 ^ 40 * 314519 * 2
def baseEnd_314519 : Nat := 47851680584165978271425

theorem tailTrace_314519 : CollatzResearch.WordTrace tailWord_314519 prefixEnd_314519 47851680584165978271425 := by
  unfold tailWord_314519
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471450347558853413794611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7647633565039235609196407 11471450347558853413794611)
  ·
    refine ⟨17207175521338280120691917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11471450347558853413794611 17207175521338280120691917)
    ·
      refine ⟨6452690820501855045259469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17207175521338280120691917 6452690820501855045259469)
      ·
        refine ⟨2419759057688195641972301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6452690820501855045259469 2419759057688195641972301)
        ·
          refine ⟨907409646633073365739613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2419759057688195641972301 907409646633073365739613)
          ·
            refine ⟨340278617487402512152355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 907409646633073365739613 340278617487402512152355)
            ·
              refine ⟨510417926231103768228533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340278617487402512152355 510417926231103768228533)
              ·
                refine ⟨47851680584165978271425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 510417926231103768228533 47851680584165978271425)
                ·
                  rfl

theorem cell20_314519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_314519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314519 prefixEnd_314519 := by exact prefixLift 314519
  have htrace : WordTrace (prefixWord ++ tailWord_314519) baseStart_314519 baseEnd_314519 := by
    simpa [prefixWord, tailWord_314519, baseEnd_314519] using wordTrace_append hprefix tailTrace_314519
  have hstable : (prefixWord ++ tailWord_314519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314519).length < 2 ^ (prefixWord ++ tailWord_314519).sum := by decide
  have hdescent : baseEnd_314519 < baseStart_314519 := by decide
  rcases family_descends (prefixWord ++ tailWord_314519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314533 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_314533 : Nat := 118140960795 + 314533 * 2 ^ 59
def prefixEnd_314533 : Nat := 4983230072969 + 3 ^ 40 * 314533 * 2
def baseEnd_314533 : Nat := 143561431733976108347551

theorem tailTrace_314533 : CollatzResearch.WordTrace tailWord_314533 prefixEnd_314533 143561431733976108347551 := by
  unfold tailWord_314533
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471960969508133804804253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7647973979672089203202835 11471960969508133804804253)
  ·
    refine ⟨4301985363565550176801595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11471960969508133804804253 4301985363565550176801595)
    ·
      refine ⟨6452978045348325265202393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301985363565550176801595 6452978045348325265202393)
      ·
        refine ⟨4839733534011243948901795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6452978045348325265202393 4839733534011243948901795)
        ·
          refine ⟨7259600301016865923352693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4839733534011243948901795 7259600301016865923352693)
          ·
            refine ⟨680587528220331180314315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7259600301016865923352693 680587528220331180314315)
            ·
              refine ⟨1020881292330496770471473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680587528220331180314315 1020881292330496770471473)
              ·
                refine ⟨765660969247872577853605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020881292330496770471473 765660969247872577853605)
                ·
                  refine ⟨143561431733976108347551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765660969247872577853605 143561431733976108347551)
                  ·
                    rfl

theorem cell20_314533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_314533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314533 prefixEnd_314533 := by exact prefixLift 314533
  have htrace : WordTrace (prefixWord ++ tailWord_314533) baseStart_314533 baseEnd_314533 := by
    simpa [prefixWord, tailWord_314533, baseEnd_314533] using wordTrace_append hprefix tailTrace_314533
  have hstable : (prefixWord ++ tailWord_314533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314533).length < 2 ^ (prefixWord ++ tailWord_314533).sum := by decide
  have hdescent : baseEnd_314533 < baseStart_314533 := by decide
  rcases family_descends (prefixWord ++ tailWord_314533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314554 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_314554 : Nat := 118140960795 + 314554 * 2 ^ 59
def prefixEnd_314554 : Nat := 4983230072969 + 3 ^ 40 * 314554 * 2
def baseEnd_314554 : Nat := 143571016706193368647465

theorem tailTrace_314554 : CollatzResearch.WordTrace tailWord_314554 prefixEnd_314554 143571016706193368647465 := by
  unfold tailWord_314554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868181725608013597829679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7648484601621369594212477 2868181725608013597829679)
  ·
    refine ⟨4302272588412020396744519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2868181725608013597829679 4302272588412020396744519)
    ·
      refine ⟨6453408882618030595116779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302272588412020396744519 6453408882618030595116779)
      ·
        refine ⟨9680113323927045892675169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453408882618030595116779 9680113323927045892675169)
        ·
          refine ⟨7260084992945284419506377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9680113323927045892675169 7260084992945284419506377)
          ·
            refine ⟨5445063744708963314629783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7260084992945284419506377 5445063744708963314629783)
            ·
              refine ⟨8167595617063444971944675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445063744708963314629783 8167595617063444971944675)
              ·
                refine ⟨12251393425595167457917013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167595617063444971944675 12251393425595167457917013)
                ·
                  refine ⟨143571016706193368647465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12251393425595167457917013 143571016706193368647465)
                  ·
                    rfl

theorem cell20_314554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_314554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314554 prefixEnd_314554 := by exact prefixLift 314554
  have htrace : WordTrace (prefixWord ++ tailWord_314554) baseStart_314554 baseEnd_314554 := by
    simpa [prefixWord, tailWord_314554, baseEnd_314554] using wordTrace_append hprefix tailTrace_314554
  have hstable : (prefixWord ++ tailWord_314554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314554).length < 2 ^ (prefixWord ++ tailWord_314554).sum := by decide
  have hdescent : baseEnd_314554 < baseStart_314554 := by decide
  rcases family_descends (prefixWord ++ tailWord_314554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314560 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_314560 : Nat := 118140960795 + 314560 * 2 ^ 59
def prefixEnd_314560 : Nat := 4983230072969 + 3 ^ 40 * 314560 * 2
def baseEnd_314560 : Nat := 143573755269684014447441

theorem tailTrace_314560 : CollatzResearch.WordTrace tailWord_314560 prefixEnd_314560 143573755269684014447441 := by
  unfold tailWord_314560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736472870205158708018567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7648630493606878277358089 5736472870205158708018567)
  ·
    refine ⟨8604709305307738062027851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5736472870205158708018567 8604709305307738062027851)
    ·
      refine ⟨12907063957961607093041777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8604709305307738062027851 12907063957961607093041777)
      ·
        refine ⟨9680297968471205319781333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12907063957961607093041777 9680297968471205319781333)
        ·
          refine ⟨226881983636043874682375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9680297968471205319781333 226881983636043874682375)
          ·
            refine ⟨340322975454065812023563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226881983636043874682375 340322975454065812023563)
            ·
              refine ⟨510484463181098718035345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340322975454065812023563 510484463181098718035345)
              ·
                refine ⟨382863347385824038526509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510484463181098718035345 382863347385824038526509)
                ·
                  refine ⟨143573755269684014447441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382863347385824038526509 143573755269684014447441)
                  ·
                    rfl

theorem cell20_314560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_314560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314560 prefixEnd_314560 := by exact prefixLift 314560
  have htrace : WordTrace (prefixWord ++ tailWord_314560) baseStart_314560 baseEnd_314560 := by
    simpa [prefixWord, tailWord_314560, baseEnd_314560] using wordTrace_append hprefix tailTrace_314560
  have hstable : (prefixWord ++ tailWord_314560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314560).length < 2 ^ (prefixWord ++ tailWord_314560).sum := by decide
  have hdescent : baseEnd_314560 < baseStart_314560 := by decide
  rcases family_descends (prefixWord ++ tailWord_314560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314578 : List Nat := [3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_314578 : Nat := 118140960795 + 314578 * 2 ^ 59
def prefixEnd_314578 : Nat := 4983230072969 + 3 ^ 40 * 314578 * 2
def baseEnd_314578 : Nat := 47860656986718650615789

theorem tailTrace_314578 : CollatzResearch.WordTrace tailWord_314578 prefixEnd_314578 47860656986718650615789 := by
  unfold tailWord_314578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868400563586276622548097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7649068169563404326794925 2868400563586276622548097)
  ·
    refine ⟨2151300422689707466911073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2868400563586276622548097 2151300422689707466911073)
    ·
      refine ⟨1613475317017280600183305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151300422689707466911073 1613475317017280600183305)
      ·
        refine ⟨1210106487762960450137479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613475317017280600183305 1210106487762960450137479)
        ·
          refine ⟨1815159731644440675206219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210106487762960450137479 1815159731644440675206219)
          ·
            refine ⟨2722739597466661012809329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815159731644440675206219 2722739597466661012809329)
            ·
              refine ⟨2042054698099995759606997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722739597466661012809329 2042054698099995759606997)
              ·
                refine ⟨47860656986718650615789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2042054698099995759606997 47860656986718650615789)
                ·
                  rfl

theorem cell20_314578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_314578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314578 prefixEnd_314578 := by exact prefixLift 314578
  have htrace : WordTrace (prefixWord ++ tailWord_314578) baseStart_314578 baseEnd_314578 := by
    simpa [prefixWord, tailWord_314578, baseEnd_314578] using wordTrace_append hprefix tailTrace_314578
  have hstable : (prefixWord ++ tailWord_314578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314578).length < 2 ^ (prefixWord ++ tailWord_314578).sum := by decide
  have hdescent : baseEnd_314578 < baseStart_314578 := by decide
  rcases family_descends (prefixWord ++ tailWord_314578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314605 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 2]
def baseStart_314605 : Nat := 118140960795 + 314605 * 2 ^ 59
def prefixEnd_314605 : Nat := 4983230072969 + 3 ^ 40 * 314605 * 2
def baseEnd_314605 : Nat := 143594294495863857947257

theorem tailTrace_314605 : CollatzResearch.WordTrace tailWord_314605 prefixEnd_314605 143594294495863857947257 := by
  unfold tailWord_314605
  simp only [CollatzResearch.WordTrace]
  refine ⟨11474587025247290101425269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7649724683498193400950179 11474587025247290101425269)
  ·
    refine ⟨1075742533616933447008619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11474587025247290101425269 1075742533616933447008619)
    ·
      refine ⟨1613613800425400170512929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075742533616933447008619 1613613800425400170512929)
      ·
        refine ⟨1210210350319050127884697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613613800425400170512929 1210210350319050127884697)
        ·
          refine ⟨907657762739287595913523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210210350319050127884697 907657762739287595913523)
          ·
            refine ⟨1361486644108931393870285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907657762739287595913523 1361486644108931393870285)
            ·
              refine ⟨510557491540849272701357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1361486644108931393870285 510557491540849272701357)
              ·
                refine ⟨191459059327818477263009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 510557491540849272701357 191459059327818477263009)
                ·
                  refine ⟨143594294495863857947257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191459059327818477263009 143594294495863857947257)
                  ·
                    rfl

theorem cell20_314605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_314605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314605 prefixEnd_314605 := by exact prefixLift 314605
  have htrace : WordTrace (prefixWord ++ tailWord_314605) baseStart_314605 baseEnd_314605 := by
    simpa [prefixWord, tailWord_314605, baseEnd_314605] using wordTrace_append hprefix tailTrace_314605
  have hstable : (prefixWord ++ tailWord_314605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314605).length < 2 ^ (prefixWord ++ tailWord_314605).sum := by decide
  have hdescent : baseEnd_314605 < baseStart_314605 := by decide
  rcases family_descends (prefixWord ++ tailWord_314605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314622 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_314622 : Nat := 118140960795 + 314622 * 2 ^ 59
def prefixEnd_314622 : Nat := 4983230072969 + 3 ^ 40 * 314622 * 2
def baseEnd_314622 : Nat := 143602053759087354380521

theorem tailTrace_314622 : CollatzResearch.WordTrace tailWord_314622 prefixEnd_314622 143602053759087354380521 := by
  unfold tailWord_314622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434400883273212750599265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7650138044123801336529413 1434400883273212750599265)
  ·
    refine ⟨1075800662454909562949449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1434400883273212750599265 1075800662454909562949449)
    ·
      refine ⟨806850496841182172212087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075800662454909562949449 806850496841182172212087)
      ·
        refine ⟨1210275745261773258318131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806850496841182172212087 1210275745261773258318131)
        ·
          refine ⟨1815413617892659887477197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210275745261773258318131 1815413617892659887477197)
          ·
            refine ⟨680780106709747457803949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1815413617892659887477197 680780106709747457803949)
            ·
              refine ⟨255292540016155296676481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680780106709747457803949 255292540016155296676481)
              ·
                refine ⟨191469405012116472507361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255292540016155296676481 191469405012116472507361)
                ·
                  refine ⟨143602053759087354380521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191469405012116472507361 143602053759087354380521)
                  ·
                    rfl

theorem cell20_314622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_314622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314622 prefixEnd_314622 := by exact prefixLift 314622
  have htrace : WordTrace (prefixWord ++ tailWord_314622) baseStart_314622 baseEnd_314622 := by
    simpa [prefixWord, tailWord_314622, baseEnd_314622] using wordTrace_append hprefix tailTrace_314622
  have hstable : (prefixWord ++ tailWord_314622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314622).length < 2 ^ (prefixWord ++ tailWord_314622).sum := by decide
  have hdescent : baseEnd_314622 < baseStart_314622 := by decide
  rcases family_descends (prefixWord ++ tailWord_314622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314623 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_314623 : Nat := 118140960795 + 314623 * 2 ^ 59
def prefixEnd_314623 : Nat := 4983230072969 + 3 ^ 40 * 314623 * 2
def baseEnd_314623 : Nat := 143602510186335795347183

theorem tailTrace_314623 : CollatzResearch.WordTrace tailWord_314623 prefixEnd_314623 143602510186335795347183 := by
  unfold tailWord_314623
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475243539182079175580523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7650162359454719450387015 11475243539182079175580523)
  ·
    refine ⟨17212865308773118763370785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11475243539182079175580523 17212865308773118763370785)
    ·
      refine ⟨12909648981579839072528089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17212865308773118763370785 12909648981579839072528089)
      ·
        refine ⟨9682236736184879304396067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12909648981579839072528089 9682236736184879304396067)
        ·
          refine ⟨14523355104277318956594101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9682236736184879304396067 14523355104277318956594101)
          ·
            refine ⟨1361564541025998652180697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14523355104277318956594101 1361564541025998652180697)
            ·
              refine ⟨1021173405769498989135523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361564541025998652180697 1021173405769498989135523)
              ·
                refine ⟨1531760108654248483703285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021173405769498989135523 1531760108654248483703285)
                ·
                  refine ⟨143602510186335795347183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1531760108654248483703285 143602510186335795347183)
                  ·
                    rfl

theorem cell20_314623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_314623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314623 prefixEnd_314623 := by exact prefixLift 314623
  have htrace : WordTrace (prefixWord ++ tailWord_314623) baseStart_314623 baseEnd_314623 := by
    simpa [prefixWord, tailWord_314623, baseEnd_314623] using wordTrace_append hprefix tailTrace_314623
  have hstable : (prefixWord ++ tailWord_314623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314623).length < 2 ^ (prefixWord ++ tailWord_314623).sum := by decide
  have hdescent : baseEnd_314623 < baseStart_314623 := by decide
  rcases family_descends (prefixWord ++ tailWord_314623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314675 : List Nat := [1, 1, 1, 2, 5, 10]
def baseStart_314675 : Nat := 118140960795 + 314675 * 2 ^ 59
def prefixEnd_314675 : Nat := 4983230072969 + 3 ^ 40 * 314675 * 2
def baseEnd_314675 : Nat := 5319490533453878726431

theorem tailTrace_314675 : CollatzResearch.WordTrace tailWord_314675 prefixEnd_314675 5319490533453878726431 := by
  unfold tailWord_314675
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477140134993692056473479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7651426756662461370982319 11477140134993692056473479)
  ·
    refine ⟨17215710202490538084710219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11477140134993692056473479 17215710202490538084710219)
    ·
      refine ⟨25823565303735807127065329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17215710202490538084710219 25823565303735807127065329)
      ·
        refine ⟨19367673977801855345298997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25823565303735807127065329 19367673977801855345298997)
        ·
          refine ⟨1815719435418923938621781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19367673977801855345298997 1815719435418923938621781)
          ·
            refine ⟨5319490533453878726431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1815719435418923938621781 5319490533453878726431)
            ·
              rfl

theorem cell20_314675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 10].length) (baseStart_314675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314675 prefixEnd_314675 := by exact prefixLift 314675
  have htrace : WordTrace (prefixWord ++ tailWord_314675) baseStart_314675 baseEnd_314675 := by
    simpa [prefixWord, tailWord_314675, baseEnd_314675] using wordTrace_append hprefix tailTrace_314675
  have hstable : (prefixWord ++ tailWord_314675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314675).length < 2 ^ (prefixWord ++ tailWord_314675).sum := by decide
  have hdescent : baseEnd_314675 < baseStart_314675 := by decide
  rcases family_descends (prefixWord ++ tailWord_314675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314681 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 2]
def baseStart_314681 : Nat := 118140960795 + 314681 * 2 ^ 59
def prefixEnd_314681 : Nat := 4983230072969 + 3 ^ 40 * 314681 * 2
def baseEnd_314681 : Nat := 143628982966745371413613

theorem tailTrace_314681 : CollatzResearch.WordTrace tailWord_314681 prefixEnd_314681 143628982966745371413613 := by
  unfold tailWord_314681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477358972971955081191897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7651572648647970054127931 11477358972971955081191897)
  ·
    refine ⟨8608019229728966310893923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11477358972971955081191897 8608019229728966310893923)
    ·
      refine ⟨12912028844593449466340885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8608019229728966310893923 12912028844593449466340885)
      ·
        refine ⟨605251352090317943734729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12912028844593449466340885 605251352090317943734729)
        ·
          refine ⟨453938514067738457801047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605251352090317943734729 453938514067738457801047)
          ·
            refine ⟨680907771101607686701571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453938514067738457801047 680907771101607686701571)
            ·
              refine ⟨1021361656652411530052357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680907771101607686701571 1021361656652411530052357)
              ·
                refine ⟨191505310622327161884817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1021361656652411530052357 191505310622327161884817)
                ·
                  refine ⟨143628982966745371413613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191505310622327161884817 143628982966745371413613)
                  ·
                    rfl

theorem cell20_314681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_314681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314681 prefixEnd_314681 := by exact prefixLift 314681
  have htrace : WordTrace (prefixWord ++ tailWord_314681) baseStart_314681 baseEnd_314681 := by
    simpa [prefixWord, tailWord_314681, baseEnd_314681] using wordTrace_append hprefix tailTrace_314681
  have hstable : (prefixWord ++ tailWord_314681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314681).length < 2 ^ (prefixWord ++ tailWord_314681).sum := by decide
  have hdescent : baseEnd_314681 < baseStart_314681 := by decide
  rcases family_descends (prefixWord ++ tailWord_314681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314709 : List Nat := [1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_314709 : Nat := 118140960795 + 314709 * 2 ^ 59
def prefixEnd_314709 : Nat := 4983230072969 + 3 ^ 40 * 314709 * 2
def baseEnd_314709 : Nat := 47880587643233906160055

theorem tailTrace_314709 : CollatzResearch.WordTrace tailWord_314709 prefixEnd_314709 47880587643233906160055 := by
  unfold tailWord_314709
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478380216870515863211181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7652253477913677242140787 11478380216870515863211181)
  ·
    refine ⟨4304392581326443448704193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11478380216870515863211181 4304392581326443448704193)
    ·
      refine ⟨3228294435994832586528145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4304392581326443448704193 3228294435994832586528145)
      ·
        refine ⟨2421220826996124439896109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3228294435994832586528145 2421220826996124439896109)
        ·
          refine ⟨907957810123546664961041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2421220826996124439896109 907957810123546664961041)
          ·
            refine ⟨680968357592659998720781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907957810123546664961041 680968357592659998720781)
            ·
              refine ⟨255363134097247499520293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680968357592659998720781 255363134097247499520293)
              ·
                refine ⟨47880587643233906160055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255363134097247499520293 47880587643233906160055)
                ·
                  rfl

theorem cell20_314709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_314709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314709 prefixEnd_314709 := by exact prefixLift 314709
  have htrace : WordTrace (prefixWord ++ tailWord_314709) baseStart_314709 baseEnd_314709 := by
    simpa [prefixWord, tailWord_314709, baseEnd_314709] using wordTrace_append hprefix tailTrace_314709
  have hstable : (prefixWord ++ tailWord_314709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314709).length < 2 ^ (prefixWord ++ tailWord_314709).sum := by decide
  have hdescent : baseEnd_314709 < baseStart_314709 := by decide
  rcases family_descends (prefixWord ++ tailWord_314709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314713 : List Nat := [1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_314713 : Nat := 118140960795 + 314713 * 2 ^ 59
def prefixEnd_314713 : Nat := 4983230072969 + 3 ^ 40 * 314713 * 2
def baseEnd_314713 : Nat := 47881196212898494115605

theorem tailTrace_314713 : CollatzResearch.WordTrace tailWord_314713 prefixEnd_314713 47881196212898494115605 := by
  unfold tailWord_314713
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478526108856024546356793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7652350739237349697571195 11478526108856024546356793)
  ·
    refine ⟨8608894581642018409767595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11478526108856024546356793 8608894581642018409767595)
    ·
      refine ⟨12913341872463027614651393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8608894581642018409767595 12913341872463027614651393)
      ·
        refine ⟨9685006404347270710988545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12913341872463027614651393 9685006404347270710988545)
        ·
          refine ⟨7263754803260453033241409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9685006404347270710988545 7263754803260453033241409)
          ·
            refine ⟨5447816102445339774931057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7263754803260453033241409 5447816102445339774931057)
            ·
              refine ⟨4085862076834004831198293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5447816102445339774931057 4085862076834004831198293)
              ·
                refine ⟨47881196212898494115605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4085862076834004831198293 47881196212898494115605)
                ·
                  rfl

theorem cell20_314713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_314713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314713 prefixEnd_314713 := by exact prefixLift 314713
  have htrace : WordTrace (prefixWord ++ tailWord_314713) baseStart_314713 baseEnd_314713 := by
    simpa [prefixWord, tailWord_314713, baseEnd_314713] using wordTrace_append hprefix tailTrace_314713
  have hstable : (prefixWord ++ tailWord_314713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314713).length < 2 ^ (prefixWord ++ tailWord_314713).sum := by decide
  have hdescent : baseEnd_314713 < baseStart_314713 := by decide
  rcases family_descends (prefixWord ++ tailWord_314713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314733 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_314733 : Nat := 118140960795 + 314733 * 2 ^ 59
def prefixEnd_314733 : Nat := 4983230072969 + 3 ^ 40 * 314733 * 2
def baseEnd_314733 : Nat := 143652717183664301680067

theorem tailTrace_314733 : CollatzResearch.WordTrace tailWord_314733 prefixEnd_314733 143652717183664301680067 := by
  unfold tailWord_314733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11479255568783567962084853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7652837045855711974723235 11479255568783567962084853)
  ·
    refine ⟨1076180209573459496445455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11479255568783567962084853 1076180209573459496445455)
    ·
      refine ⟨1614270314360189244668183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076180209573459496445455 1614270314360189244668183)
      ·
        refine ⟨2421405471540283867002275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614270314360189244668183 2421405471540283867002275)
        ·
          refine ⟨3632108207310425800503413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2421405471540283867002275 3632108207310425800503413)
          ·
            refine ⟨340510144435352418797195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3632108207310425800503413 340510144435352418797195)
            ·
              refine ⟨510765216653028628195793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340510144435352418797195 510765216653028628195793)
              ·
                refine ⟨383073912489771471146845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510765216653028628195793 383073912489771471146845)
                ·
                  refine ⟨143652717183664301680067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383073912489771471146845 143652717183664301680067)
                  ·
                    rfl

theorem cell20_314733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_314733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314733 prefixEnd_314733 := by exact prefixLift 314733
  have htrace : WordTrace (prefixWord ++ tailWord_314733) baseStart_314733 baseEnd_314733 := by
    simpa [prefixWord, tailWord_314733, baseEnd_314733] using wordTrace_append hprefix tailTrace_314733
  have hstable : (prefixWord ++ tailWord_314733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314733).length < 2 ^ (prefixWord ++ tailWord_314733).sum := by decide
  have hdescent : baseEnd_314733 < baseStart_314733 := by decide
  rcases family_descends (prefixWord ++ tailWord_314733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314799 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 2]
def baseStart_314799 : Nat := 118140960795 + 314799 * 2 ^ 59
def prefixEnd_314799 : Nat := 4983230072969 + 3 ^ 40 * 314799 * 2
def baseEnd_314799 : Nat := 143682841382061405479797

theorem tailTrace_314799 : CollatzResearch.WordTrace tailWord_314799 prefixEnd_314799 143682841382061405479797 := by
  unfold tailWord_314799
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481662786544461233987451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7654441857696307489324967 11481662786544461233987451)
  ·
    refine ⟨17222494179816691850981177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11481662786544461233987451 17222494179816691850981177)
    ·
      refine ⟨12916870634862518888235883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17222494179816691850981177 12916870634862518888235883)
      ·
        refine ⟨19375305952293778332353825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12916870634862518888235883 19375305952293778332353825)
        ·
          refine ⟨14531479464220333749265369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19375305952293778332353825 14531479464220333749265369)
          ·
            refine ⟨10898609598165250311949027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14531479464220333749265369 10898609598165250311949027)
            ·
              refine ⟨16347914397247875467923541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10898609598165250311949027 16347914397247875467923541)
              ·
                refine ⟨191577121842748540639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 16347914397247875467923541 191577121842748540639729)
                ·
                  refine ⟨143682841382061405479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191577121842748540639729 143682841382061405479797)
                  ·
                    rfl

theorem cell20_314799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2].length) (baseStart_314799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314799 prefixEnd_314799 := by exact prefixLift 314799
  have htrace : WordTrace (prefixWord ++ tailWord_314799) baseStart_314799 baseEnd_314799 := by
    simpa [prefixWord, tailWord_314799, baseEnd_314799] using wordTrace_append hprefix tailTrace_314799
  have hstable : (prefixWord ++ tailWord_314799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314799).length < 2 ^ (prefixWord ++ tailWord_314799).sum := by decide
  have hdescent : baseEnd_314799 < baseStart_314799 := by decide
  rcases family_descends (prefixWord ++ tailWord_314799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314827 : List Nat := [1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_314827 : Nat := 118140960795 + 314827 * 2 ^ 59
def prefixEnd_314827 : Nat := 4983230072969 + 3 ^ 40 * 314827 * 2
def baseEnd_314827 : Nat := 47898540448339250848783

theorem tailTrace_314827 : CollatzResearch.WordTrace tailWord_314827 prefixEnd_314827 47898540448339250848783 := by
  unfold tailWord_314827
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482684030443022016006735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7655122686962014677337823 11482684030443022016006735)
  ·
    refine ⟨17224026045664533024010103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11482684030443022016006735 17224026045664533024010103)
    ·
      refine ⟨25836039068496799536015155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17224026045664533024010103 25836039068496799536015155)
      ·
        refine ⟨38754058602745199304022733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25836039068496799536015155 38754058602745199304022733)
        ·
          refine ⟨14532771976029449739008525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38754058602745199304022733 14532771976029449739008525)
          ·
            refine ⟨5449789491011043652128197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14532771976029449739008525 5449789491011043652128197)
            ·
              refine ⟨1021835529564570684774037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5449789491011043652128197 1021835529564570684774037)
              ·
                refine ⟨47898540448339250848783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1021835529564570684774037 47898540448339250848783)
                ·
                  rfl

theorem cell20_314827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_314827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314827 prefixEnd_314827 := by exact prefixLift 314827
  have htrace : WordTrace (prefixWord ++ tailWord_314827) baseStart_314827 baseEnd_314827 := by
    simpa [prefixWord, tailWord_314827, baseEnd_314827] using wordTrace_append hprefix tailTrace_314827
  have hstable : (prefixWord ++ tailWord_314827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314827).length < 2 ^ (prefixWord ++ tailWord_314827).sum := by decide
  have hdescent : baseEnd_314827 < baseStart_314827 := by decide
  rcases family_descends (prefixWord ++ tailWord_314827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314913 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_314913 : Nat := 118140960795 + 314913 * 2 ^ 59
def prefixEnd_314913 : Nat := 4983230072969 + 3 ^ 40 * 314913 * 2
def baseEnd_314913 : Nat := 143734874088383675679331

theorem tailTrace_314913 : CollatzResearch.WordTrace tailWord_314913 prefixEnd_314913 143734874088383675679331 := by
  unfold tailWord_314913
  simp only [CollatzResearch.WordTrace]
  refine ⟨11485820708131458703637393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7657213805420972469091595 11485820708131458703637393)
  ·
    refine ⟨8614365531098594027728045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11485820708131458703637393 8614365531098594027728045)
    ·
      refine ⟨3230387074161972760398017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8614365531098594027728045 3230387074161972760398017)
      ·
        refine ⟨2422790305621479570298513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3230387074161972760398017 2422790305621479570298513)
        ·
          refine ⟨1817092729216109677723885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422790305621479570298513 1817092729216109677723885)
          ·
            refine ⟨681409773456041129146457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1817092729216109677723885 681409773456041129146457)
            ·
              refine ⟨511057330092030846859843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681409773456041129146457 511057330092030846859843)
              ·
                refine ⟨766585995138046270289765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511057330092030846859843 766585995138046270289765)
                ·
                  refine ⟨143734874088383675679331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 766585995138046270289765 143734874088383675679331)
                  ·
                    rfl

theorem cell20_314913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_314913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314913 prefixEnd_314913 := by exact prefixLift 314913
  have htrace : WordTrace (prefixWord ++ tailWord_314913) baseStart_314913 baseEnd_314913 := by
    simpa [prefixWord, tailWord_314913, baseEnd_314913] using wordTrace_append hprefix tailTrace_314913
  have hstable : (prefixWord ++ tailWord_314913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314913).length < 2 ^ (prefixWord ++ tailWord_314913).sum := by decide
  have hdescent : baseEnd_314913 < baseStart_314913 := by decide
  rcases family_descends (prefixWord ++ tailWord_314913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314937 : List Nat := [1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_314937 : Nat := 118140960795 + 314937 * 2 ^ 59
def prefixEnd_314937 : Nat := 4983230072969 + 3 ^ 40 * 314937 * 2
def baseEnd_314937 : Nat := 47915276114115419626411

theorem tailTrace_314937 : CollatzResearch.WordTrace tailWord_314937 prefixEnd_314937 47915276114115419626411 := by
  unfold tailWord_314937
  simp only [CollatzResearch.WordTrace]
  refine ⟨11486696060044510802511065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7657797373363007201674043 11486696060044510802511065)
  ·
    refine ⟨8615022045033383101883299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11486696060044510802511065 8615022045033383101883299)
    ·
      refine ⟨12922533067550074652824949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615022045033383101883299 12922533067550074652824949)
      ·
        refine ⟨1211487475082819498702339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12922533067550074652824949 1211487475082819498702339)
        ·
          refine ⟨1817231212624229248053509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211487475082819498702339 1817231212624229248053509)
          ·
            refine ⟨340730852367042984010033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1817231212624229248053509 340730852367042984010033)
            ·
              refine ⟨255548139275282238007525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340730852367042984010033 255548139275282238007525)
              ·
                refine ⟨47915276114115419626411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255548139275282238007525 47915276114115419626411)
                ·
                  rfl

theorem cell20_314937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_314937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314937 prefixEnd_314937 := by exact prefixLift 314937
  have htrace : WordTrace (prefixWord ++ tailWord_314937) baseStart_314937 baseEnd_314937 := by
    simpa [prefixWord, tailWord_314937, baseEnd_314937] using wordTrace_append hprefix tailTrace_314937
  have hstable : (prefixWord ++ tailWord_314937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314937).length < 2 ^ (prefixWord ++ tailWord_314937).sum := by decide
  have hdescent : baseEnd_314937 < baseStart_314937 := by decide
  rcases family_descends (prefixWord ++ tailWord_314937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314965 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_314965 : Nat := 118140960795 + 314965 * 2 ^ 59
def prefixEnd_314965 : Nat := 4983230072969 + 3 ^ 40 * 314965 * 2
def baseEnd_314965 : Nat := 143758608305302605945785

theorem tailTrace_314965 : CollatzResearch.WordTrace tailWord_314965 prefixEnd_314965 143758608305302605945785 := by
  unfold tailWord_314965
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487717303943071584530349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7658478202628714389686899 11487717303943071584530349)
  ·
    refine ⟨4307893988978651844198881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11487717303943071584530349 4307893988978651844198881)
    ·
      refine ⟨3230920491733988883149161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4307893988978651844198881 3230920491733988883149161)
      ·
        refine ⟨2423190368800491662361871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3230920491733988883149161 2423190368800491662361871)
        ·
          refine ⟨3634785553200737493542807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423190368800491662361871 3634785553200737493542807)
          ·
            refine ⟨5452178329801106240314211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634785553200737493542807 5452178329801106240314211)
            ·
              refine ⟨8178267494701659360471317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452178329801106240314211 8178267494701659360471317)
              ·
                refine ⟨383356288814140282522093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8178267494701659360471317 383356288814140282522093)
                ·
                  refine ⟨143758608305302605945785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383356288814140282522093 143758608305302605945785)
                  ·
                    rfl

theorem cell20_314965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_314965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314965 prefixEnd_314965 := by exact prefixLift 314965
  have htrace : WordTrace (prefixWord ++ tailWord_314965) baseStart_314965 baseEnd_314965 := by
    simpa [prefixWord, tailWord_314965, baseEnd_314965] using wordTrace_append hprefix tailTrace_314965
  have hstable : (prefixWord ++ tailWord_314965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314965).length < 2 ^ (prefixWord ++ tailWord_314965).sum := by decide
  have hdescent : baseEnd_314965 < baseStart_314965 := by decide
  rcases family_descends (prefixWord ++ tailWord_314965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314979 : List Nat := [1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_314979 : Nat := 118140960795 + 314979 * 2 ^ 59
def prefixEnd_314979 : Nat := 4983230072969 + 3 ^ 40 * 314979 * 2
def baseEnd_314979 : Nat := 47921666095593593159687

theorem tailTrace_314979 : CollatzResearch.WordTrace tailWord_314979 prefixEnd_314979 47921666095593593159687 := by
  unfold tailWord_314979
  simp only [CollatzResearch.WordTrace]
  refine ⟨11488227925892351975539991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7658818617261567983693327 11488227925892351975539991)
  ·
    refine ⟨17232341888838527963309987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11488227925892351975539991 17232341888838527963309987)
    ·
      refine ⟨25848512833257791944964981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17232341888838527963309987 25848512833257791944964981)
      ·
        refine ⟨2423298078117917994840467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25848512833257791944964981 2423298078117917994840467)
        ·
          refine ⟨3634947117176876992260701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423298078117917994840467 3634947117176876992260701)
          ·
            refine ⟨1363105168941328872097763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3634947117176876992260701 1363105168941328872097763)
            ·
              refine ⟨2044657753411993308146645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363105168941328872097763 2044657753411993308146645)
              ·
                refine ⟨47921666095593593159687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2044657753411993308146645 47921666095593593159687)
                ·
                  rfl

theorem cell20_314979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_314979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_314979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_314979 prefixEnd_314979 := by exact prefixLift 314979
  have htrace : WordTrace (prefixWord ++ tailWord_314979) baseStart_314979 baseEnd_314979 := by
    simpa [prefixWord, tailWord_314979, baseEnd_314979] using wordTrace_append hprefix tailTrace_314979
  have hstable : (prefixWord ++ tailWord_314979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314979).length < 2 ^ (prefixWord ++ tailWord_314979).sum := by decide
  have hdescent : baseEnd_314979 < baseStart_314979 := by decide
  rcases family_descends (prefixWord ++ tailWord_314979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315024 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_315024 : Nat := 118140960795 + 315024 * 2 ^ 59
def prefixEnd_315024 : Nat := 4983230072969 + 3 ^ 40 * 315024 * 2
def baseEnd_315024 : Nat := 143785537512960622978877

theorem tailTrace_315024 : CollatzResearch.WordTrace tailWord_315024 prefixEnd_315024 143785537512960622978877 := by
  unfold tailWord_315024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744934605364662330464063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7659912807152883107285417 5744934605364662330464063)
  ·
    refine ⟨8617401908046993495696095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5744934605364662330464063 8617401908046993495696095)
    ·
      refine ⟨12926102862070490243544143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8617401908046993495696095 12926102862070490243544143)
      ·
        refine ⟨19389154293105735365316215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12926102862070490243544143 19389154293105735365316215)
        ·
          refine ⟨29083731439658603047974323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19389154293105735365316215 29083731439658603047974323)
          ·
            refine ⟨43625597159487904571961485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29083731439658603047974323 43625597159487904571961485)
            ·
              refine ⟨16359598934807964214485557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43625597159487904571961485 16359598934807964214485557)
              ·
                refine ⟨1533712400138246645108021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16359598934807964214485557 1533712400138246645108021)
                ·
                  refine ⟨143785537512960622978877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1533712400138246645108021 143785537512960622978877)
                  ·
                    rfl

theorem cell20_315024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_315024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315024 prefixEnd_315024 := by exact prefixLift 315024
  have htrace : WordTrace (prefixWord ++ tailWord_315024) baseStart_315024 baseEnd_315024 := by
    simpa [prefixWord, tailWord_315024, baseEnd_315024] using wordTrace_append hprefix tailTrace_315024
  have hstable : (prefixWord ++ tailWord_315024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315024).length < 2 ^ (prefixWord ++ tailWord_315024).sum := by decide
  have hdescent : baseEnd_315024 < baseStart_315024 := by decide
  rcases family_descends (prefixWord ++ tailWord_315024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315061 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 2]
def baseStart_315061 : Nat := 118140960795 + 315061 * 2 ^ 59
def prefixEnd_315061 : Nat := 4983230072969 + 3 ^ 40 * 315061 * 2
def baseEnd_315061 : Nat := 143802425321152938745393

theorem tailTrace_315061 : CollatzResearch.WordTrace tailWord_315061 prefixEnd_315061 143802425321152938745393 := by
  unfold tailWord_315061
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491218711595279980025037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7660812474396853320016691 11491218711595279980025037)
  ·
    refine ⟨4309207016848229992509389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11491218711595279980025037 4309207016848229992509389)
    ·
      refine ⟨1615952631318086247191021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4309207016848229992509389 1615952631318086247191021)
      ·
        refine ⟨605982236744282342696633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1615952631318086247191021 605982236744282342696633)
        ·
          refine ⟨454486677558211757022475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605982236744282342696633 454486677558211757022475)
          ·
            refine ⟨681730016337317635533713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454486677558211757022475 681730016337317635533713)
            ·
              refine ⟨511297512252988226650285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681730016337317635533713 511297512252988226650285)
              ·
                refine ⟨191736567094870584993857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511297512252988226650285 191736567094870584993857)
                ·
                  refine ⟨143802425321152938745393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191736567094870584993857 143802425321152938745393)
                  ·
                    rfl

theorem cell20_315061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_315061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315061 prefixEnd_315061 := by exact prefixLift 315061
  have htrace : WordTrace (prefixWord ++ tailWord_315061) baseStart_315061 baseEnd_315061 := by
    simpa [prefixWord, tailWord_315061, baseEnd_315061] using wordTrace_append hprefix tailTrace_315061
  have hstable : (prefixWord ++ tailWord_315061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315061).length < 2 ^ (prefixWord ++ tailWord_315061).sum := by decide
  have hdescent : baseEnd_315061 < baseStart_315061 := by decide
  rcases family_descends (prefixWord ++ tailWord_315061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315065 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 2]
def baseStart_315065 : Nat := 118140960795 + 315065 * 2 ^ 59
def prefixEnd_315065 : Nat := 4983230072969 + 3 ^ 40 * 315065 * 2
def baseEnd_315065 : Nat := 143804251030146702612043

theorem tailTrace_315065 : CollatzResearch.WordTrace tailWord_315065 prefixEnd_315065 143804251030146702612043 := by
  unfold tailWord_315065
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491364603580788663170649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7660909735720525775447099 11491364603580788663170649)
  ·
    refine ⟨8618523452685591497377987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11491364603580788663170649 8618523452685591497377987)
    ·
      refine ⟨12927785179028387246066981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618523452685591497377987 12927785179028387246066981)
      ·
        refine ⟨2423959721067822608637559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12927785179028387246066981 2423959721067822608637559)
        ·
          refine ⟨3635939581601733912956339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423959721067822608637559 3635939581601733912956339)
          ·
            refine ⟨5453909372402600869434509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635939581601733912956339 5453909372402600869434509)
            ·
              refine ⟨2045216014650975326037941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5453909372402600869434509 2045216014650975326037941)
              ·
                refine ⟨191739001373528936816057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2045216014650975326037941 191739001373528936816057)
                ·
                  refine ⟨143804251030146702612043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191739001373528936816057 143804251030146702612043)
                  ·
                    rfl

theorem cell20_315065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_315065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315065 prefixEnd_315065 := by exact prefixLift 315065
  have htrace : WordTrace (prefixWord ++ tailWord_315065) baseStart_315065 baseEnd_315065 := by
    simpa [prefixWord, tailWord_315065, baseEnd_315065] using wordTrace_append hprefix tailTrace_315065
  have hstable : (prefixWord ++ tailWord_315065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315065).length < 2 ^ (prefixWord ++ tailWord_315065).sum := by decide
  have hdescent : baseEnd_315065 < baseStart_315065 := by decide
  rcases family_descends (prefixWord ++ tailWord_315065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315078 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_315078 : Nat := 118140960795 + 315078 * 2 ^ 59
def prefixEnd_315078 : Nat := 4983230072969 + 3 ^ 40 * 315078 * 2
def baseEnd_315078 : Nat := 143810184584376435178657

theorem tailTrace_315078 : CollatzResearch.WordTrace tailWord_315078 prefixEnd_315078 143810184584376435178657 := by
  unfold tailWord_315078
  simp only [CollatzResearch.WordTrace]
  refine ⟨359119961016677871356059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7661225835022461255595925 359119961016677871356059)
  ·
    refine ⟨538679941525016807034089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359119961016677871356059 538679941525016807034089)
    ·
      refine ⟨404009956143762605275567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 538679941525016807034089 404009956143762605275567)
      ·
        refine ⟨606014934215643907913351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404009956143762605275567 606014934215643907913351)
        ·
          refine ⟨909022401323465861870027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606014934215643907913351 909022401323465861870027)
          ·
            refine ⟨1363533601985198792805041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909022401323465861870027 1363533601985198792805041)
            ·
              refine ⟨1022650201488899094603781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363533601985198792805041 1022650201488899094603781)
              ·
                refine ⟨191746912779168580238209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1022650201488899094603781 191746912779168580238209)
                ·
                  refine ⟨143810184584376435178657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191746912779168580238209 143810184584376435178657)
                  ·
                    rfl

theorem cell20_315078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_315078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315078 prefixEnd_315078 := by exact prefixLift 315078
  have htrace : WordTrace (prefixWord ++ tailWord_315078) baseStart_315078 baseEnd_315078 := by
    simpa [prefixWord, tailWord_315078, baseEnd_315078] using wordTrace_append hprefix tailTrace_315078
  have hstable : (prefixWord ++ tailWord_315078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315078).length < 2 ^ (prefixWord ++ tailWord_315078).sum := by decide
  have hdescent : baseEnd_315078 < baseStart_315078 := by decide
  rcases family_descends (prefixWord ++ tailWord_315078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315096 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_315096 : Nat := 118140960795 + 315096 * 2 ^ 59
def prefixEnd_315096 : Nat := 4983230072969 + 3 ^ 40 * 315096 * 2
def baseEnd_315096 : Nat := 143818400274848372578583

theorem tailTrace_315096 : CollatzResearch.WordTrace tailWord_315096 prefixEnd_315096 143818400274848372578583 := by
  unfold tailWord_315096
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746247633234240478774571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7661663510978987305032761 5746247633234240478774571)
  ·
    refine ⟨8619371449851360718161857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5746247633234240478774571 8619371449851360718161857)
    ·
      refine ⟨6464528587388520538621393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8619371449851360718161857 6464528587388520538621393)
      ·
        refine ⟨4848396440541390403966045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6464528587388520538621393 4848396440541390403966045)
        ·
          refine ⟨1818148665203021401487267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4848396440541390403966045 1818148665203021401487267)
          ·
            refine ⟨2727222997804532102230901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818148665203021401487267 2727222997804532102230901)
            ·
              refine ⟨255677156044174884584147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2727222997804532102230901 255677156044174884584147)
              ·
                refine ⟨383515734066262326876221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255677156044174884584147 383515734066262326876221)
                ·
                  refine ⟨143818400274848372578583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383515734066262326876221 143818400274848372578583)
                  ·
                    rfl

theorem cell20_315096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_315096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315096 prefixEnd_315096 := by exact prefixLift 315096
  have htrace : WordTrace (prefixWord ++ tailWord_315096) baseStart_315096 baseEnd_315096 := by
    simpa [prefixWord, tailWord_315096, baseEnd_315096] using wordTrace_append hprefix tailTrace_315096
  have hstable : (prefixWord ++ tailWord_315096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315096).length < 2 ^ (prefixWord ++ tailWord_315096).sum := by decide
  have hdescent : baseEnd_315096 < baseStart_315096 := by decide
  rcases family_descends (prefixWord ++ tailWord_315096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315117 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_315117 : Nat := 118140960795 + 315117 * 2 ^ 59
def prefixEnd_315117 : Nat := 4983230072969 + 3 ^ 40 * 315117 * 2
def baseEnd_315117 : Nat := 143827985247065632878497

theorem tailTrace_315117 : CollatzResearch.WordTrace tailWord_315117 prefixEnd_315117 143827985247065632878497 := by
  unfold tailWord_315117
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493261199392401544063605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7662174132928267696042403 11493261199392401544063605)
  ·
    refine ⟨1077493237443037644755963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11493261199392401544063605 1077493237443037644755963)
    ·
      refine ⟨1616239856164556467133945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1077493237443037644755963 1616239856164556467133945)
      ·
        refine ⟨1212179892123417350350459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1616239856164556467133945 1212179892123417350350459)
        ·
          refine ⟨1818269838185126025525689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212179892123417350350459 1818269838185126025525689)
          ·
            refine ⟨1363702378638844519144267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818269838185126025525689 1363702378638844519144267)
            ·
              refine ⟨2045553567958266778716401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363702378638844519144267 2045553567958266778716401)
              ·
                refine ⟨1534165175968700084037301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045553567958266778716401 1534165175968700084037301)
                ·
                  refine ⟨143827985247065632878497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1534165175968700084037301 143827985247065632878497)
                  ·
                    rfl

theorem cell20_315117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_315117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315117 prefixEnd_315117 := by exact prefixLift 315117
  have htrace : WordTrace (prefixWord ++ tailWord_315117) baseStart_315117 baseEnd_315117 := by
    simpa [prefixWord, tailWord_315117, baseEnd_315117] using wordTrace_append hprefix tailTrace_315117
  have hstable : (prefixWord ++ tailWord_315117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315117).length < 2 ^ (prefixWord ++ tailWord_315117).sum := by decide
  have hdescent : baseEnd_315117 < baseStart_315117 := by decide
  rcases family_descends (prefixWord ++ tailWord_315117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315169 : List Nat := [1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_315169 : Nat := 118140960795 + 315169 * 2 ^ 59
def prefixEnd_315169 : Nat := 4983230072969 + 3 ^ 40 * 315169 * 2
def baseEnd_315169 : Nat := 47950573154661521048317

theorem tailTrace_315169 : CollatzResearch.WordTrace tailWord_315169 prefixEnd_315169 47950573154661521048317 := by
  unfold tailWord_315169
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495157795204014424956561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7663438530136009616637707 11495157795204014424956561)
  ·
    refine ⟨8621368346403010818717421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11495157795204014424956561 8621368346403010818717421)
    ·
      refine ⟨3233013129901129057019033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8621368346403010818717421 3233013129901129057019033)
      ·
        refine ⟨2424759847425846792764275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3233013129901129057019033 2424759847425846792764275)
        ·
          refine ⟨3637139771138770189146413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424759847425846792764275 3637139771138770189146413)
          ·
            refine ⟨1363927414177038820929905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3637139771138770189146413 1363927414177038820929905)
            ·
              refine ⟨1022945560632779115697429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363927414177038820929905 1022945560632779115697429)
              ·
                refine ⟨47950573154661521048317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1022945560632779115697429 47950573154661521048317)
                ·
                  rfl

theorem cell20_315169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_315169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315169 prefixEnd_315169 := by exact prefixLift 315169
  have htrace : WordTrace (prefixWord ++ tailWord_315169) baseStart_315169 baseEnd_315169 := by
    simpa [prefixWord, tailWord_315169, baseEnd_315169] using wordTrace_append hprefix tailTrace_315169
  have hstable : (prefixWord ++ tailWord_315169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315169).length < 2 ^ (prefixWord ++ tailWord_315169).sum := by decide
  have hdescent : baseEnd_315169 < baseStart_315169 := by decide
  rcases family_descends (prefixWord ++ tailWord_315169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315183 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_315183 : Nat := 118140960795 + 315183 * 2 ^ 59
def prefixEnd_315183 : Nat := 4983230072969 + 3 ^ 40 * 315183 * 2
def baseEnd_315183 : Nat := 143858109445462736678227

theorem tailTrace_315183 : CollatzResearch.WordTrace tailWord_315183 prefixEnd_315183 143858109445462736678227 := by
  unfold tailWord_315183
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495668417153294815966203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7663778944768863210644135 11495668417153294815966203)
  ·
    refine ⟨17243502625729942223949305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11495668417153294815966203 17243502625729942223949305)
    ·
      refine ⟨12932626969297456667961979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17243502625729942223949305 12932626969297456667961979)
      ·
        refine ⟨19398940453946185001942969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12932626969297456667961979 19398940453946185001942969)
        ·
          refine ⟨14549205340459638751457227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19398940453946185001942969 14549205340459638751457227)
          ·
            refine ⟨21823808010689458127185841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14549205340459638751457227 21823808010689458127185841)
            ·
              refine ⟨16367856008017093595389381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21823808010689458127185841 16367856008017093595389381)
              ·
                refine ⟨3068973001503205049135509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16367856008017093595389381 3068973001503205049135509)
                ·
                  refine ⟨143858109445462736678227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3068973001503205049135509 143858109445462736678227)
                  ·
                    rfl

theorem cell20_315183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_315183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315183 prefixEnd_315183 := by exact prefixLift 315183
  have htrace : WordTrace (prefixWord ++ tailWord_315183) baseStart_315183 baseEnd_315183 := by
    simpa [prefixWord, tailWord_315183, baseEnd_315183] using wordTrace_append hprefix tailTrace_315183
  have hstable : (prefixWord ++ tailWord_315183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315183).length < 2 ^ (prefixWord ++ tailWord_315183).sum := by decide
  have hdescent : baseEnd_315183 < baseStart_315183 := by decide
  rcases family_descends (prefixWord ++ tailWord_315183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315196 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_315196 : Nat := 118140960795 + 315196 * 2 ^ 59
def prefixEnd_315196 : Nat := 4983230072969 + 3 ^ 40 * 315196 * 2
def baseEnd_315196 : Nat := 143864042999692469244841

theorem tailTrace_315196 : CollatzResearch.WordTrace tailWord_315196 prefixEnd_315196 143864042999692469244841 := by
  unfold tailWord_315196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748071283053099018094721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7664095044070798690792961 5748071283053099018094721)
  ·
    refine ⟨4311053462289824263571041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5748071283053099018094721 4311053462289824263571041)
    ·
      refine ⟨3233290096717368197678281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4311053462289824263571041 3233290096717368197678281)
      ·
        refine ⟨2424967572538026148258711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3233290096717368197678281 2424967572538026148258711)
        ·
          refine ⟨3637451358807039222388067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424967572538026148258711 3637451358807039222388067)
          ·
            refine ⟨5456177038210558833582101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637451358807039222388067 5456177038210558833582101)
            ·
              refine ⟨255758298666119945324161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5456177038210558833582101 255758298666119945324161)
              ·
                refine ⟨191818723999589958993121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255758298666119945324161 191818723999589958993121)
                ·
                  refine ⟨143864042999692469244841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191818723999589958993121 143864042999692469244841)
                  ·
                    rfl

theorem cell20_315196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_315196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315196 prefixEnd_315196 := by exact prefixLift 315196
  have htrace : WordTrace (prefixWord ++ tailWord_315196) baseStart_315196 baseEnd_315196 := by
    simpa [prefixWord, tailWord_315196, baseEnd_315196] using wordTrace_append hprefix tailTrace_315196
  have hstable : (prefixWord ++ tailWord_315196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315196).length < 2 ^ (prefixWord ++ tailWord_315196).sum := by decide
  have hdescent : baseEnd_315196 < baseStart_315196 := by decide
  rcases family_descends (prefixWord ++ tailWord_315196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315207 : List Nat := [1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_315207 : Nat := 118140960795 + 315207 * 2 ^ 59
def prefixEnd_315207 : Nat := 4983230072969 + 3 ^ 40 * 315207 * 2
def baseEnd_315207 : Nat := 47956354566475106626043

theorem tailTrace_315207 : CollatzResearch.WordTrace tailWord_315207 prefixEnd_315207 47956354566475106626043 := by
  unfold tailWord_315207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496543769066346914839875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7664362512710897943226583 11496543769066346914839875)
  ·
    refine ⟨17244815653599520372259813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11496543769066346914839875 17244815653599520372259813)
    ·
      refine ⟨3233402935049910069798715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17244815653599520372259813 3233402935049910069798715)
      ·
        refine ⟨4850104402574865104698073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233402935049910069798715 4850104402574865104698073)
        ·
          refine ⟨3637578301931148828523555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4850104402574865104698073 3637578301931148828523555)
          ·
            refine ⟨5456367452896723242785333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637578301931148828523555 5456367452896723242785333)
            ·
              refine ⟨511534448709067804011125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5456367452896723242785333 511534448709067804011125)
              ·
                refine ⟨47956354566475106626043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 511534448709067804011125 47956354566475106626043)
                ·
                  rfl

theorem cell20_315207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_315207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315207 prefixEnd_315207 := by exact prefixLift 315207
  have htrace : WordTrace (prefixWord ++ tailWord_315207) baseStart_315207 baseEnd_315207 := by
    simpa [prefixWord, tailWord_315207, baseEnd_315207] using wordTrace_append hprefix tailTrace_315207
  have hstable : (prefixWord ++ tailWord_315207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315207).length < 2 ^ (prefixWord ++ tailWord_315207).sum := by decide
  have hdescent : baseEnd_315207 < baseStart_315207 := by decide
  rcases family_descends (prefixWord ++ tailWord_315207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315214 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_315214 : Nat := 118140960795 + 315214 * 2 ^ 59
def prefixEnd_315214 : Nat := 4983230072969 + 3 ^ 40 * 315214 * 2
def baseEnd_315214 : Nat := 143872258690164406644767

theorem tailTrace_315214 : CollatzResearch.WordTrace tailWord_315214 prefixEnd_315214 143872258690164406644767 := by
  unfold tailWord_315214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437099885005123388793087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7664532720027324740229797 1437099885005123388793087)
  ·
    refine ⟨2155649827507685083189631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437099885005123388793087 2155649827507685083189631)
    ·
      refine ⟨3233474741261527624784447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155649827507685083189631 3233474741261527624784447)
      ·
        refine ⟨4850212111892291437176671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233474741261527624784447 4850212111892291437176671)
        ·
          refine ⟨7275318167838437155765007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850212111892291437176671 7275318167838437155765007)
          ·
            refine ⟨10912977251757655733647511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275318167838437155765007 10912977251757655733647511)
            ·
              refine ⟨16369465877636483600471267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10912977251757655733647511 16369465877636483600471267)
              ·
                refine ⟨24554198816454725400706901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16369465877636483600471267 24554198816454725400706901)
                ·
                  refine ⟨143872258690164406644767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24554198816454725400706901 143872258690164406644767)
                  ·
                    rfl

theorem cell20_315214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_315214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315214 prefixEnd_315214 := by exact prefixLift 315214
  have htrace : WordTrace (prefixWord ++ tailWord_315214) baseStart_315214 baseEnd_315214 := by
    simpa [prefixWord, tailWord_315214, baseEnd_315214] using wordTrace_append hprefix tailTrace_315214
  have hstable : (prefixWord ++ tailWord_315214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315214).length < 2 ^ (prefixWord ++ tailWord_315214).sum := by decide
  have hdescent : baseEnd_315214 < baseStart_315214 := by decide
  rcases family_descends (prefixWord ++ tailWord_315214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315234 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_315234 : Nat := 118140960795 + 315234 * 2 ^ 59
def prefixEnd_315234 : Nat := 4983230072969 + 3 ^ 40 * 315234 * 2
def baseEnd_315234 : Nat := 143881387235133225978019

theorem tailTrace_315234 : CollatzResearch.WordTrace tailWord_315234 prefixEnd_315234 143881387235133225978019 := by
  unfold tailWord_315234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874382134992132631518189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7665019026645687017381837 2874382134992132631518189)
  ·
    refine ⟨1077893300622049736819321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2874382134992132631518189 1077893300622049736819321)
    ·
      refine ⟨808419975466537302614491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1077893300622049736819321 808419975466537302614491)
      ·
        refine ⟨1212629963199805953921737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808419975466537302614491 1212629963199805953921737)
        ·
          refine ⟨909472472399854465441303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212629963199805953921737 909472472399854465441303)
          ·
            refine ⟨1364208708599781698161955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909472472399854465441303 1364208708599781698161955)
            ·
              refine ⟨2046313062899672547242933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364208708599781698161955 2046313062899672547242933)
              ·
                refine ⟨191841849646844301304025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2046313062899672547242933 191841849646844301304025)
                ·
                  refine ⟨143881387235133225978019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191841849646844301304025 143881387235133225978019)
                  ·
                    rfl

theorem cell20_315234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_315234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315234 prefixEnd_315234 := by exact prefixLift 315234
  have htrace : WordTrace (prefixWord ++ tailWord_315234) baseStart_315234 baseEnd_315234 := by
    simpa [prefixWord, tailWord_315234, baseEnd_315234] using wordTrace_append hprefix tailTrace_315234
  have hstable : (prefixWord ++ tailWord_315234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315234).length < 2 ^ (prefixWord ++ tailWord_315234).sum := by decide
  have hdescent : baseEnd_315234 < baseStart_315234 := by decide
  rcases family_descends (prefixWord ++ tailWord_315234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315321 : List Nat := [1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_315321 : Nat := 118140960795 + 315321 * 2 ^ 59
def prefixEnd_315321 : Nat := 4983230072969 + 3 ^ 40 * 315321 * 2
def baseEnd_315321 : Nat := 47973698801915863359221

theorem tailTrace_315321 : CollatzResearch.WordTrace tailWord_315321 prefixEnd_315321 47973698801915863359221 := by
  unfold tailWord_315321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11500701690653344384489817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7667134460435562922993211 11500701690653344384489817)
  ·
    refine ⟨8625526267990008288367363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11500701690653344384489817 8625526267990008288367363)
    ·
      refine ⟨12938289401985012432551045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8625526267990008288367363 12938289401985012432551045)
      ·
        refine ⟨2425929262872189831103321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12938289401985012432551045 2425929262872189831103321)
        ·
          refine ⟨1819446947154142373327491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2425929262872189831103321 1819446947154142373327491)
          ·
            refine ⟨2729170420731213559991237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819446947154142373327491 2729170420731213559991237)
            ·
              refine ⟨511719453887102542498357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2729170420731213559991237 511719453887102542498357)
              ·
                refine ⟨47973698801915863359221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 511719453887102542498357 47973698801915863359221)
                ·
                  rfl

theorem cell20_315321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_315321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315321 prefixEnd_315321 := by exact prefixLift 315321
  have htrace : WordTrace (prefixWord ++ tailWord_315321) baseStart_315321 baseEnd_315321 := by
    simpa [prefixWord, tailWord_315321, baseEnd_315321] using wordTrace_append hprefix tailTrace_315321
  have hstable : (prefixWord ++ tailWord_315321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315321).length < 2 ^ (prefixWord ++ tailWord_315321).sum := by decide
  have hdescent : baseEnd_315321 < baseStart_315321 := by decide
  rcases family_descends (prefixWord ++ tailWord_315321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315335 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_315335 : Nat := 118140960795 + 315335 * 2 ^ 59
def prefixEnd_315335 : Nat := 4983230072969 + 3 ^ 40 * 315335 * 2
def baseEnd_315335 : Nat := 143927486387225763610939

theorem tailTrace_315335 : CollatzResearch.WordTrace tailWord_315335 prefixEnd_315335 143927486387225763610939 := by
  unfold tailWord_315335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501212312602624775499459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7667474875068416516999639 11501212312602624775499459)
  ·
    refine ⟨17251818468903937163249189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11501212312602624775499459 17251818468903937163249189)
    ·
      refine ⟨3234715962919488218109223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17251818468903937163249189 3234715962919488218109223)
      ·
        refine ⟨4852073944379232327163835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234715962919488218109223 4852073944379232327163835)
        ·
          refine ⟨7278110916568848490745753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852073944379232327163835 7278110916568848490745753)
          ·
            refine ⟨5458583187426636368059315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7278110916568848490745753 5458583187426636368059315)
            ·
              refine ⟨8187874781139954552088973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458583187426636368059315 8187874781139954552088973)
              ·
                refine ⟨3070453042927482957033365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8187874781139954552088973 3070453042927482957033365)
                ·
                  refine ⟨143927486387225763610939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3070453042927482957033365 143927486387225763610939)
                  ·
                    rfl

theorem cell20_315335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_315335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315335 prefixEnd_315335 := by exact prefixLift 315335
  have htrace : WordTrace (prefixWord ++ tailWord_315335) baseStart_315335 baseEnd_315335 := by
    simpa [prefixWord, tailWord_315335, baseEnd_315335] using wordTrace_append hprefix tailTrace_315335
  have hstable : (prefixWord ++ tailWord_315335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315335).length < 2 ^ (prefixWord ++ tailWord_315335).sum := by decide
  have hdescent : baseEnd_315335 < baseStart_315335 := by decide
  rcases family_descends (prefixWord ++ tailWord_315335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315404 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_315404 : Nat := 118140960795 + 315404 * 2 ^ 59
def prefixEnd_315404 : Nat := 4983230072969 + 3 ^ 40 * 315404 * 2
def baseEnd_315404 : Nat := 143958979867368190310657

theorem tailTrace_315404 : CollatzResearch.WordTrace tailWord_315404 prefixEnd_315404 143958979867368190310657 := by
  unfold tailWord_315404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751864474676324779880633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7669152632901766373174177 5751864474676324779880633)
  ·
    refine ⟨4313898356007243584910475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5751864474676324779880633 4313898356007243584910475)
    ·
      refine ⟨6470847534010865377365713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313898356007243584910475 6470847534010865377365713)
      ·
        refine ⟨4853135650508149033024285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6470847534010865377365713 4853135650508149033024285)
        ·
          refine ⟨1819925868940555887384107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4853135650508149033024285 1819925868940555887384107)
          ·
            refine ⟨2729888803410833831076161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819925868940555887384107 2729888803410833831076161)
            ·
              refine ⟨2047416602558125373307121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729888803410833831076161 2047416602558125373307121)
              ·
                refine ⟨1535562451918594029980341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047416602558125373307121 1535562451918594029980341)
                ·
                  refine ⟨143958979867368190310657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535562451918594029980341 143958979867368190310657)
                  ·
                    rfl

theorem cell20_315404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_315404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315404 prefixEnd_315404 := by exact prefixLift 315404
  have htrace : WordTrace (prefixWord ++ tailWord_315404) baseStart_315404 baseEnd_315404 := by
    simpa [prefixWord, tailWord_315404, baseEnd_315404] using wordTrace_append hprefix tailTrace_315404
  have hstable : (prefixWord ++ tailWord_315404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315404).length < 2 ^ (prefixWord ++ tailWord_315404).sum := by decide
  have hdescent : baseEnd_315404 < baseStart_315404 := by decide
  rcases family_descends (prefixWord ++ tailWord_315404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315421 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_315421 : Nat := 118140960795 + 315421 * 2 ^ 59
def prefixEnd_315421 : Nat := 4983230072969 + 3 ^ 40 * 315421 * 2
def baseEnd_315421 : Nat := 143966739130591686743921

theorem tailTrace_315421 : CollatzResearch.WordTrace tailWord_315421 prefixEnd_315421 143966739130591686743921 := by
  unfold tailWord_315421
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504348990291061463130117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7669565993527374308753411 11504348990291061463130117)
  ·
    refine ⟨2157065435679574024336897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11504348990291061463130117 2157065435679574024336897)
    ·
      refine ⟨1617799076759680518252673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2157065435679574024336897 1617799076759680518252673)
      ·
        refine ⟨1213349307569760388689505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617799076759680518252673 1213349307569760388689505)
        ·
          refine ⟨910011980677320291517129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213349307569760388689505 910011980677320291517129)
          ·
            refine ⟨682508985507990218637847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910011980677320291517129 682508985507990218637847)
            ·
              refine ⟨1023763478261985327956771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682508985507990218637847 1023763478261985327956771)
              ·
                refine ⟨1535645217392977991935157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023763478261985327956771 1535645217392977991935157)
                ·
                  refine ⟨143966739130591686743921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535645217392977991935157 143966739130591686743921)
                  ·
                    rfl

theorem cell20_315421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_315421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315421 prefixEnd_315421 := by exact prefixLift 315421
  have htrace : WordTrace (prefixWord ++ tailWord_315421) baseStart_315421 baseEnd_315421 := by
    simpa [prefixWord, tailWord_315421, baseEnd_315421] using wordTrace_append hprefix tailTrace_315421
  have hstable : (prefixWord ++ tailWord_315421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315421).length < 2 ^ (prefixWord ++ tailWord_315421).sum := by decide
  have hdescent : baseEnd_315421 < baseStart_315421 := by decide
  rcases family_descends (prefixWord ++ tailWord_315421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315480 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_315480 : Nat := 118140960795 + 315480 * 2 ^ 59
def prefixEnd_315480 : Nat := 4983230072969 + 3 ^ 40 * 315480 * 2
def baseEnd_315480 : Nat := 143993668338249703777013

theorem tailTrace_315480 : CollatzResearch.WordTrace tailWord_315480 prefixEnd_315480 143993668338249703777013 := by
  unfold tailWord_315480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753250448538657269763947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7671000598051543026351929 5753250448538657269763947)
  ·
    refine ⟨8629875672807985904645921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5753250448538657269763947 8629875672807985904645921)
    ·
      refine ⟨6472406754605989428484441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8629875672807985904645921 6472406754605989428484441)
      ·
        refine ⟨4854305065954492071363331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6472406754605989428484441 4854305065954492071363331)
        ·
          refine ⟨7281457598931738107044997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854305065954492071363331 7281457598931738107044997)
          ·
            refine ⟨1365273299799700895070937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7281457598931738107044997 1365273299799700895070937)
            ·
              refine ⟨1023954974849775671303203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365273299799700895070937 1023954974849775671303203)
              ·
                refine ⟨1535932462274663506954805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023954974849775671303203 1535932462274663506954805)
                ·
                  refine ⟨143993668338249703777013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1535932462274663506954805 143993668338249703777013)
                  ·
                    rfl

theorem cell20_315480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_315480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315480 prefixEnd_315480 := by exact prefixLift 315480
  have htrace : WordTrace (prefixWord ++ tailWord_315480) baseStart_315480 baseEnd_315480 := by
    simpa [prefixWord, tailWord_315480, baseEnd_315480] using wordTrace_append hprefix tailTrace_315480
  have hstable : (prefixWord ++ tailWord_315480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315480).length < 2 ^ (prefixWord ++ tailWord_315480).sum := by decide
  have hdescent : baseEnd_315480 < baseStart_315480 := by decide
  rcases family_descends (prefixWord ++ tailWord_315480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315486 : List Nat := [4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_315486 : Nat := 118140960795 + 315486 * 2 ^ 59
def prefixEnd_315486 : Nat := 4983230072969 + 3 ^ 40 * 315486 * 2
def baseEnd_315486 : Nat := 47998802300580116525663

theorem tailTrace_315486 : CollatzResearch.WordTrace tailWord_315486 prefixEnd_315486 47998802300580116525663 := by
  unfold tailWord_315486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438339966881947195530789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7671146490037051709497541 1438339966881947195530789)
  ·
    refine ⟨269688743790365099162023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1438339966881947195530789 269688743790365099162023)
    ·
      refine ⟨404533115685547648743035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269688743790365099162023 404533115685547648743035)
      ·
        refine ⟨606799673528321473114553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404533115685547648743035 606799673528321473114553)
        ·
          refine ⟨455099755146241104835915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606799673528321473114553 455099755146241104835915)
          ·
            refine ⟨682649632719361657253873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455099755146241104835915 682649632719361657253873)
            ·
              refine ⟨511987224539521242940405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682649632719361657253873 511987224539521242940405)
              ·
                refine ⟨47998802300580116525663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 511987224539521242940405 47998802300580116525663)
                ·
                  rfl

theorem cell20_315486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_315486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315486 prefixEnd_315486 := by exact prefixLift 315486
  have htrace : WordTrace (prefixWord ++ tailWord_315486) baseStart_315486 baseEnd_315486 := by
    simpa [prefixWord, tailWord_315486, baseEnd_315486] using wordTrace_append hprefix tailTrace_315486
  have hstable : (prefixWord ++ tailWord_315486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315486).length < 2 ^ (prefixWord ++ tailWord_315486).sum := by decide
  have hdescent : baseEnd_315486 < baseStart_315486 := by decide
  rcases family_descends (prefixWord ++ tailWord_315486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315487 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_315487 : Nat := 118140960795 + 315487 * 2 ^ 59
def prefixEnd_315487 : Nat := 4983230072969 + 3 ^ 40 * 315487 * 2
def baseEnd_315487 : Nat := 143996863328988790543651

theorem tailTrace_315487 : CollatzResearch.WordTrace tailWord_315487 prefixEnd_315487 143996863328988790543651 := by
  unfold tailWord_315487
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506756208051954735032715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7671170805367969823355143 11506756208051954735032715)
  ·
    refine ⟨17260134312077932102549073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11506756208051954735032715 17260134312077932102549073)
    ·
      refine ⟨12945100734058449076911805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17260134312077932102549073 12945100734058449076911805)
      ·
        refine ⟨4854412775271918403841927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12945100734058449076911805 4854412775271918403841927)
        ·
          refine ⟨7281619162907877605762891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854412775271918403841927 7281619162907877605762891)
          ·
            refine ⟨10922428744361816408644337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281619162907877605762891 10922428744361816408644337)
            ·
              refine ⟨8191821558271362306483253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10922428744361816408644337 8191821558271362306483253)
              ·
                refine ⟨767983271087940216232805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8191821558271362306483253 767983271087940216232805)
                ·
                  refine ⟨143996863328988790543651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767983271087940216232805 143996863328988790543651)
                  ·
                    rfl

theorem cell20_315487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_315487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315487 prefixEnd_315487 := by exact prefixLift 315487
  have htrace : WordTrace (prefixWord ++ tailWord_315487) baseStart_315487 baseEnd_315487 := by
    simpa [prefixWord, tailWord_315487, baseEnd_315487] using wordTrace_append hprefix tailTrace_315487
  have hstable : (prefixWord ++ tailWord_315487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315487).length < 2 ^ (prefixWord ++ tailWord_315487).sum := by decide
  have hdescent : baseEnd_315487 < baseStart_315487 := by decide
  rcases family_descends (prefixWord ++ tailWord_315487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315534 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_315534 : Nat := 118140960795 + 315534 * 2 ^ 59
def prefixEnd_315534 : Nat := 4983230072969 + 3 ^ 40 * 315534 * 2
def baseEnd_315534 : Nat := 144018315409665515976793

theorem tailTrace_315534 : CollatzResearch.WordTrace tailWord_315534 prefixEnd_315534 144018315409665515976793 := by
  unfold tailWord_315534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438558804860210220249207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7672313625921121174662437 1438558804860210220249207)
  ·
    refine ⟨2157838207290315330373811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1438558804860210220249207 2157838207290315330373811)
    ·
      refine ⟨3236757310935472995560717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157838207290315330373811 3236757310935472995560717)
      ·
        refine ⟨1213783991600802373335269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3236757310935472995560717 1213783991600802373335269)
        ·
          refine ⟨227584498425150445000363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1213783991600802373335269 227584498425150445000363)
          ·
            refine ⟨341376747637725667500545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227584498425150445000363 341376747637725667500545)
            ·
              refine ⟨256032560728294250625409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341376747637725667500545 256032560728294250625409)
              ·
                refine ⟨192024420546220687969057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256032560728294250625409 192024420546220687969057)
                ·
                  refine ⟨144018315409665515976793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192024420546220687969057 144018315409665515976793)
                  ·
                    rfl

theorem cell20_315534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_315534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315534 prefixEnd_315534 := by exact prefixLift 315534
  have htrace : WordTrace (prefixWord ++ tailWord_315534) baseStart_315534 baseEnd_315534 := by
    simpa [prefixWord, tailWord_315534, baseEnd_315534] using wordTrace_append hprefix tailTrace_315534
  have hstable : (prefixWord ++ tailWord_315534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315534).length < 2 ^ (prefixWord ++ tailWord_315534).sum := by decide
  have hdescent : baseEnd_315534 < baseStart_315534 := by decide
  rcases family_descends (prefixWord ++ tailWord_315534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315549 : List Nat := [1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_315549 : Nat := 118140960795 + 315549 * 2 ^ 59
def prefixEnd_315549 : Nat := 4983230072969 + 3 ^ 40 * 315549 * 2
def baseEnd_315549 : Nat := 48008387272797376825577

theorem tailTrace_315549 : CollatzResearch.WordTrace tailWord_315549 prefixEnd_315549 48008387272797376825577 := by
  unfold tailWord_315549
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509017533827339323789701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7672678355884892882526467 11509017533827339323789701)
  ·
    refine ⟨2157940787592626123210569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11509017533827339323789701 2157940787592626123210569)
    ·
      refine ⟨1618455590694469592407927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2157940787592626123210569 1618455590694469592407927)
      ·
        refine ⟨2427683386041704388611891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618455590694469592407927 2427683386041704388611891)
        ·
          refine ⟨3641525079062556582917837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427683386041704388611891 3641525079062556582917837)
          ·
            refine ⟨1365571904648458718594189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3641525079062556582917837 1365571904648458718594189)
            ·
              refine ⟨512089464243172019472821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1365571904648458718594189 512089464243172019472821)
              ·
                refine ⟨48008387272797376825577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512089464243172019472821 48008387272797376825577)
                ·
                  rfl

theorem cell20_315549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_315549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315549 prefixEnd_315549 := by exact prefixLift 315549
  have htrace : WordTrace (prefixWord ++ tailWord_315549) baseStart_315549 baseEnd_315549 := by
    simpa [prefixWord, tailWord_315549, baseEnd_315549] using wordTrace_append hprefix tailTrace_315549
  have hstable : (prefixWord ++ tailWord_315549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315549).length < 2 ^ (prefixWord ++ tailWord_315549).sum := by decide
  have hdescent : baseEnd_315549 < baseStart_315549 := by decide
  rcases family_descends (prefixWord ++ tailWord_315549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315559 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_315559 : Nat := 118140960795 + 315559 * 2 ^ 59
def prefixEnd_315559 : Nat := 4983230072969 + 3 ^ 40 * 315559 * 2
def baseEnd_315559 : Nat := 144029726090876540143357

theorem tailTrace_315559 : CollatzResearch.WordTrace tailWord_315559 prefixEnd_315559 144029726090876540143357 := by
  unfold tailWord_315559
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509382263791111031653731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7672921509194074021102487 11509382263791111031653731)
  ·
    refine ⟨17264073395686666547480597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11509382263791111031653731 17264073395686666547480597)
    ·
      refine ⟨809253440422812494413153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17264073395686666547480597 809253440422812494413153)
      ·
        refine ⟨606940080317109370809865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809253440422812494413153 606940080317109370809865)
        ·
          refine ⟨455205060237832028107399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606940080317109370809865 455205060237832028107399)
          ·
            refine ⟨682807590356748042161099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455205060237832028107399 682807590356748042161099)
            ·
              refine ⟨1024211385535122063241649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682807590356748042161099 1024211385535122063241649)
              ·
                refine ⟨768158539151341547431237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024211385535122063241649 768158539151341547431237)
                ·
                  refine ⟨144029726090876540143357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768158539151341547431237 144029726090876540143357)
                  ·
                    rfl

theorem cell20_315559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_315559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315559 prefixEnd_315559 := by exact prefixLift 315559
  have htrace : WordTrace (prefixWord ++ tailWord_315559) baseStart_315559 baseEnd_315559 := by
    simpa [prefixWord, tailWord_315559, baseEnd_315559] using wordTrace_append hprefix tailTrace_315559
  have hstable : (prefixWord ++ tailWord_315559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315559).length < 2 ^ (prefixWord ++ tailWord_315559).sum := by decide
  have hdescent : baseEnd_315559 < baseStart_315559 := by decide
  rcases family_descends (prefixWord ++ tailWord_315559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315586 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_315586 : Nat := 118140960795 + 315586 * 2 ^ 59
def prefixEnd_315586 : Nat := 4983230072969 + 3 ^ 40 * 315586 * 2
def baseEnd_315586 : Nat := 144042049626584446243247

theorem tailTrace_315586 : CollatzResearch.WordTrace tailWord_315586 prefixEnd_315586 144042049626584446243247 := by
  unfold tailWord_315586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877591758673323660721653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7673578023128863095257741 2877591758673323660721653)
  ·
    refine ⟨269774227375624093192655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2877591758673323660721653 269774227375624093192655)
    ·
      refine ⟨404661341063436139788983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269774227375624093192655 404661341063436139788983)
      ·
        refine ⟨606992011595154209683475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404661341063436139788983 606992011595154209683475)
        ·
          refine ⟨910488017392731314525213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606992011595154209683475 910488017392731314525213)
          ·
            refine ⟨341433006522274242946955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 910488017392731314525213 341433006522274242946955)
            ·
              refine ⟨512149509783411364420433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341433006522274242946955 512149509783411364420433)
              ·
                refine ⟨384112132337558523315325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512149509783411364420433 384112132337558523315325)
                ·
                  refine ⟨144042049626584446243247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384112132337558523315325 144042049626584446243247)
                  ·
                    rfl

theorem cell20_315586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_315586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315586 prefixEnd_315586 := by exact prefixLift 315586
  have htrace : WordTrace (prefixWord ++ tailWord_315586) baseStart_315586 baseEnd_315586 := by
    simpa [prefixWord, tailWord_315586, baseEnd_315586] using wordTrace_append hprefix tailTrace_315586
  have hstable : (prefixWord ++ tailWord_315586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315586).length < 2 ^ (prefixWord ++ tailWord_315586).sum := by decide
  have hdescent : baseEnd_315586 < baseStart_315586 := by decide
  rcases family_descends (prefixWord ++ tailWord_315586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315594 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_315594 : Nat := 118140960795 + 315594 * 2 ^ 59
def prefixEnd_315594 : Nat := 4983230072969 + 3 ^ 40 * 315594 * 2
def baseEnd_315594 : Nat := 144045701044571973976547

theorem tailTrace_315594 : CollatzResearch.WordTrace tailWord_315594 prefixEnd_315594 144045701044571973976547 := by
  unfold tailWord_315594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877664704666078002294459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7673772545776208006118557 2877664704666078002294459)
  ·
    refine ⟨4316497056999117003441689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877664704666078002294459 4316497056999117003441689)
    ·
      refine ⟨3237372792749337752581267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4316497056999117003441689 3237372792749337752581267)
      ·
        refine ⟨4856059189124006628871901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237372792749337752581267 4856059189124006628871901)
        ·
          refine ⟨1821022195921502485826963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4856059189124006628871901 1821022195921502485826963)
          ·
            refine ⟨2731533293882253728740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821022195921502485826963 2731533293882253728740445)
            ·
              refine ⟨1024324985205845148277667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2731533293882253728740445 1024324985205845148277667)
              ·
                refine ⟨1536487477808767722416501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024324985205845148277667 1536487477808767722416501)
                ·
                  refine ⟨144045701044571973976547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1536487477808767722416501 144045701044571973976547)
                  ·
                    rfl

theorem cell20_315594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_315594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315594 prefixEnd_315594 := by exact prefixLift 315594
  have htrace : WordTrace (prefixWord ++ tailWord_315594) baseStart_315594 baseEnd_315594 := by
    simpa [prefixWord, tailWord_315594, baseEnd_315594] using wordTrace_append hprefix tailTrace_315594
  have hstable : (prefixWord ++ tailWord_315594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315594).length < 2 ^ (prefixWord ++ tailWord_315594).sum := by decide
  have hdescent : baseEnd_315594 < baseStart_315594 := by decide
  rcases family_descends (prefixWord ++ tailWord_315594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315601 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_315601 : Nat := 118140960795 + 315601 * 2 ^ 59
def prefixEnd_315601 : Nat := 4983230072969 + 3 ^ 40 * 315601 * 2
def baseEnd_315601 : Nat := 144048896035311060743185

theorem tailTrace_315601 : CollatzResearch.WordTrace tailWord_315601 prefixEnd_315601 144048896035311060743185 := by
  unfold tailWord_315601
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510914129638952204682657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7673942753092634803121771 11510914129638952204682657)
  ·
    refine ⟨8633185597229214153511993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11510914129638952204682657 8633185597229214153511993)
    ·
      refine ⟨6474889197921910615133995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8633185597229214153511993 6474889197921910615133995)
      ·
        refine ⟨9712333796882865922700993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6474889197921910615133995 9712333796882865922700993)
        ·
          refine ⟨7284250347662149442025745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9712333796882865922700993 7284250347662149442025745)
          ·
            refine ⟨5463187760746612081519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7284250347662149442025745 5463187760746612081519309)
            ·
              refine ⟨2048695410279979530569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5463187760746612081519309 2048695410279979530569741)
              ·
                refine ⟨768260778854992323963653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2048695410279979530569741 768260778854992323963653)
                ·
                  refine ⟨144048896035311060743185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768260778854992323963653 144048896035311060743185)
                  ·
                    rfl

theorem cell20_315601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_315601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315601 prefixEnd_315601 := by exact prefixLift 315601
  have htrace : WordTrace (prefixWord ++ tailWord_315601) baseStart_315601 baseEnd_315601 := by
    simpa [prefixWord, tailWord_315601, baseEnd_315601] using wordTrace_append hprefix tailTrace_315601
  have hstable : (prefixWord ++ tailWord_315601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315601).length < 2 ^ (prefixWord ++ tailWord_315601).sum := by decide
  have hdescent : baseEnd_315601 < baseStart_315601 := by decide
  rcases family_descends (prefixWord ++ tailWord_315601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315652 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_315652 : Nat := 118140960795 + 315652 * 2 ^ 59
def prefixEnd_315652 : Nat := 4983230072969 + 3 ^ 40 * 315652 * 2
def baseEnd_315652 : Nat := 144072173824981550042977

theorem tailTrace_315652 : CollatzResearch.WordTrace tailWord_315652 prefixEnd_315652 144072173824981550042977 := by
  unfold tailWord_315652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756387126227093957394605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7675182834969458609859473 5756387126227093957394605)
  ·
    refine ⟨2158645172335160234022977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5756387126227093957394605 2158645172335160234022977)
    ·
      refine ⟨1618983879251370175517233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158645172335160234022977 1618983879251370175517233)
      ·
        refine ⟨1214237909438527631637925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618983879251370175517233 1214237909438527631637925)
        ·
          refine ⟨227669608019723930932111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1214237909438527631637925 227669608019723930932111)
          ·
            refine ⟨341504412029585896398167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227669608019723930932111 341504412029585896398167)
            ·
              refine ⟨512256618044378844597251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341504412029585896398167 512256618044378844597251)
              ·
                refine ⟨768384927066568266895877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512256618044378844597251 768384927066568266895877)
                ·
                  refine ⟨144072173824981550042977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768384927066568266895877 144072173824981550042977)
                  ·
                    rfl

theorem cell20_315652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_315652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315652 prefixEnd_315652 := by exact prefixLift 315652
  have htrace : WordTrace (prefixWord ++ tailWord_315652) baseStart_315652 baseEnd_315652 := by
    simpa [prefixWord, tailWord_315652, baseEnd_315652] using wordTrace_append hprefix tailTrace_315652
  have hstable : (prefixWord ++ tailWord_315652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315652).length < 2 ^ (prefixWord ++ tailWord_315652).sum := by decide
  have hdescent : baseEnd_315652 < baseStart_315652 := by decide
  rcases family_descends (prefixWord ++ tailWord_315652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315656 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_315656 : Nat := 118140960795 + 315656 * 2 ^ 59
def prefixEnd_315656 : Nat := 4983230072969 + 3 ^ 40 * 315656 * 2
def baseEnd_315656 : Nat := 144073999533975313909627

theorem tailTrace_315656 : CollatzResearch.WordTrace tailWord_315656 prefixEnd_315656 144073999533975313909627 := by
  unfold tailWord_315656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756460072219848298967411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7675280096293131065289881 5756460072219848298967411)
  ·
    refine ⟨8634690108329772448451117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5756460072219848298967411 8634690108329772448451117)
    ·
      refine ⟨3238008790623664668169169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8634690108329772448451117 3238008790623664668169169)
      ·
        refine ⟨2428506592967748501126877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3238008790623664668169169 2428506592967748501126877)
        ·
          refine ⟨910689972362905687922579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2428506592967748501126877 910689972362905687922579)
          ·
            refine ⟨1366034958544358531883869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910689972362905687922579 1366034958544358531883869)
            ·
              refine ⟨512263109454134449456451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1366034958544358531883869 512263109454134449456451)
              ·
                refine ⟨768394664181201674184677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512263109454134449456451 768394664181201674184677)
                ·
                  refine ⟨144073999533975313909627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768394664181201674184677 144073999533975313909627)
                  ·
                    rfl

theorem cell20_315656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_315656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315656 prefixEnd_315656 := by exact prefixLift 315656
  have htrace : WordTrace (prefixWord ++ tailWord_315656) baseStart_315656 baseEnd_315656 := by
    simpa [prefixWord, tailWord_315656, baseEnd_315656] using wordTrace_append hprefix tailTrace_315656
  have hstable : (prefixWord ++ tailWord_315656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315656).length < 2 ^ (prefixWord ++ tailWord_315656).sum := by decide
  have hdescent : baseEnd_315656 < baseStart_315656 := by decide
  rcases family_descends (prefixWord ++ tailWord_315656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315732 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_315732 : Nat := 118140960795 + 315732 * 2 ^ 59
def prefixEnd_315732 : Nat := 4983230072969 + 3 ^ 40 * 315732 * 2
def baseEnd_315732 : Nat := 144108688004856827375983

theorem tailTrace_315732 : CollatzResearch.WordTrace tailWord_315732 prefixEnd_315732 144108688004856827375983 := by
  unfold tailWord_315732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5757846046082180788850725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7677128061442907718467633 5757846046082180788850725)
  ·
    refine ⟨1079596133640408897909511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5757846046082180788850725 1079596133640408897909511)
    ·
      refine ⟨1619394200460613346864267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079596133640408897909511 1619394200460613346864267)
      ·
        refine ⟨2429091300690920020296401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619394200460613346864267 2429091300690920020296401)
        ·
          refine ⟨1821818475518190015222301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429091300690920020296401 1821818475518190015222301)
          ·
            refine ⟨683181928319321255708363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1821818475518190015222301 683181928319321255708363)
            ·
              refine ⟨1024772892478981883562545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683181928319321255708363 1024772892478981883562545)
              ·
                refine ⟨768579669359236412671909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024772892478981883562545 768579669359236412671909)
                ·
                  refine ⟨144108688004856827375983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768579669359236412671909 144108688004856827375983)
                  ·
                    rfl

theorem cell20_315732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_315732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315732 prefixEnd_315732 := by exact prefixLift 315732
  have htrace : WordTrace (prefixWord ++ tailWord_315732) baseStart_315732 baseEnd_315732 := by
    simpa [prefixWord, tailWord_315732, baseEnd_315732] using wordTrace_append hprefix tailTrace_315732
  have hstable : (prefixWord ++ tailWord_315732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315732).length < 2 ^ (prefixWord ++ tailWord_315732).sum := by decide
  have hdescent : baseEnd_315732 < baseStart_315732 := by decide
  rcases family_descends (prefixWord ++ tailWord_315732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315749 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 2]
def baseStart_315749 : Nat := 118140960795 + 315749 * 2 ^ 59
def prefixEnd_315749 : Nat := 4983230072969 + 3 ^ 40 * 315749 * 2
def baseEnd_315749 : Nat := 144116447268080323809247

theorem tailTrace_315749 : CollatzResearch.WordTrace tailWord_315749 prefixEnd_315749 144116447268080323809247 := by
  unfold tailWord_315749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516312133102773481070301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7677541422068515654046867 11516312133102773481070301)
  ·
    refine ⟨4318617049913540055401363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11516312133102773481070301 4318617049913540055401363)
    ·
      refine ⟨6477925574870310083102045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318617049913540055401363 6477925574870310083102045)
      ·
        refine ⟨2429222090576366281163267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6477925574870310083102045 2429222090576366281163267)
        ·
          refine ⟨3643833135864549421744901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429222090576366281163267 3643833135864549421744901)
          ·
            refine ⟨683218712974603016577169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3643833135864549421744901 683218712974603016577169)
            ·
              refine ⟨512414034730952262432877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683218712974603016577169 512414034730952262432877)
              ·
                refine ⟨192155263024107098412329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512414034730952262432877 192155263024107098412329)
                ·
                  refine ⟨144116447268080323809247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192155263024107098412329 144116447268080323809247)
                  ·
                    rfl

theorem cell20_315749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_315749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315749 prefixEnd_315749 := by exact prefixLift 315749
  have htrace : WordTrace (prefixWord ++ tailWord_315749) baseStart_315749 baseEnd_315749 := by
    simpa [prefixWord, tailWord_315749, baseEnd_315749] using wordTrace_append hprefix tailTrace_315749
  have hstable : (prefixWord ++ tailWord_315749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315749).length < 2 ^ (prefixWord ++ tailWord_315749).sum := by decide
  have hdescent : baseEnd_315749 < baseStart_315749 := by decide
  rcases family_descends (prefixWord ++ tailWord_315749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315760 : List Nat := [2, 1, 1, 1, 4, 4, 7]
def baseStart_315760 : Nat := 118140960795 + 315760 * 2 ^ 59
def prefixEnd_315760 : Nat := 4983230072969 + 3 ^ 40 * 315760 * 2
def baseEnd_315760 : Nat := 16013496440868130493615

theorem tailTrace_315760 : CollatzResearch.WordTrace tailWord_315760 prefixEnd_315760 16013496440868130493615 := by
  unfold tailWord_315760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758356668031461179860367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7677808890708614906480489 5758356668031461179860367)
  ·
    refine ⟨8637535002047191769790551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5758356668031461179860367 8637535002047191769790551)
    ·
      refine ⟨12956302503070787654685827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8637535002047191769790551 12956302503070787654685827)
      ·
        refine ⟨19434453754606181482028741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12956302503070787654685827 19434453754606181482028741)
        ·
          refine ⟨3643960078988659027880389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19434453754606181482028741 3643960078988659027880389)
          ·
            refine ⟨683242514810373567727573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3643960078988659027880389 683242514810373567727573)
            ·
              refine ⟨16013496440868130493615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 683242514810373567727573 16013496440868130493615)
              ·
                rfl

theorem cell20_315760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_315760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315760 prefixEnd_315760 := by exact prefixLift 315760
  have htrace : WordTrace (prefixWord ++ tailWord_315760) baseStart_315760 baseEnd_315760 := by
    simpa [prefixWord, tailWord_315760, baseEnd_315760] using wordTrace_append hprefix tailTrace_315760
  have hstable : (prefixWord ++ tailWord_315760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315760).length < 2 ^ (prefixWord ++ tailWord_315760).sum := by decide
  have hdescent : baseEnd_315760 < baseStart_315760 := by decide
  rcases family_descends (prefixWord ++ tailWord_315760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315766 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_315766 : Nat := 118140960795 + 315766 * 2 ^ 59
def prefixEnd_315766 : Nat := 4983230072969 + 3 ^ 40 * 315766 * 2
def baseEnd_315766 : Nat := 144124206531303820242511

theorem tailTrace_315766 : CollatzResearch.WordTrace tailWord_315766 prefixEnd_315766 144124206531303820242511 := by
  unfold tailWord_315766
  simp only [CollatzResearch.WordTrace]
  refine ⟨719808260877574086527447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7677954782694123589626101 719808260877574086527447)
  ·
    refine ⟨1079712391316361129791171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719808260877574086527447 1079712391316361129791171)
    ·
      refine ⟨1619568586974541694686757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079712391316361129791171 1619568586974541694686757)
      ·
        refine ⟨303669110057726567753767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1619568586974541694686757 303669110057726567753767)
        ·
          refine ⟨455503665086589851630651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303669110057726567753767 455503665086589851630651)
          ·
            refine ⟨683255497629884777445977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455503665086589851630651 683255497629884777445977)
            ·
              refine ⟨512441623222413583084483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683255497629884777445977 512441623222413583084483)
              ·
                refine ⟨768662434833620374626725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512441623222413583084483 768662434833620374626725)
                ·
                  refine ⟨144124206531303820242511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768662434833620374626725 144124206531303820242511)
                  ·
                    rfl

theorem cell20_315766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_315766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315766 prefixEnd_315766 := by exact prefixLift 315766
  have htrace : WordTrace (prefixWord ++ tailWord_315766) baseStart_315766 baseEnd_315766 := by
    simpa [prefixWord, tailWord_315766, baseEnd_315766] using wordTrace_append hprefix tailTrace_315766
  have hstable : (prefixWord ++ tailWord_315766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315766).length < 2 ^ (prefixWord ++ tailWord_315766).sum := by decide
  have hdescent : baseEnd_315766 < baseStart_315766 := by decide
  rcases family_descends (prefixWord ++ tailWord_315766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315815 : List Nat := [1, 1, 6, 1, 1, 4, 6]
def baseStart_315815 : Nat := 118140960795 + 315815 * 2 ^ 59
def prefixEnd_315815 : Nat := 4983230072969 + 3 ^ 40 * 315815 * 2
def baseEnd_315815 : Nat := 16016285718497491956553

theorem tailTrace_315815 : CollatzResearch.WordTrace tailWord_315815 prefixEnd_315815 16016285718497491956553 := by
  unfold tailWord_315815
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518719350863666752972899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7679146233909111168648599 11518719350863666752972899)
  ·
    refine ⟨17278079026295500129459349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11518719350863666752972899 17278079026295500129459349)
    ·
      refine ⟨809909954357601568568407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17278079026295500129459349 809909954357601568568407)
      ·
        refine ⟨1214864931536402352852611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809909954357601568568407 1214864931536402352852611)
        ·
          refine ⟨1822297397304603529278917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214864931536402352852611 1822297397304603529278917)
          ·
            refine ⟨341680761994613161739797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1822297397304603529278917 341680761994613161739797)
            ·
              refine ⟨16016285718497491956553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 341680761994613161739797 16016285718497491956553)
              ·
                rfl

theorem cell20_315815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_315815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315815 prefixEnd_315815 := by exact prefixLift 315815
  have htrace : WordTrace (prefixWord ++ tailWord_315815) baseStart_315815 baseEnd_315815 := by
    simpa [prefixWord, tailWord_315815, baseEnd_315815] using wordTrace_append hprefix tailTrace_315815
  have hstable : (prefixWord ++ tailWord_315815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315815).length < 2 ^ (prefixWord ++ tailWord_315815).sum := by decide
  have hdescent : baseEnd_315815 < baseStart_315815 := by decide
  rcases family_descends (prefixWord ++ tailWord_315815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315821 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 2]
def baseStart_315821 : Nat := 118140960795 + 315821 * 2 ^ 59
def prefixEnd_315821 : Nat := 4983230072969 + 3 ^ 40 * 315821 * 2
def baseEnd_315821 : Nat := 144149310029968073408953

theorem tailTrace_315821 : CollatzResearch.WordTrace tailWord_315821 prefixEnd_315821 144149310029968073408953 := by
  unfold tailWord_315821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518938188841929777691317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7679292125894619851794211 11518938188841929777691317)
  ·
    refine ⟨1079900455203930916658561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11518938188841929777691317 1079900455203930916658561)
    ·
      refine ⟨809925341402948187493921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079900455203930916658561 809925341402948187493921)
      ·
        refine ⟨607444006052211140620441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809925341402948187493921 607444006052211140620441)
        ·
          refine ⟨455583004539158355465331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607444006052211140620441 455583004539158355465331)
          ·
            refine ⟨683374506808737533197997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455583004539158355465331 683374506808737533197997)
            ·
              refine ⟨256265440053276574949249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683374506808737533197997 256265440053276574949249)
              ·
                refine ⟨192199080039957431211937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256265440053276574949249 192199080039957431211937)
                ·
                  refine ⟨144149310029968073408953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192199080039957431211937 144149310029968073408953)
                  ·
                    rfl

theorem cell20_315821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_315821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315821 prefixEnd_315821 := by exact prefixLift 315821
  have htrace : WordTrace (prefixWord ++ tailWord_315821) baseStart_315821 baseEnd_315821 := by
    simpa [prefixWord, tailWord_315821, baseEnd_315821] using wordTrace_append hprefix tailTrace_315821
  have hstable : (prefixWord ++ tailWord_315821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315821).length < 2 ^ (prefixWord ++ tailWord_315821).sum := by decide
  have hdescent : baseEnd_315821 < baseStart_315821 := by decide
  rcases family_descends (prefixWord ++ tailWord_315821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315880 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_315880 : Nat := 118140960795 + 315880 * 2 ^ 59
def prefixEnd_315880 : Nat := 4983230072969 + 3 ^ 40 * 315880 * 2
def baseEnd_315880 : Nat := 144176239237626090442045

theorem tailTrace_315880 : CollatzResearch.WordTrace tailWord_315880 prefixEnd_315880 144176239237626090442045 := by
  unfold tailWord_315880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760545047814091427044547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7680726730418788569392729 5760545047814091427044547)
  ·
    refine ⟨8640817571721137140566821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760545047814091427044547 8640817571721137140566821)
    ·
      refine ⟨1620153294697713213856279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8640817571721137140566821 1620153294697713213856279)
      ·
        refine ⟨2430229942046569820784419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620153294697713213856279 2430229942046569820784419)
        ·
          refine ⟨3645344913069854731176629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430229942046569820784419 3645344913069854731176629)
          ·
            refine ⟨341751085600298881047809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3645344913069854731176629 341751085600298881047809)
            ·
              refine ⟨256313314200224160785857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341751085600298881047809 256313314200224160785857)
              ·
                refine ⟨192234985650168120589393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256313314200224160785857 192234985650168120589393)
                ·
                  refine ⟨144176239237626090442045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192234985650168120589393 144176239237626090442045)
                  ·
                    rfl

theorem cell20_315880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_315880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315880 prefixEnd_315880 := by exact prefixLift 315880
  have htrace : WordTrace (prefixWord ++ tailWord_315880) baseStart_315880 baseEnd_315880 := by
    simpa [prefixWord, tailWord_315880, baseEnd_315880] using wordTrace_append hprefix tailTrace_315880
  have hstable : (prefixWord ++ tailWord_315880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315880).length < 2 ^ (prefixWord ++ tailWord_315880).sum := by decide
  have hdescent : baseEnd_315880 < baseStart_315880 := by decide
  rcases family_descends (prefixWord ++ tailWord_315880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315884 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_315884 : Nat := 118140960795 + 315884 * 2 ^ 59
def prefixEnd_315884 : Nat := 4983230072969 + 3 ^ 40 * 315884 * 2
def baseEnd_315884 : Nat := 144178064946619854308695

theorem tailTrace_315884 : CollatzResearch.WordTrace tailWord_315884 prefixEnd_315884 144178064946619854308695 := by
  unfold tailWord_315884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760617993806845768617353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7680823991742461024823137 5760617993806845768617353)
  ·
    refine ⟨4320463495355134326463015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5760617993806845768617353 4320463495355134326463015)
    ·
      refine ⟨6480695243032701489694523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320463495355134326463015 6480695243032701489694523)
      ·
        refine ⟨9721042864549052234541785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6480695243032701489694523 9721042864549052234541785)
        ·
          refine ⟨7290782148411789175906339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9721042864549052234541785 7290782148411789175906339)
          ·
            refine ⟨10936173222617683763859509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7290782148411789175906339 10936173222617683763859509)
            ·
              refine ⟨1025266239620407852861829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10936173222617683763859509 1025266239620407852861829)
              ·
                refine ⟨192237419928826472411593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1025266239620407852861829 192237419928826472411593)
                ·
                  refine ⟨144178064946619854308695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192237419928826472411593 144178064946619854308695)
                  ·
                    rfl

theorem cell20_315884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_315884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315884 prefixEnd_315884 := by exact prefixLift 315884
  have htrace : WordTrace (prefixWord ++ tailWord_315884) baseStart_315884 baseEnd_315884 := by
    simpa [prefixWord, tailWord_315884, baseEnd_315884] using wordTrace_append hprefix tailTrace_315884
  have hstable : (prefixWord ++ tailWord_315884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315884).length < 2 ^ (prefixWord ++ tailWord_315884).sum := by decide
  have hdescent : baseEnd_315884 < baseStart_315884 := by decide
  rcases family_descends (prefixWord ++ tailWord_315884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315905 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_315905 : Nat := 118140960795 + 315905 * 2 ^ 59
def prefixEnd_315905 : Nat := 4983230072969 + 3 ^ 40 * 315905 * 2
def baseEnd_315905 : Nat := 144187649918837114608609

theorem tailTrace_315905 : CollatzResearch.WordTrace tailWord_315905 prefixEnd_315905 144187649918837114608609 := by
  unfold tailWord_315905
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522001920537612123749169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7681334613691741415832779 11522001920537612123749169)
  ·
    refine ⟨8641501440403209092811877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11522001920537612123749169 8641501440403209092811877)
    ·
      refine ⟨1620281520075601704902227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8641501440403209092811877 1620281520075601704902227)
      ·
        refine ⟨2430422280113402557353341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620281520075601704902227 2430422280113402557353341)
        ·
          refine ⟨911408355042525959007503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2430422280113402557353341 911408355042525959007503)
          ·
            refine ⟨1367112532563788938511255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911408355042525959007503 1367112532563788938511255)
            ·
              refine ⟨2050668798845683407766883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367112532563788938511255 2050668798845683407766883)
              ·
                refine ⟨3076003198268525111650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050668798845683407766883 3076003198268525111650325)
                ·
                  refine ⟨144187649918837114608609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3076003198268525111650325 144187649918837114608609)
                  ·
                    rfl

theorem cell20_315905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_315905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315905 prefixEnd_315905 := by exact prefixLift 315905
  have htrace : WordTrace (prefixWord ++ tailWord_315905) baseStart_315905 baseEnd_315905 := by
    simpa [prefixWord, tailWord_315905, baseEnd_315905] using wordTrace_append hprefix tailTrace_315905
  have hstable : (prefixWord ++ tailWord_315905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315905).length < 2 ^ (prefixWord ++ tailWord_315905).sum := by decide
  have hdescent : baseEnd_315905 < baseStart_315905 := by decide
  rcases family_descends (prefixWord ++ tailWord_315905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315908 : List Nat := [2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_315908 : Nat := 118140960795 + 315908 * 2 ^ 59
def prefixEnd_315908 : Nat := 4983230072969 + 3 ^ 40 * 315908 * 2
def baseEnd_315908 : Nat := 48063006400194145836199

theorem tailTrace_315908 : CollatzResearch.WordTrace tailWord_315908 prefixEnd_315908 48063006400194145836199 := by
  unfold tailWord_315908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761055669763371818054189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7681407559684495757405585 5761055669763371818054189)
  ·
    refine ⟨2160395876161264431770321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5761055669763371818054189 2160395876161264431770321)
    ·
      refine ⟨1620296907120948323827741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2160395876161264431770321 1620296907120948323827741)
      ·
        refine ⟨607611340170355621435403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1620296907120948323827741 607611340170355621435403)
        ·
          refine ⟨911417010255533432153105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607611340170355621435403 911417010255533432153105)
          ·
            refine ⟨683562757691650074114829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911417010255533432153105 683562757691650074114829)
            ·
              refine ⟨256336034134368777793061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683562757691650074114829 256336034134368777793061)
              ·
                refine ⟨48063006400194145836199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256336034134368777793061 48063006400194145836199)
                ·
                  rfl

theorem cell20_315908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_315908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315908 prefixEnd_315908 := by exact prefixLift 315908
  have htrace : WordTrace (prefixWord ++ tailWord_315908) baseStart_315908 baseEnd_315908 := by
    simpa [prefixWord, tailWord_315908, baseEnd_315908] using wordTrace_append hprefix tailTrace_315908
  have hstable : (prefixWord ++ tailWord_315908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315908).length < 2 ^ (prefixWord ++ tailWord_315908).sum := by decide
  have hdescent : baseEnd_315908 < baseStart_315908 := by decide
  rcases family_descends (prefixWord ++ tailWord_315908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315988 : List Nat := [2, 4, 1, 1, 1, 3, 8]
def baseStart_315988 : Nat := 118140960795 + 315988 * 2 ^ 59
def prefixEnd_315988 : Nat := 4983230072969 + 3 ^ 40 * 315988 * 2
def baseEnd_315988 : Nat := 16025059264495301649067

theorem tailTrace_315988 : CollatzResearch.WordTrace tailWord_315988 prefixEnd_315988 16025059264495301649067 := by
  unfold tailWord_315988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762514589618458649510309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7683352786157944866013745 5762514589618458649510309)
  ·
    refine ⟨1080471485553460996783183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5762514589618458649510309 1080471485553460996783183)
    ·
      refine ⟨1620707228330191495174775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080471485553460996783183 1620707228330191495174775)
      ·
        refine ⟨2431060842495287242762163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620707228330191495174775 2431060842495287242762163)
        ·
          refine ⟨3646591263742930864143245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431060842495287242762163 3646591263742930864143245)
          ·
            refine ⟨1367471723903599074053717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3646591263742930864143245 1367471723903599074053717)
            ·
              refine ⟨16025059264495301649067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1367471723903599074053717 16025059264495301649067)
              ·
                rfl

theorem cell20_315988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_315988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_315988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_315988 prefixEnd_315988 := by exact prefixLift 315988
  have htrace : WordTrace (prefixWord ++ tailWord_315988) baseStart_315988 baseEnd_315988 := by
    simpa [prefixWord, tailWord_315988, baseEnd_315988] using wordTrace_append hprefix tailTrace_315988
  have hstable : (prefixWord ++ tailWord_315988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315988).length < 2 ^ (prefixWord ++ tailWord_315988).sum := by decide
  have hdescent : baseEnd_315988 < baseStart_315988 := by decide
  rcases family_descends (prefixWord ++ tailWord_315988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316005 : List Nat := [1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_316005 : Nat := 118140960795 + 316005 * 2 ^ 59
def prefixEnd_316005 : Nat := 4983230072969 + 3 ^ 40 * 316005 * 2
def baseEnd_316005 : Nat := 48077764214560403758289

theorem tailTrace_316005 : CollatzResearch.WordTrace tailWord_316005 prefixEnd_316005 48077764214560403758289 := by
  unfold tailWord_316005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525649220175329202389469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7683766146783552801592979 11525649220175329202389469)
  ·
    refine ⟨4322118457565748450896051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11525649220175329202389469 4322118457565748450896051)
    ·
      refine ⟨6483177686348622676344077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4322118457565748450896051 6483177686348622676344077)
      ·
        refine ⟨2431191632380733503629029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6483177686348622676344077 2431191632380733503629029)
        ·
          refine ⟨455848431071387531930443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2431191632380733503629029 455848431071387531930443)
          ·
            refine ⟨683772646607081297895665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455848431071387531930443 683772646607081297895665)
            ·
              refine ⟨512829484955310973421749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683772646607081297895665 512829484955310973421749)
              ·
                refine ⟨48077764214560403758289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512829484955310973421749 48077764214560403758289)
                ·
                  rfl

theorem cell20_316005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_316005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316005 prefixEnd_316005 := by exact prefixLift 316005
  have htrace : WordTrace (prefixWord ++ tailWord_316005) baseStart_316005 baseEnd_316005 := by
    simpa [prefixWord, tailWord_316005, baseEnd_316005] using wordTrace_append hprefix tailTrace_316005
  have hstable : (prefixWord ++ tailWord_316005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316005).length < 2 ^ (prefixWord ++ tailWord_316005).sum := by decide
  have hdescent : baseEnd_316005 < baseStart_316005 := by decide
  rcases family_descends (prefixWord ++ tailWord_316005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316133 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_316133 : Nat := 118140960795 + 316133 * 2 ^ 59
def prefixEnd_316133 : Nat := 4983230072969 + 3 ^ 40 * 316133 * 2
def baseEnd_316133 : Nat := 144291715331481655007677

theorem tailTrace_316133 : CollatzResearch.WordTrace tailWord_316133 prefixEnd_316133 144291715331481655007677 := by
  unfold tailWord_316133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530317763711607063049053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7686878509141071375366035 11530317763711607063049053)
  ·
    refine ⟨4323869161391852648643395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11530317763711607063049053 4323869161391852648643395)
    ·
      refine ⟨6485803742087778972965093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323869161391852648643395 6485803742087778972965093)
      ·
        refine ⟨1216088201641458557430955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6485803742087778972965093 1216088201641458557430955)
        ·
          refine ⟨1824132302462187836146433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216088201641458557430955 1824132302462187836146433)
          ·
            refine ⟨1368099226846640877109825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824132302462187836146433 1368099226846640877109825)
            ·
              refine ⟨1026074420134980657832369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368099226846640877109825 1026074420134980657832369)
              ·
                refine ⟨769555815101235493374277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026074420134980657832369 769555815101235493374277)
                ·
                  refine ⟨144291715331481655007677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769555815101235493374277 144291715331481655007677)
                  ·
                    rfl

theorem cell20_316133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_316133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316133 prefixEnd_316133 := by exact prefixLift 316133
  have htrace : WordTrace (prefixWord ++ tailWord_316133) baseStart_316133 baseEnd_316133 := by
    simpa [prefixWord, tailWord_316133, baseEnd_316133] using wordTrace_append hprefix tailTrace_316133
  have hstable : (prefixWord ++ tailWord_316133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316133).length < 2 ^ (prefixWord ++ tailWord_316133).sum := by decide
  have hdescent : baseEnd_316133 < baseStart_316133 := by decide
  rcases family_descends (prefixWord ++ tailWord_316133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316136 : List Nat := [2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_316136 : Nat := 118140960795 + 316136 * 2 ^ 59
def prefixEnd_316136 : Nat := 4983230072969 + 3 ^ 40 * 316136 * 2
def baseEnd_316136 : Nat := 48097694871075659302555

theorem tailTrace_316136 : CollatzResearch.WordTrace tailWord_316136 prefixEnd_316136 48097694871075659302555 := by
  unfold tailWord_316136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765213591350369287704131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7686951455133825716938841 5765213591350369287704131)
  ·
    refine ⟨8647820387025553931556197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765213591350369287704131 8647820387025553931556197)
    ·
      refine ⟨1621466322567291362166787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8647820387025553931556197 1621466322567291362166787)
      ·
        refine ⟨2432199483850937043250181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621466322567291362166787 2432199483850937043250181)
        ·
          refine ⟨456037403222050695609409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2432199483850937043250181 456037403222050695609409)
          ·
            refine ⟨342028052416538021707057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456037403222050695609409 342028052416538021707057)
            ·
              refine ⟨256521039312403516280293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342028052416538021707057 256521039312403516280293)
              ·
                refine ⟨48097694871075659302555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256521039312403516280293 48097694871075659302555)
                ·
                  rfl

theorem cell20_316136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_316136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316136 prefixEnd_316136 := by exact prefixLift 316136
  have htrace : WordTrace (prefixWord ++ tailWord_316136) baseStart_316136 baseEnd_316136 := by
    simpa [prefixWord, tailWord_316136, baseEnd_316136] using wordTrace_append hprefix tailTrace_316136
  have hstable : (prefixWord ++ tailWord_316136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316136).length < 2 ^ (prefixWord ++ tailWord_316136).sum := by decide
  have hdescent : baseEnd_316136 < baseStart_316136 := by decide
  rcases family_descends (prefixWord ++ tailWord_316136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316154 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_316154 : Nat := 118140960795 + 316154 * 2 ^ 59
def prefixEnd_316154 : Nat := 4983230072969 + 3 ^ 40 * 316154 * 2
def baseEnd_316154 : Nat := 144301300303698915307591

theorem tailTrace_316154 : CollatzResearch.WordTrace tailWord_316154 prefixEnd_316154 144301300303698915307591 := by
  unfold tailWord_316154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882770924158881912390879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7687389131090351766375677 2882770924158881912390879)
  ·
    refine ⟨4324156386238322868586319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882770924158881912390879 4324156386238322868586319)
    ·
      refine ⟨6486234579357484302879479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324156386238322868586319 6486234579357484302879479)
      ·
        refine ⟨9729351869036226454319219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486234579357484302879479 9729351869036226454319219)
        ·
          refine ⟨14594027803554339681478829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729351869036226454319219 14594027803554339681478829)
          ·
            refine ⟨5472760426332877380554561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14594027803554339681478829 5472760426332877380554561)
            ·
              refine ⟨4104570319749658035415921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5472760426332877380554561 4104570319749658035415921)
              ·
                refine ⟨3078427739812243526561941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104570319749658035415921 3078427739812243526561941)
                ·
                  refine ⟨144301300303698915307591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3078427739812243526561941 144301300303698915307591)
                  ·
                    rfl

theorem cell20_316154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_316154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316154 prefixEnd_316154 := by exact prefixLift 316154
  have htrace : WordTrace (prefixWord ++ tailWord_316154) baseStart_316154 baseEnd_316154 := by
    simpa [prefixWord, tailWord_316154, baseEnd_316154] using wordTrace_append hprefix tailTrace_316154
  have hstable : (prefixWord ++ tailWord_316154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316154).length < 2 ^ (prefixWord ++ tailWord_316154).sum := by decide
  have hdescent : baseEnd_316154 < baseStart_316154 := by decide
  rcases family_descends (prefixWord ++ tailWord_316154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316164 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_316164 : Nat := 118140960795 + 316164 * 2 ^ 59
def prefixEnd_316164 : Nat := 4983230072969 + 3 ^ 40 * 316164 * 2
def baseEnd_316164 : Nat := 144305864576183324974217

theorem tailTrace_316164 : CollatzResearch.WordTrace tailWord_316164 prefixEnd_316164 144305864576183324974217 := by
  unfold tailWord_316164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765724213299649678713773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7687632284399532904951697 5765724213299649678713773)
  ·
    refine ⟨2162146579987368629517665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5765724213299649678713773 2162146579987368629517665)
    ·
      refine ⟨1621609934990526472138249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2162146579987368629517665 1621609934990526472138249)
      ·
        refine ⟨1216207451242894854103687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621609934990526472138249 1216207451242894854103687)
        ·
          refine ⟨1824311176864342281155531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216207451242894854103687 1824311176864342281155531)
          ·
            refine ⟨2736466765296513421733297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824311176864342281155531 2736466765296513421733297)
            ·
              refine ⟨2052350073972385066299973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736466765296513421733297 2052350073972385066299973)
              ·
                refine ⟨384815638869822199931245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2052350073972385066299973 384815638869822199931245)
                ·
                  refine ⟨144305864576183324974217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384815638869822199931245 144305864576183324974217)
                  ·
                    rfl

theorem cell20_316164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_316164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316164 prefixEnd_316164 := by exact prefixLift 316164
  have htrace : WordTrace (prefixWord ++ tailWord_316164) baseStart_316164 baseEnd_316164 := by
    simpa [prefixWord, tailWord_316164, baseEnd_316164] using wordTrace_append hprefix tailTrace_316164
  have hstable : (prefixWord ++ tailWord_316164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316164).length < 2 ^ (prefixWord ++ tailWord_316164).sum := by decide
  have hdescent : baseEnd_316164 < baseStart_316164 := by decide
  rcases family_descends (prefixWord ++ tailWord_316164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316247 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_316247 : Nat := 118140960795 + 316247 * 2 ^ 59
def prefixEnd_316247 : Nat := 4983230072969 + 3 ^ 40 * 316247 * 2
def baseEnd_316247 : Nat := 144343748037803925207211

theorem tailTrace_316247 : CollatzResearch.WordTrace tailWord_316247 prefixEnd_316247 144343748037803925207211 := by
  unfold tailWord_316247
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534475685298604532698995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7689650456865736355132663 11534475685298604532698995)
  ·
    refine ⟨17301713527947906799048493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11534475685298604532698995 17301713527947906799048493)
    ·
      refine ⟨6488142572980465049643185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17301713527947906799048493 6488142572980465049643185)
      ·
        refine ⟨4866106929735348787232389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6488142572980465049643185 4866106929735348787232389)
        ·
          refine ⟨912395049325377897606073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4866106929735348787232389 912395049325377897606073)
          ·
            refine ⟨684296286994033423204555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912395049325377897606073 684296286994033423204555)
            ·
              refine ⟨1026444430491050134806833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684296286994033423204555 1026444430491050134806833)
              ·
                refine ⟨769833322868287601105125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026444430491050134806833 769833322868287601105125)
                ·
                  refine ⟨144343748037803925207211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769833322868287601105125 144343748037803925207211)
                  ·
                    rfl

theorem cell20_316247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_316247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316247 prefixEnd_316247 := by exact prefixLift 316247
  have htrace : WordTrace (prefixWord ++ tailWord_316247) baseStart_316247 baseEnd_316247 := by
    simpa [prefixWord, tailWord_316247, baseEnd_316247] using wordTrace_append hprefix tailTrace_316247
  have hstable : (prefixWord ++ tailWord_316247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316247).length < 2 ^ (prefixWord ++ tailWord_316247).sum := by decide
  have hdescent : baseEnd_316247 < baseStart_316247 := by decide
  rcases family_descends (prefixWord ++ tailWord_316247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316264 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_316264 : Nat := 118140960795 + 316264 * 2 ^ 59
def prefixEnd_316264 : Nat := 4983230072969 + 3 ^ 40 * 316264 * 2
def baseEnd_316264 : Nat := 144351507301027421640475

theorem tailTrace_316264 : CollatzResearch.WordTrace tailWord_316264 prefixEnd_316264 144351507301027421640475 := by
  unfold tailWord_316264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767547863118508218033923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7690063817491344290711897 5767547863118508218033923)
  ·
    refine ⟨8651321794677762327050885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5767547863118508218033923 8651321794677762327050885)
    ·
      refine ⟨1622122836502080436322041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8651321794677762327050885 1622122836502080436322041)
      ·
        refine ⟨1216592127376560327241531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1622122836502080436322041 1216592127376560327241531)
        ·
          refine ⟨1824888191064840490862297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216592127376560327241531 1824888191064840490862297)
          ·
            refine ⟨1368666143298630368146723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824888191064840490862297 1368666143298630368146723)
            ·
              refine ⟨2052999214947945552220085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368666143298630368146723 2052999214947945552220085)
              ·
                refine ⟨192468676401369895520633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2052999214947945552220085 192468676401369895520633)
                ·
                  refine ⟨144351507301027421640475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192468676401369895520633 144351507301027421640475)
                  ·
                    rfl

theorem cell20_316264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_316264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316264 prefixEnd_316264 := by exact prefixLift 316264
  have htrace : WordTrace (prefixWord ++ tailWord_316264) baseStart_316264 baseEnd_316264 := by
    simpa [prefixWord, tailWord_316264, baseEnd_316264] using wordTrace_append hprefix tailTrace_316264
  have hstable : (prefixWord ++ tailWord_316264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316264).length < 2 ^ (prefixWord ++ tailWord_316264).sum := by decide
  have hdescent : baseEnd_316264 < baseStart_316264 := by decide
  rcases family_descends (prefixWord ++ tailWord_316264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316268 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_316268 : Nat := 118140960795 + 316268 * 2 ^ 59
def prefixEnd_316268 : Nat := 4983230072969 + 3 ^ 40 * 316268 * 2
def baseEnd_316268 : Nat := 144353333010021185507125

theorem tailTrace_316268 : CollatzResearch.WordTrace tailWord_316268 prefixEnd_316268 144353333010021185507125 := by
  unfold tailWord_316268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767620809111262559606729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7690161078815016746142305 5767620809111262559606729)
  ·
    refine ⟨4325715606833446919705047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5767620809111262559606729 4325715606833446919705047)
    ·
      refine ⟨6488573410250170379557571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325715606833446919705047 6488573410250170379557571)
      ·
        refine ⟨9732860115375255569336357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488573410250170379557571 9732860115375255569336357)
        ·
          refine ⟨1824911271632860419250567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9732860115375255569336357 1824911271632860419250567)
          ·
            refine ⟨2737366907449290628875851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824911271632860419250567 2737366907449290628875851)
            ·
              refine ⟨4106050361173935943313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737366907449290628875851 4106050361173935943313777)
              ·
                refine ⟨3079537770880451957485333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106050361173935943313777 3079537770880451957485333)
                ·
                  refine ⟨144353333010021185507125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3079537770880451957485333 144353333010021185507125)
                  ·
                    rfl

theorem cell20_316268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_316268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316268 prefixEnd_316268 := by exact prefixLift 316268
  have htrace : WordTrace (prefixWord ++ tailWord_316268) baseStart_316268 baseEnd_316268 := by
    simpa [prefixWord, tailWord_316268, baseEnd_316268] using wordTrace_append hprefix tailTrace_316268
  have hstable : (prefixWord ++ tailWord_316268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316268).length < 2 ^ (prefixWord ++ tailWord_316268).sum := by decide
  have hdescent : baseEnd_316268 < baseStart_316268 := by decide
  rcases family_descends (prefixWord ++ tailWord_316268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316295 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 3]
def baseStart_316295 : Nat := 118140960795 + 316295 * 2 ^ 59
def prefixEnd_316295 : Nat := 4983230072969 + 3 ^ 40 * 316295 * 2
def baseEnd_316295 : Nat := 144365656545729091607015

theorem tailTrace_316295 : CollatzResearch.WordTrace tailWord_316295 prefixEnd_316295 144365656545729091607015 := by
  unfold tailWord_316295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536226389124708730446339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7690817592749805820297559 11536226389124708730446339)
  ·
    refine ⟨17304339583687063095669509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11536226389124708730446339 17304339583687063095669509)
    ·
      refine ⟨3244563671941324330438033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17304339583687063095669509 3244563671941324330438033)
      ·
        refine ⟨2433422753955993247828525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3244563671941324330438033 2433422753955993247828525)
        ·
          refine ⟨912533532733497467935697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2433422753955993247828525 912533532733497467935697)
          ·
            refine ⟨684400149550123100951773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912533532733497467935697 684400149550123100951773)
            ·
              refine ⟨256650056081296162856915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 684400149550123100951773 256650056081296162856915)
              ·
                refine ⟨384975084121944244285373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256650056081296162856915 384975084121944244285373)
                ·
                  refine ⟨144365656545729091607015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384975084121944244285373 144365656545729091607015)
                  ·
                    rfl

theorem cell20_316295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_316295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316295 prefixEnd_316295 := by exact prefixLift 316295
  have htrace : WordTrace (prefixWord ++ tailWord_316295) baseStart_316295 baseEnd_316295 := by
    simpa [prefixWord, tailWord_316295, baseEnd_316295] using wordTrace_append hprefix tailTrace_316295
  have hstable : (prefixWord ++ tailWord_316295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316295).length < 2 ^ (prefixWord ++ tailWord_316295).sum := by decide
  have hdescent : baseEnd_316295 < baseStart_316295 := by decide
  rcases family_descends (prefixWord ++ tailWord_316295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316299 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_316299 : Nat := 118140960795 + 316299 * 2 ^ 59
def prefixEnd_316299 : Nat := 4983230072969 + 3 ^ 40 * 316299 * 2
def baseEnd_316299 : Nat := 144367482254722855473665

theorem tailTrace_316299 : CollatzResearch.WordTrace tailWord_316299 prefixEnd_316299 144367482254722855473665 := by
  unfold tailWord_316299
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536372281110217413591951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7690914854073478275727967 11536372281110217413591951)
  ·
    refine ⟨17304558421665326120387927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11536372281110217413591951 17304558421665326120387927)
    ·
      refine ⟨25956837632497989180581891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17304558421665326120387927 25956837632497989180581891)
      ·
        refine ⟨38935256448746983770872837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25956837632497989180581891 38935256448746983770872837)
        ·
          refine ⟨7300360584140059457038657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38935256448746983770872837 7300360584140059457038657)
          ·
            refine ⟨5475270438105044592778993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7300360584140059457038657 5475270438105044592778993)
            ·
              refine ⟨4106452828578783444584245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5475270438105044592778993 4106452828578783444584245)
              ·
                refine ⟨384979952679260947929773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4106452828578783444584245 384979952679260947929773)
                ·
                  refine ⟨144367482254722855473665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384979952679260947929773 144367482254722855473665)
                  ·
                    rfl

theorem cell20_316299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_316299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316299 prefixEnd_316299 := by exact prefixLift 316299
  have htrace : WordTrace (prefixWord ++ tailWord_316299) baseStart_316299 baseEnd_316299 := by
    simpa [prefixWord, tailWord_316299, baseEnd_316299] using wordTrace_append hprefix tailTrace_316299
  have hstable : (prefixWord ++ tailWord_316299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316299).length < 2 ^ (prefixWord ++ tailWord_316299).sum := by decide
  have hdescent : baseEnd_316299 < baseStart_316299 := by decide
  rcases family_descends (prefixWord ++ tailWord_316299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316309 : List Nat := [1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_316309 : Nat := 118140960795 + 316309 * 2 ^ 59
def prefixEnd_316309 : Nat := 4983230072969 + 3 ^ 40 * 316309 * 2
def baseEnd_316309 : Nat := 48124015509069088380097

theorem tailTrace_316309 : CollatzResearch.WordTrace tailWord_316309 prefixEnd_316309 48124015509069088380097 := by
  unfold tailWord_316309
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536737011073989121455981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7691158007382659414303987 11536737011073989121455981)
  ·
    refine ⟨4326276379152745920545993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11536737011073989121455981 4326276379152745920545993)
    ·
      refine ⟨3244707284364559440409495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4326276379152745920545993 3244707284364559440409495)
      ·
        refine ⟨4867060926546839160614243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244707284364559440409495 4867060926546839160614243)
        ·
          refine ⟨7300591389820258740921365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867060926546839160614243 7300591389820258740921365)
          ·
            refine ⟨342215221397824628480689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7300591389820258740921365 342215221397824628480689)
            ·
              refine ⟨256661416048368471360517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342215221397824628480689 256661416048368471360517)
              ·
                refine ⟨48124015509069088380097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256661416048368471360517 48124015509069088380097)
                ·
                  rfl

theorem cell20_316309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_316309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316309 prefixEnd_316309 := by exact prefixLift 316309
  have htrace : WordTrace (prefixWord ++ tailWord_316309) baseStart_316309 baseEnd_316309 := by
    simpa [prefixWord, tailWord_316309, baseEnd_316309] using wordTrace_append hprefix tailTrace_316309
  have hstable : (prefixWord ++ tailWord_316309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316309).length < 2 ^ (prefixWord ++ tailWord_316309).sum := by decide
  have hdescent : baseEnd_316309 < baseStart_316309 := by decide
  rcases family_descends (prefixWord ++ tailWord_316309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316319 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 2]
def baseStart_316319 : Nat := 118140960795 + 316319 * 2 ^ 59
def prefixEnd_316319 : Nat := 4983230072969 + 3 ^ 40 * 316319 * 2
def baseEnd_316319 : Nat := 144376610799691674806917

theorem tailTrace_316319 : CollatzResearch.WordTrace tailWord_316319 prefixEnd_316319 144376610799691674806917 := by
  unfold tailWord_316319
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537101741037760829320011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7691401160691840552880007 11537101741037760829320011)
  ·
    refine ⟨17305652611556641243980017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537101741037760829320011 17305652611556641243980017)
    ·
      refine ⟨12979239458667480932985013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17305652611556641243980017 12979239458667480932985013)
      ·
        refine ⟨1216803699250076337467345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12979239458667480932985013 1216803699250076337467345)
        ·
          refine ⟨912602774437557253100509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216803699250076337467345 912602774437557253100509)
          ·
            refine ⟨342226040414083969912691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 912602774437557253100509 342226040414083969912691)
            ·
              refine ⟨513339060621125954869037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342226040414083969912691 513339060621125954869037)
              ·
                refine ⟨192502147732922233075889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 513339060621125954869037 192502147732922233075889)
                ·
                  refine ⟨144376610799691674806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192502147732922233075889 144376610799691674806917)
                  ·
                    rfl

theorem cell20_316319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2].length) (baseStart_316319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316319 prefixEnd_316319 := by exact prefixLift 316319
  have htrace : WordTrace (prefixWord ++ tailWord_316319) baseStart_316319 baseEnd_316319 := by
    simpa [prefixWord, tailWord_316319, baseEnd_316319] using wordTrace_append hprefix tailTrace_316319
  have hstable : (prefixWord ++ tailWord_316319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316319).length < 2 ^ (prefixWord ++ tailWord_316319).sum := by decide
  have hdescent : baseEnd_316319 < baseStart_316319 := by decide
  rcases family_descends (prefixWord ++ tailWord_316319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316402 : List Nat := [3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_316402 : Nat := 118140960795 + 316402 * 2 ^ 59
def prefixEnd_316402 : Nat := 4983230072969 + 3 ^ 40 * 316402 * 2
def baseEnd_316402 : Nat := 48138164753770758346637

theorem tailTrace_316402 : CollatzResearch.WordTrace tailWord_316402 prefixEnd_316402 48138164753770758346637 := by
  unfold tailWord_316402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885032249934266501147865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7693419333158044003060973 2885032249934266501147865)
  ·
    refine ⟨2163774187450699875860899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2885032249934266501147865 2163774187450699875860899)
    ·
      refine ⟨3245661281176049813791349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2163774187450699875860899 3245661281176049813791349)
      ·
        refine ⟨304280745110254670042939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3245661281176049813791349 304280745110254670042939)
        ·
          refine ⟨456421117665382005064409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304280745110254670042939 456421117665382005064409)
          ·
            refine ⟨342315838249036503798307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456421117665382005064409 342315838249036503798307)
            ·
              refine ⟨513473757373554755697461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342315838249036503798307 513473757373554755697461)
              ·
                refine ⟨48138164753770758346637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513473757373554755697461 48138164753770758346637)
                ·
                  rfl

theorem cell20_316402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_316402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316402 prefixEnd_316402 := by exact prefixLift 316402
  have htrace : WordTrace (prefixWord ++ tailWord_316402) baseStart_316402 baseEnd_316402 := by
    simpa [prefixWord, tailWord_316402, baseEnd_316402] using wordTrace_append hprefix tailTrace_316402
  have hstable : (prefixWord ++ tailWord_316402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316402).length < 2 ^ (prefixWord ++ tailWord_316402).sum := by decide
  have hdescent : baseEnd_316402 < baseStart_316402 := by decide
  rcases family_descends (prefixWord ++ tailWord_316402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316444 : List Nat := [2, 2, 3, 1, 4, 1, 7]
def baseStart_316444 : Nat := 118140960795 + 316444 * 2 ^ 59
def prefixEnd_316444 : Nat := 4983230072969 + 3 ^ 40 * 316444 * 2
def baseEnd_316444 : Nat := 16048184911749643959971

theorem tailTrace_316444 : CollatzResearch.WordTrace tailWord_316444 prefixEnd_316444 16048184911749643959971 := by
  unfold tailWord_316444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770830432792453588810193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7694440577056604785080257 5770830432792453588810193)
  ·
    refine ⟨4328122824594340191607645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5770830432792453588810193 4328122824594340191607645)
    ·
      refine ⟨1623046059222877571852867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4328122824594340191607645 1623046059222877571852867)
      ·
        refine ⟨2434569088834316357779301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623046059222877571852867 2434569088834316357779301)
        ·
          refine ⟨456481704156434317083619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2434569088834316357779301 456481704156434317083619)
          ·
            refine ⟨684722556234651475625429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456481704156434317083619 684722556234651475625429)
            ·
              refine ⟨16048184911749643959971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 684722556234651475625429 16048184911749643959971)
              ·
                rfl

theorem cell20_316444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_316444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316444 prefixEnd_316444 := by exact prefixLift 316444
  have htrace : WordTrace (prefixWord ++ tailWord_316444) baseStart_316444 baseEnd_316444 := by
    simpa [prefixWord, tailWord_316444, baseEnd_316444] using wordTrace_append hprefix tailTrace_316444
  have hstable : (prefixWord ++ tailWord_316444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316444).length < 2 ^ (prefixWord ++ tailWord_316444).sum := by decide
  have hdescent : baseEnd_316444 < baseStart_316444 := by decide
  rcases family_descends (prefixWord ++ tailWord_316444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316451 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_316451 : Nat := 118140960795 + 316451 * 2 ^ 59
def prefixEnd_316451 : Nat := 4983230072969 + 3 ^ 40 * 316451 * 2
def baseEnd_316451 : Nat := 144436859196485882406377

theorem tailTrace_316451 : CollatzResearch.WordTrace tailWord_316451 prefixEnd_316451 144436859196485882406377 := by
  unfold tailWord_316451
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541916176559547373125207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694610784373031582083471 11541916176559547373125207)
  ·
    refine ⟨17312874264839321059687811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11541916176559547373125207 17312874264839321059687811)
    ·
      refine ⟨25969311397258981589531717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17312874264839321059687811 25969311397258981589531717)
      ·
        refine ⟨4869245886986059048037197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25969311397258981589531717 4869245886986059048037197)
        ·
          refine ⟨1825967207619772143013949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4869245886986059048037197 1825967207619772143013949)
          ·
            refine ⟨684737702857414553630231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1825967207619772143013949 684737702857414553630231)
            ·
              refine ⟨1027106554286121830445347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684737702857414553630231 1027106554286121830445347)
              ·
                refine ⟨1540659831429182745668021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027106554286121830445347 1540659831429182745668021)
                ·
                  refine ⟨144436859196485882406377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1540659831429182745668021 144436859196485882406377)
                  ·
                    rfl

theorem cell20_316451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_316451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_316451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_316451 prefixEnd_316451 := by exact prefixLift 316451
  have htrace : WordTrace (prefixWord ++ tailWord_316451) baseStart_316451 baseEnd_316451 := by
    simpa [prefixWord, tailWord_316451, baseEnd_316451] using wordTrace_append hprefix tailTrace_316451
  have hstable : (prefixWord ++ tailWord_316451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316451).length < 2 ^ (prefixWord ++ tailWord_316451).sum := by decide
  have hdescent : baseEnd_316451 < baseStart_316451 := by decide
  rcases family_descends (prefixWord ++ tailWord_316451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
