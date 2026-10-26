import V185TrunkScan21Chunk022

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_277496 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_277496 : Nat := 118140960795 + 277496 * 2 ^ 59
def prefixEnd_277496 : Nat := 4983230072969 + 3 ^ 40 * 277496 * 2
def baseEnd_277496 : Nat := 63328367866734013032811

theorem tailTrace_277496 : CollatzResearch.WordTrace tailWord_277496 prefixEnd_277496 63328367866734013032811 := by
  unfold tailWord_277496
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060555301343429694398171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6747407068457906259197561 5060555301343429694398171)
  ·
    refine ⟨7590832952015144541597257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5060555301343429694398171 7590832952015144541597257)
    ·
      refine ⟨5693124714011358406197943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7590832952015144541597257 5693124714011358406197943)
      ·
        refine ⟨8539687071017037609296915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693124714011358406197943 8539687071017037609296915)
        ·
          refine ⟨12809530606525556413945373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8539687071017037609296915 12809530606525556413945373)
          ·
            refine ⟨4803573977447083655229515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12809530606525556413945373 4803573977447083655229515)
            ·
              refine ⟨7205360966170625482844273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803573977447083655229515 7205360966170625482844273)
              ·
                refine ⟨5404020724627969112133205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205360966170625482844273 5404020724627969112133205)
                ·
                  refine ⟨63328367866734013032811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5404020724627969112133205 63328367866734013032811)
                  ·
                    rfl

theorem cell21_277496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_277496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277496 prefixEnd_277496 := by exact prefixLift 277496
  have htrace : WordTrace (prefixWord ++ tailWord_277496) baseStart_277496 baseEnd_277496 := by
    simpa [prefixWord, tailWord_277496, baseEnd_277496] using wordTrace_append hprefix tailTrace_277496
  have hstable : (prefixWord ++ tailWord_277496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277496).length < 2 ^ (prefixWord ++ tailWord_277496).sum := by decide
  have hdescent : baseEnd_277496 < baseStart_277496 := by decide
  rcases family_descends (prefixWord ++ tailWord_277496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277502 : List Nat := [4, 2, 2, 2, 2, 1, 3, 5]
def baseStart_277502 : Nat := 118140960795 + 277502 * 2 ^ 59
def prefixEnd_277502 : Nat := 4983230072969 + 3 ^ 40 * 277502 * 2
def baseEnd_277502 : Nat := 21109912382826445310933

theorem tailTrace_277502 : CollatzResearch.WordTrace tailWord_277502 prefixEnd_277502 21109912382826445310933 := by
  unfold tailWord_277502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265166180083140301689345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6747552960443414942343173 1265166180083140301689345)
  ·
    refine ⟨948874635062355226267009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1265166180083140301689345 948874635062355226267009)
    ·
      refine ⟨711655976296766419700257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948874635062355226267009 711655976296766419700257)
      ·
        refine ⟨533741982222574814775193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711655976296766419700257 533741982222574814775193)
        ·
          refine ⟨400306486666931111081395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533741982222574814775193 400306486666931111081395)
          ·
            refine ⟨600459730000396666622093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400306486666931111081395 600459730000396666622093)
            ·
              refine ⟨225172398750148749983285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600459730000396666622093 225172398750148749983285)
              ·
                refine ⟨21109912382826445310933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225172398750148749983285 21109912382826445310933)
                ·
                  rfl

theorem cell21_277502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_277502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277502 prefixEnd_277502 := by exact prefixLift 277502
  have htrace : WordTrace (prefixWord ++ tailWord_277502) baseStart_277502 baseEnd_277502 := by
    simpa [prefixWord, tailWord_277502, baseEnd_277502] using wordTrace_append hprefix tailTrace_277502
  have hstable : (prefixWord ++ tailWord_277502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277502).length < 2 ^ (prefixWord ++ tailWord_277502).sum := by decide
  have hdescent : baseEnd_277502 < baseStart_277502 := by decide
  rcases family_descends (prefixWord ++ tailWord_277502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277516 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_277516 : Nat := 118140960795 + 277516 * 2 ^ 59
def prefixEnd_277516 : Nat := 4983230072969 + 3 ^ 40 * 277516 * 2
def baseEnd_277516 : Nat := 63332932139218422699437

theorem tailTrace_277516 : CollatzResearch.WordTrace tailWord_277516 prefixEnd_277516 63332932139218422699437 := by
  unfold tailWord_277516
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060920031307201402262201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6747893375076268536349601 5060920031307201402262201)
  ·
    refine ⟨3795690023480401051696651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5060920031307201402262201 3795690023480401051696651)
    ·
      refine ⟨5693535035220601577544977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795690023480401051696651 5693535035220601577544977)
      ·
        refine ⟨4270151276415451183158733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5693535035220601577544977 4270151276415451183158733)
        ·
          refine ⟨1601306728655794193684525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4270151276415451183158733 1601306728655794193684525)
          ·
            refine ⟨600490023245922822631697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1601306728655794193684525 600490023245922822631697)
            ·
              refine ⟨450367517434442116973773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600490023245922822631697 450367517434442116973773)
              ·
                refine ⟨168887819037915793865165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 450367517434442116973773 168887819037915793865165)
                ·
                  refine ⟨63332932139218422699437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168887819037915793865165 63332932139218422699437)
                  ·
                    rfl

theorem cell21_277516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_277516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277516 prefixEnd_277516 := by exact prefixLift 277516
  have htrace : WordTrace (prefixWord ++ tailWord_277516) baseStart_277516 baseEnd_277516 := by
    simpa [prefixWord, tailWord_277516, baseEnd_277516] using wordTrace_append hprefix tailTrace_277516
  have hstable : (prefixWord ++ tailWord_277516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277516).length < 2 ^ (prefixWord ++ tailWord_277516).sum := by decide
  have hdescent : baseEnd_277516 < baseStart_277516 := by decide
  rcases family_descends (prefixWord ++ tailWord_277516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277522 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_277522 : Nat := 118140960795 + 277522 * 2 ^ 59
def prefixEnd_277522 : Nat := 4983230072969 + 3 ^ 40 * 277522 * 2
def baseEnd_277522 : Nat := 63334301420963745599425

theorem tailTrace_277522 : CollatzResearch.WordTrace tailWord_277522 prefixEnd_277522 63334301420963745599425 := by
  unfold tailWord_277522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530514725148166457310705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6748039267061777219495213 2530514725148166457310705)
  ·
    refine ⟨1897886043861124842983029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2530514725148166457310705 1897886043861124842983029)
    ·
      refine ⟨177926816611980454029659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1897886043861124842983029 177926816611980454029659)
      ·
        refine ⟨266890224917970681044489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177926816611980454029659 266890224917970681044489)
        ·
          refine ⟨200167668688478010783367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266890224917970681044489 200167668688478010783367)
          ·
            refine ⟨300251503032717016175051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200167668688478010783367 300251503032717016175051)
            ·
              refine ⟨450377254549075524262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300251503032717016175051 450377254549075524262577)
              ·
                refine ⟨337782940911806643196933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450377254549075524262577 337782940911806643196933)
                ·
                  refine ⟨63334301420963745599425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337782940911806643196933 63334301420963745599425)
                  ·
                    rfl

theorem cell21_277522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_277522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277522 prefixEnd_277522 := by exact prefixLift 277522
  have htrace : WordTrace (prefixWord ++ tailWord_277522) baseStart_277522 baseEnd_277522 := by
    simpa [prefixWord, tailWord_277522, baseEnd_277522] using wordTrace_append hprefix tailTrace_277522
  have hstable : (prefixWord ++ tailWord_277522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277522).length < 2 ^ (prefixWord ++ tailWord_277522).sum := by decide
  have hdescent : baseEnd_277522 < baseStart_277522 := by decide
  rcases family_descends (prefixWord ++ tailWord_277522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277561 : List Nat := [1, 2, 1, 5, 2, 3, 2, 5]
def baseStart_277561 : Nat := 118140960795 + 277561 * 2 ^ 59
def prefixEnd_277561 : Nat := 4983230072969 + 3 ^ 40 * 277561 * 2
def baseEnd_277561 : Nat := 21114400584102781483115

theorem tailTrace_277561 : CollatzResearch.WordTrace tailWord_277561 prefixEnd_277561 21114400584102781483115 := by
  unfold tailWord_277561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123481347451375489912537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6748987564967583659941691 10123481347451375489912537)
  ·
    refine ⟨7592611010588531617434403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10123481347451375489912537 7592611010588531617434403)
    ·
      refine ⟨11388916515882797426151605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7592611010588531617434403 11388916515882797426151605)
      ·
        refine ⟨1067710923364012258701713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11388916515882797426151605 1067710923364012258701713)
        ·
          refine ⟨800783192523009194026285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067710923364012258701713 800783192523009194026285)
          ·
            refine ⟨300293697196128447759857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800783192523009194026285 300293697196128447759857)
            ·
              refine ⟨225220272897096335819893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300293697196128447759857 225220272897096335819893)
              ·
                refine ⟨21114400584102781483115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225220272897096335819893 21114400584102781483115)
                ·
                  rfl

theorem cell21_277561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 5].length) (baseStart_277561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277561 prefixEnd_277561 := by exact prefixLift 277561
  have htrace : WordTrace (prefixWord ++ tailWord_277561) baseStart_277561 baseEnd_277561 := by
    simpa [prefixWord, tailWord_277561, baseEnd_277561] using wordTrace_append hprefix tailTrace_277561
  have hstable : (prefixWord ++ tailWord_277561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277561).length < 2 ^ (prefixWord ++ tailWord_277561).sum := by decide
  have hdescent : baseEnd_277561 < baseStart_277561 := by decide
  rcases family_descends (prefixWord ++ tailWord_277561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277589 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_277589 : Nat := 118140960795 + 277589 * 2 ^ 59
def prefixEnd_277589 : Nat := 4983230072969 + 3 ^ 40 * 277589 * 2
def baseEnd_277589 : Nat := 63349591733786517982621

theorem tailTrace_277589 : CollatzResearch.WordTrace tailWord_277589 prefixEnd_277589 63349591733786517982621 := by
  unfold tailWord_277589
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124502591349936271931821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6749668394233290847954547 10124502591349936271931821)
  ·
    refine ⟨3796688471756226101974433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10124502591349936271931821 3796688471756226101974433)
    ·
      refine ⟨2847516353817169576480825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3796688471756226101974433 2847516353817169576480825)
      ·
        refine ⟨2135637265362877182360619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2847516353817169576480825 2135637265362877182360619)
        ·
          refine ⟨3203455898044315773540929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135637265362877182360619 3203455898044315773540929)
          ·
            refine ⟨2402591923533236830155697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203455898044315773540929 2402591923533236830155697)
            ·
              refine ⟨1801943942649927622616773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2402591923533236830155697 1801943942649927622616773)
              ·
                refine ⟨337864489246861429240645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1801943942649927622616773 337864489246861429240645)
                ·
                  refine ⟨63349591733786517982621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337864489246861429240645 63349591733786517982621)
                  ·
                    rfl

theorem cell21_277589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_277589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277589 prefixEnd_277589 := by exact prefixLift 277589
  have htrace : WordTrace (prefixWord ++ tailWord_277589) baseStart_277589 baseEnd_277589 := by
    simpa [prefixWord, tailWord_277589, baseEnd_277589] using wordTrace_append hprefix tailTrace_277589
  have hstable : (prefixWord ++ tailWord_277589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277589).length < 2 ^ (prefixWord ++ tailWord_277589).sum := by decide
  have hdescent : baseEnd_277589 < baseStart_277589 := by decide
  rcases family_descends (prefixWord ++ tailWord_277589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277592 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_277592 : Nat := 118140960795 + 277592 * 2 ^ 59
def prefixEnd_277592 : Nat := 4983230072969 + 3 ^ 40 * 277592 * 2
def baseEnd_277592 : Nat := 63350276374659179432615

theorem tailTrace_277592 : CollatzResearch.WordTrace tailWord_277592 prefixEnd_277592 63350276374659179432615 := by
  unfold tailWord_277592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062306005169533892145515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6749741340226045189527353 5062306005169533892145515)
  ·
    refine ⟨7593459007754300838218273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5062306005169533892145515 7593459007754300838218273)
    ·
      refine ⟨5695094255815725628663705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7593459007754300838218273 5695094255815725628663705)
      ·
        refine ⟨4271320691861794221497779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5695094255815725628663705 4271320691861794221497779)
        ·
          refine ⟨6406981037792691332246669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271320691861794221497779 6406981037792691332246669)
          ·
            refine ⟨2402617889172259249592501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6406981037792691332246669 2402617889172259249592501)
            ·
              refine ⟨225245427109899304649297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2402617889172259249592501 225245427109899304649297)
              ·
                refine ⟨168934070332424478486973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225245427109899304649297 168934070332424478486973)
                ·
                  refine ⟨63350276374659179432615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168934070332424478486973 63350276374659179432615)
                  ·
                    rfl

theorem cell21_277592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_277592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277592 prefixEnd_277592 := by exact prefixLift 277592
  have htrace : WordTrace (prefixWord ++ tailWord_277592) baseStart_277592 baseEnd_277592 := by
    simpa [prefixWord, tailWord_277592, baseEnd_277592] using wordTrace_append hprefix tailTrace_277592
  have hstable : (prefixWord ++ tailWord_277592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277592).length < 2 ^ (prefixWord ++ tailWord_277592).sum := by decide
  have hdescent : baseEnd_277592 < baseStart_277592 := by decide
  rcases family_descends (prefixWord ++ tailWord_277592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277665 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_277665 : Nat := 118140960795 + 277665 * 2 ^ 59
def prefixEnd_277665 : Nat := 4983230072969 + 3 ^ 40 * 277665 * 2
def baseEnd_277665 : Nat := 63366935969227274715799

theorem tailTrace_277665 : CollatzResearch.WordTrace tailWord_277665 prefixEnd_277665 63366935969227274715799 := by
  unfold tailWord_277665
  simp only [CollatzResearch.WordTrace]
  refine ⟨10127274539074601251698449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6751516359383067501132299 10127274539074601251698449)
  ·
    refine ⟨7595455904305950938773837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10127274539074601251698449 7595455904305950938773837)
    ·
      refine ⟨2848295964114731602040189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7595455904305950938773837 2848295964114731602040189)
      ·
        refine ⟨1068110986543024350765071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2848295964114731602040189 1068110986543024350765071)
        ·
          refine ⟨1602166479814536526147607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068110986543024350765071 1602166479814536526147607)
          ·
            refine ⟨2403249719721804789221411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602166479814536526147607 2403249719721804789221411)
            ·
              refine ⟨3604874579582707183832117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403249719721804789221411 3604874579582707183832117)
              ·
                refine ⟨337956991835878798484261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3604874579582707183832117 337956991835878798484261)
                ·
                  refine ⟨63366935969227274715799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337956991835878798484261 63366935969227274715799)
                  ·
                    rfl

theorem cell21_277665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_277665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277665 prefixEnd_277665 := by exact prefixLift 277665
  have htrace : WordTrace (prefixWord ++ tailWord_277665) baseStart_277665 baseEnd_277665 := by
    simpa [prefixWord, tailWord_277665, baseEnd_277665] using wordTrace_append hprefix tailTrace_277665
  have hstable : (prefixWord ++ tailWord_277665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277665).length < 2 ^ (prefixWord ++ tailWord_277665).sum := by decide
  have hdescent : baseEnd_277665 < baseStart_277665 := by decide
  rcases family_descends (prefixWord ++ tailWord_277665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277702 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_277702 : Nat := 118140960795 + 277702 * 2 ^ 59
def prefixEnd_277702 : Nat := 4983230072969 + 3 ^ 40 * 277702 * 2
def baseEnd_277702 : Nat := 63375379873323432599057

theorem tailTrace_277702 : CollatzResearch.WordTrace tailWord_277702 prefixEnd_277702 63375379873323432599057 := by
  unfold tailWord_277702
  simp only [CollatzResearch.WordTrace]
  refine ⟨316519501248142392837355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6752416026627037713863573 316519501248142392837355)
  ·
    refine ⟨474779251872213589256033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316519501248142392837355 474779251872213589256033)
    ·
      refine ⟨356084438904160191942025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474779251872213589256033 356084438904160191942025)
      ·
        refine ⟨267063329178120143956519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356084438904160191942025 267063329178120143956519)
        ·
          refine ⟨400594993767180215934779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267063329178120143956519 400594993767180215934779)
          ·
            refine ⟨600892490650770323902169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400594993767180215934779 600892490650770323902169)
            ·
              refine ⟨450669367988077742926627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600892490650770323902169 450669367988077742926627)
              ·
                refine ⟨676004051982116614389941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450669367988077742926627 676004051982116614389941)
                ·
                  refine ⟨63375379873323432599057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676004051982116614389941 63375379873323432599057)
                  ·
                    rfl

theorem cell21_277702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_277702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277702 prefixEnd_277702 := by exact prefixLift 277702
  have htrace : WordTrace (prefixWord ++ tailWord_277702) baseStart_277702 baseEnd_277702 := by
    simpa [prefixWord, tailWord_277702, baseEnd_277702] using wordTrace_append hprefix tailTrace_277702
  have hstable : (prefixWord ++ tailWord_277702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277702).length < 2 ^ (prefixWord ++ tailWord_277702).sum := by decide
  have hdescent : baseEnd_277702 < baseStart_277702 := by decide
  rcases family_descends (prefixWord ++ tailWord_277702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277716 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_277716 : Nat := 118140960795 + 277716 * 2 ^ 59
def prefixEnd_277716 : Nat := 4983230072969 + 3 ^ 40 * 277716 * 2
def baseEnd_277716 : Nat := 63378574864062519365695

theorem tailTrace_277716 : CollatzResearch.WordTrace tailWord_277716 prefixEnd_277716 63378574864062519365695 := by
  unfold tailWord_277716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064567330944918480902501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6752756441259891307870001 5064567330944918480902501)
  ·
    refine ⟨949606374552172215169219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5064567330944918480902501 949606374552172215169219)
    ·
      refine ⟨1424409561828258322753829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949606374552172215169219 1424409561828258322753829)
      ·
        refine ⟨267076792842798435516343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1424409561828258322753829 267076792842798435516343)
        ·
          refine ⟨400615189264197653274515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267076792842798435516343 400615189264197653274515)
          ·
            refine ⟨600922783896296479911773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400615189264197653274515 600922783896296479911773)
            ·
              refine ⟨225346043961111179966915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600922783896296479911773 225346043961111179966915)
              ·
                refine ⟨338019065941666769950373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225346043961111179966915 338019065941666769950373)
                ·
                  refine ⟨63378574864062519365695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338019065941666769950373 63378574864062519365695)
                  ·
                    rfl

theorem cell21_277716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_277716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277716 prefixEnd_277716 := by exact prefixLift 277716
  have htrace : WordTrace (prefixWord ++ tailWord_277716) baseStart_277716 baseEnd_277716 := by
    simpa [prefixWord, tailWord_277716, baseEnd_277716] using wordTrace_append hprefix tailTrace_277716
  have hstable : (prefixWord ++ tailWord_277716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277716).length < 2 ^ (prefixWord ++ tailWord_277716).sum := by decide
  have hdescent : baseEnd_277716 < baseStart_277716 := by decide
  rcases family_descends (prefixWord ++ tailWord_277716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277741 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_277741 : Nat := 118140960795 + 277741 * 2 ^ 59
def prefixEnd_277741 : Nat := 4983230072969 + 3 ^ 40 * 277741 * 2
def baseEnd_277741 : Nat := 63384280204668031448977

theorem tailTrace_277741 : CollatzResearch.WordTrace tailWord_277741 prefixEnd_277741 63384280204668031448977 := by
  unfold tailWord_277741
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130046486799266231465077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6753364324532844154310051 10130046486799266231465077)
  ·
    refine ⟨949691858137431209199851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10130046486799266231465077 949691858137431209199851)
    ·
      refine ⟨1424537787206146813799777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949691858137431209199851 1424537787206146813799777)
      ·
        refine ⟨1068403340404610110349833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1424537787206146813799777 1068403340404610110349833)
        ·
          refine ⟨801302505303457582762375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068403340404610110349833 801302505303457582762375)
          ·
            refine ⟨1201953757955186374143563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801302505303457582762375 1201953757955186374143563)
            ·
              refine ⟨1802930636932779561215345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201953757955186374143563 1802930636932779561215345)
              ·
                refine ⟨1352197977699584670911509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802930636932779561215345 1352197977699584670911509)
                ·
                  refine ⟨63384280204668031448977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1352197977699584670911509 63384280204668031448977)
                  ·
                    rfl

theorem cell21_277741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_277741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277741 prefixEnd_277741 := by exact prefixLift 277741
  have htrace : WordTrace (prefixWord ++ tailWord_277741) baseStart_277741 baseEnd_277741 := by
    simpa [prefixWord, tailWord_277741, baseEnd_277741] using wordTrace_append hprefix tailTrace_277741
  have hstable : (prefixWord ++ tailWord_277741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277741).length < 2 ^ (prefixWord ++ tailWord_277741).sum := by decide
  have hdescent : baseEnd_277741 < baseStart_277741 := by decide
  rcases family_descends (prefixWord ++ tailWord_277741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277820 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_277820 : Nat := 118140960795 + 277820 * 2 ^ 59
def prefixEnd_277820 : Nat := 4983230072969 + 3 ^ 40 * 277820 * 2
def baseEnd_277820 : Nat := 63402309080981449632149

theorem tailTrace_277820 : CollatzResearch.WordTrace tailWord_277820 prefixEnd_277820 63402309080981449632149 := by
  unfold tailWord_277820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066463926756531361795457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6755285235675375149060609 5066463926756531361795457)
  ·
    refine ⟨3799847945067398521346593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5066463926756531361795457 3799847945067398521346593)
    ·
      refine ⟨2849885958800548891009945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3799847945067398521346593 2849885958800548891009945)
      ·
        refine ⟨2137414469100411668257459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849885958800548891009945 2137414469100411668257459)
        ·
          refine ⟨3206121703650617502386189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137414469100411668257459 3206121703650617502386189)
          ·
            refine ⟨1202295638868981563394821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3206121703650617502386189 1202295638868981563394821)
            ·
              refine ⟨225430432287934043136529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1202295638868981563394821 225430432287934043136529)
              ·
                refine ⟨169072824215950532352397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225430432287934043136529 169072824215950532352397)
                ·
                  refine ⟨63402309080981449632149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169072824215950532352397 63402309080981449632149)
                  ·
                    rfl

theorem cell21_277820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_277820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277820 prefixEnd_277820 := by exact prefixLift 277820
  have htrace : WordTrace (prefixWord ++ tailWord_277820) baseStart_277820 baseEnd_277820 := by
    simpa [prefixWord, tailWord_277820, baseEnd_277820] using wordTrace_append hprefix tailTrace_277820
  have hstable : (prefixWord ++ tailWord_277820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277820).length < 2 ^ (prefixWord ++ tailWord_277820).sum := by decide
  have hdescent : baseEnd_277820 < baseStart_277820 := by decide
  rcases family_descends (prefixWord ++ tailWord_277820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277831 : List Nat := [1, 1, 4, 1, 2, 3, 3, 6]
def baseStart_277831 : Nat := 118140960795 + 277831 * 2 ^ 59
def prefixEnd_277831 : Nat := 4983230072969 + 3 ^ 40 * 277831 * 2
def baseEnd_277831 : Nat := 21134939810282624982931

theorem tailTrace_277831 : CollatzResearch.WordTrace tailWord_277831 prefixEnd_277831 21134939810282624982931 := by
  unfold tailWord_277831
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133329056473211602241347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6755552704315474401494231 10133329056473211602241347)
  ·
    refine ⟨15199993584709817403362021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133329056473211602241347 15199993584709817403362021)
    ·
      refine ⟨2849998797133090763130379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15199993584709817403362021 2849998797133090763130379)
      ·
        refine ⟨4274998195699636144695569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849998797133090763130379 4274998195699636144695569)
        ·
          refine ⟨3206248646774727108521677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4274998195699636144695569 3206248646774727108521677)
          ·
            refine ⟨1202343242540522665695629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3206248646774727108521677 1202343242540522665695629)
            ·
              refine ⟨450878715952695999635861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202343242540522665695629 450878715952695999635861)
              ·
                refine ⟨21134939810282624982931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 450878715952695999635861 21134939810282624982931)
                ·
                  rfl

theorem cell21_277831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_277831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277831 prefixEnd_277831 := by exact prefixLift 277831
  have htrace : WordTrace (prefixWord ++ tailWord_277831) baseStart_277831 baseEnd_277831 := by
    simpa [prefixWord, tailWord_277831, baseEnd_277831] using wordTrace_append hprefix tailTrace_277831
  have hstable : (prefixWord ++ tailWord_277831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277831).length < 2 ^ (prefixWord ++ tailWord_277831).sum := by decide
  have hdescent : baseEnd_277831 < baseStart_277831 := by decide
  rcases family_descends (prefixWord ++ tailWord_277831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277989 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 3]
def baseStart_277989 : Nat := 118140960795 + 277989 * 2 ^ 59
def prefixEnd_277989 : Nat := 4983230072969 + 3 ^ 40 * 277989 * 2
def baseEnd_277989 : Nat := 63440877183474711315137

theorem tailTrace_277989 : CollatzResearch.WordTrace tailWord_277989 prefixEnd_277989 63440877183474711315137 := by
  unfold tailWord_277989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139091789900804586493021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6759394526600536390995347 10139091789900804586493021)
  ·
    refine ⟨3802159421212801719934883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10139091789900804586493021 3802159421212801719934883)
    ·
      refine ⟨5703239131819202579902325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3802159421212801719934883 5703239131819202579902325)
      ·
        refine ⟨534678668608050241865843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5703239131819202579902325 534678668608050241865843)
        ·
          refine ⟨802018002912075362798765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534678668608050241865843 802018002912075362798765)
          ·
            refine ⟨300756751092028261049537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 802018002912075362798765 300756751092028261049537)
            ·
              refine ⟨225567563319021195787153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300756751092028261049537 225567563319021195787153)
              ·
                refine ⟨169175672489265896840365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225567563319021195787153 169175672489265896840365)
                ·
                  refine ⟨63440877183474711315137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169175672489265896840365 63440877183474711315137)
                  ·
                    rfl

theorem cell21_277989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_277989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277989 prefixEnd_277989 := by exact prefixLift 277989
  have htrace : WordTrace (prefixWord ++ tailWord_277989) baseStart_277989 baseEnd_277989 := by
    simpa [prefixWord, tailWord_277989, baseEnd_277989] using wordTrace_append hprefix tailTrace_277989
  have hstable : (prefixWord ++ tailWord_277989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277989).length < 2 ^ (prefixWord ++ tailWord_277989).sum := by decide
  have hdescent : baseEnd_277989 < baseStart_277989 := by decide
  rcases family_descends (prefixWord ++ tailWord_277989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278093 : List Nat := [1, 6, 1, 1, 4, 1, 7]
def baseStart_278093 : Nat := 118140960795 + 278093 * 2 ^ 59
def prefixEnd_278093 : Nat := 4983230072969 + 3 ^ 40 * 278093 * 2
def baseEnd_278093 : Nat := 7051623488932626842399

theorem tailTrace_278093 : CollatzResearch.WordTrace tailWord_278093 prefixEnd_278093 7051623488932626842399 := by
  unfold tailWord_278093
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142884981524030348278933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6761923321016020232185955 10142884981524030348278933)
  ·
    refine ⟨475447733508938922575575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10142884981524030348278933 475447733508938922575575)
    ·
      refine ⟨713171600263408383863363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475447733508938922575575 713171600263408383863363)
      ·
        refine ⟨1069757400395112575795045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713171600263408383863363 1069757400395112575795045)
        ·
          refine ⟨200579512574083607961571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1069757400395112575795045 200579512574083607961571)
          ·
            refine ⟨300869268861125411942357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200579512574083607961571 300869268861125411942357)
            ·
              refine ⟨7051623488932626842399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 300869268861125411942357 7051623488932626842399)
              ·
                rfl

theorem cell21_278093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 7].length) (baseStart_278093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278093 prefixEnd_278093 := by exact prefixLift 278093
  have htrace : WordTrace (prefixWord ++ tailWord_278093) baseStart_278093 baseEnd_278093 := by
    simpa [prefixWord, tailWord_278093, baseEnd_278093] using wordTrace_append hprefix tailTrace_278093
  have hstable : (prefixWord ++ tailWord_278093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278093).length < 2 ^ (prefixWord ++ tailWord_278093).sum := by decide
  have hdescent : baseEnd_278093 < baseStart_278093 := by decide
  rcases family_descends (prefixWord ++ tailWord_278093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278104 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_278104 : Nat := 118140960795 + 278104 * 2 ^ 59
def prefixEnd_278104 : Nat := 4983230072969 + 3 ^ 40 * 278104 * 2
def baseEnd_278104 : Nat := 63467121750260066898235

theorem tailTrace_278104 : CollatzResearch.WordTrace tailWord_278104 prefixEnd_278104 63467121750260066898235 := by
  unfold tailWord_278104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071643092242089613464683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6762190789656119484619577 5071643092242089613464683)
  ·
    refine ⟨7607464638363134420197025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5071643092242089613464683 7607464638363134420197025)
    ·
      refine ⟨5705598478772350815147769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7607464638363134420197025 5705598478772350815147769)
      ·
        refine ⟨4279198859079263111360827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5705598478772350815147769 4279198859079263111360827)
        ·
          refine ⟨6418798288618894667041241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279198859079263111360827 6418798288618894667041241)
          ·
            refine ⟨4814098716464171000280931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418798288618894667041241 4814098716464171000280931)
            ·
              refine ⟨7221148074696256500421397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814098716464171000280931 7221148074696256500421397)
              ·
                refine ⟨338491316001387023457253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7221148074696256500421397 338491316001387023457253)
                ·
                  refine ⟨63467121750260066898235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338491316001387023457253 63467121750260066898235)
                  ·
                    rfl

theorem cell21_278104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_278104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278104 prefixEnd_278104 := by exact prefixLift 278104
  have htrace : WordTrace (prefixWord ++ tailWord_278104) baseStart_278104 baseEnd_278104 := by
    simpa [prefixWord, tailWord_278104, baseEnd_278104] using wordTrace_append hprefix tailTrace_278104
  have hstable : (prefixWord ++ tailWord_278104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278104).length < 2 ^ (prefixWord ++ tailWord_278104).sum := by decide
  have hdescent : baseEnd_278104 < baseStart_278104 := by decide
  rcases family_descends (prefixWord ++ tailWord_278104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278121 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 4]
def baseStart_278121 : Nat := 118140960795 + 278121 * 2 ^ 59
def prefixEnd_278121 : Nat := 4983230072969 + 3 ^ 40 * 278121 * 2
def baseEnd_278121 : Nat := 63471001381871815114867

theorem tailTrace_278121 : CollatzResearch.WordTrace tailWord_278121 prefixEnd_278121 63471001381871815114867 := by
  unfold tailWord_278121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143906225422591130298217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6762604150281727420198811 10143906225422591130298217)
  ·
    refine ⟨7607929669066943347723663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10143906225422591130298217 7607929669066943347723663)
    ·
      refine ⟨11411894503600415021585495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7607929669066943347723663 11411894503600415021585495)
      ·
        refine ⟨17117841755400622532378243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11411894503600415021585495 17117841755400622532378243)
        ·
          refine ⟨25676762633100933798567365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17117841755400622532378243 25676762633100933798567365)
          ·
            refine ⟨4814392993706425087231381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25676762633100933798567365 4814392993706425087231381)
            ·
              refine ⟨225674671579988675963971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4814392993706425087231381 225674671579988675963971)
              ·
                refine ⟨338512007369983013945957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225674671579988675963971 338512007369983013945957)
                ·
                  refine ⟨63471001381871815114867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338512007369983013945957 63471001381871815114867)
                  ·
                    rfl

theorem cell21_278121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_278121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278121 prefixEnd_278121 := by exact prefixLift 278121
  have htrace : WordTrace (prefixWord ++ tailWord_278121) baseStart_278121 baseEnd_278121 := by
    simpa [prefixWord, tailWord_278121, baseEnd_278121] using wordTrace_append hprefix tailTrace_278121
  have hstable : (prefixWord ++ tailWord_278121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278121).length < 2 ^ (prefixWord ++ tailWord_278121).sum := by decide
  have hdescent : baseEnd_278121 < baseStart_278121 := by decide
  rcases family_descends (prefixWord ++ tailWord_278121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278152 : List Nat := [2, 1, 3, 5, 2, 8]
def baseStart_278152 : Nat := 118140960795 + 278152 * 2 ^ 59
def prefixEnd_278152 : Nat := 4983230072969 + 3 ^ 40 * 278152 * 2
def baseEnd_278152 : Nat := 2351039852008246299931

theorem tailTrace_278152 : CollatzResearch.WordTrace tailWord_278152 prefixEnd_278152 2351039852008246299931 := by
  unfold tailWord_278152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5072518444155141712338355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6763357925540188949784473 5072518444155141712338355)
  ·
    refine ⟨7608777666232712568507533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5072518444155141712338355 7608777666232712568507533)
    ·
      refine ⟨2853291624837267213190325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7608777666232712568507533 2853291624837267213190325)
      ·
        refine ⟨267496089828493801236593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2853291624837267213190325 267496089828493801236593)
        ·
          refine ⟨200622067371370350927445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267496089828493801236593 200622067371370350927445)
          ·
            refine ⟨2351039852008246299931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 200622067371370350927445 2351039852008246299931)
            ·
              rfl

theorem cell21_278152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 8].length) (baseStart_278152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278152 prefixEnd_278152 := by exact prefixLift 278152
  have htrace : WordTrace (prefixWord ++ tailWord_278152) baseStart_278152 baseEnd_278152 := by
    simpa [prefixWord, tailWord_278152, baseEnd_278152] using wordTrace_append hprefix tailTrace_278152
  have hstable : (prefixWord ++ tailWord_278152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278152).length < 2 ^ (prefixWord ++ tailWord_278152).sum := by decide
  have hdescent : baseEnd_278152 < baseStart_278152 := by decide
  rcases family_descends (prefixWord ++ tailWord_278152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278194 : List Nat := [3, 2, 1, 1, 1, 2, 2, 9]
def baseStart_278194 : Nat := 118140960795 + 278194 * 2 ^ 59
def prefixEnd_278194 : Nat := 4983230072969 + 3 ^ 40 * 278194 * 2
def baseEnd_278194 : Nat := 21162553658813303466017

theorem tailTrace_278194 : CollatzResearch.WordTrace tailWord_278194 prefixEnd_278194 21162553658813303466017 := by
  unfold tailWord_278194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536642188539531149426409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6764379169438749731803757 2536642188539531149426409)
  ·
    refine ⟨1902481641404648362069807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2536642188539531149426409 1902481641404648362069807)
    ·
      refine ⟨2853722462106972543104711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902481641404648362069807 2853722462106972543104711)
      ·
        refine ⟨4280583693160458814657067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853722462106972543104711 4280583693160458814657067)
        ·
          refine ⟨6420875539740688221985601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280583693160458814657067 6420875539740688221985601)
          ·
            refine ⟨4815656654805516166489201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6420875539740688221985601 4815656654805516166489201)
            ·
              refine ⟨3611742491104137124866901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4815656654805516166489201 3611742491104137124866901)
              ·
                refine ⟨21162553658813303466017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3611742491104137124866901 21162553658813303466017)
                ·
                  rfl

theorem cell21_278194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_278194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278194 prefixEnd_278194 := by exact prefixLift 278194
  have htrace : WordTrace (prefixWord ++ tailWord_278194) baseStart_278194 baseEnd_278194 := by
    simpa [prefixWord, tailWord_278194, baseEnd_278194] using wordTrace_append hprefix tailTrace_278194
  have hstable : (prefixWord ++ tailWord_278194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278194).length < 2 ^ (prefixWord ++ tailWord_278194).sum := by decide
  have hdescent : baseEnd_278194 < baseStart_278194 := by decide
  rcases family_descends (prefixWord ++ tailWord_278194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278225 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_278225 : Nat := 118140960795 + 278225 * 2 ^ 59
def prefixEnd_278225 : Nat := 4983230072969 + 3 ^ 40 * 278225 * 2
def baseEnd_278225 : Nat := 63494735598790745381321

theorem tailTrace_278225 : CollatzResearch.WordTrace tailWord_278225 prefixEnd_278225 63494735598790745381321 := by
  unfold tailWord_278225
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147699417045816892084129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6765132944697211261389419 10147699417045816892084129)
  ·
    refine ⟨7610774562784362669063097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10147699417045816892084129 7610774562784362669063097)
    ·
      refine ⟨5708080922088272001797323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7610774562784362669063097 5708080922088272001797323)
      ·
        refine ⟨8562121383132408002695985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5708080922088272001797323 8562121383132408002695985)
        ·
          refine ⟨6421591037349306002021989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8562121383132408002695985 6421591037349306002021989)
          ·
            refine ⟨1204048319502994875379123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6421591037349306002021989 1204048319502994875379123)
            ·
              refine ⟨1806072479254492313068685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204048319502994875379123 1806072479254492313068685)
              ·
                refine ⟨677277179720434617400757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806072479254492313068685 677277179720434617400757)
                ·
                  refine ⟨63494735598790745381321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 677277179720434617400757 63494735598790745381321)
                  ·
                    rfl

theorem cell21_278225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_278225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278225 prefixEnd_278225 := by exact prefixLift 278225
  have htrace : WordTrace (prefixWord ++ tailWord_278225) baseStart_278225 baseEnd_278225 := by
    simpa [prefixWord, tailWord_278225, baseEnd_278225] using wordTrace_append hprefix tailTrace_278225
  have hstable : (prefixWord ++ tailWord_278225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278225).length < 2 ^ (prefixWord ++ tailWord_278225).sum := by decide
  have hdescent : baseEnd_278225 < baseStart_278225 := by decide
  rcases family_descends (prefixWord ++ tailWord_278225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278276 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_278276 : Nat := 118140960795 + 278276 * 2 ^ 59
def prefixEnd_278276 : Nat := 4983230072969 + 3 ^ 40 * 278276 * 2
def baseEnd_278276 : Nat := 63506374493625990031217

theorem tailTrace_278276 : CollatzResearch.WordTrace tailWord_278276 prefixEnd_278276 63506374493625990031217 := by
  unfold tailWord_278276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074779769930526301095341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6766373026574035068127121 5074779769930526301095341)
  ·
    refine ⟨1903042413723947362910753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5074779769930526301095341 1903042413723947362910753)
    ·
      refine ⟨1427281810292960522183065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1903042413723947362910753 1427281810292960522183065)
      ·
        refine ⟨1070461357719720391637299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1427281810292960522183065 1070461357719720391637299)
        ·
          refine ⟨1605692036579580587455949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070461357719720391637299 1605692036579580587455949)
          ·
            refine ⟨602134513717342720295981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1605692036579580587455949 602134513717342720295981)
            ·
              refine ⟨225800442644003520110993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 602134513717342720295981 225800442644003520110993)
              ·
                refine ⟨169350331983002640083245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225800442644003520110993 169350331983002640083245)
                ·
                  refine ⟨63506374493625990031217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169350331983002640083245 63506374493625990031217)
                  ·
                    rfl

theorem cell21_278276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_278276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278276 prefixEnd_278276 := by exact prefixLift 278276
  have htrace : WordTrace (prefixWord ++ tailWord_278276) baseStart_278276 baseEnd_278276 := by
    simpa [prefixWord, tailWord_278276, baseEnd_278276] using wordTrace_append hprefix tailTrace_278276
  have hstable : (prefixWord ++ tailWord_278276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278276).length < 2 ^ (prefixWord ++ tailWord_278276).sum := by decide
  have hdescent : baseEnd_278276 < baseStart_278276 := by decide
  rcases family_descends (prefixWord ++ tailWord_278276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278290 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_278290 : Nat := 118140960795 + 278290 * 2 ^ 59
def prefixEnd_278290 : Nat := 4983230072969 + 3 ^ 40 * 278290 * 2
def baseEnd_278290 : Nat := 63509569484365076797855

theorem tailTrace_278290 : CollatzResearch.WordTrace tailWord_278290 prefixEnd_278290 63509569484365076797855 := by
  unfold tailWord_278290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537517540452583248300081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6766713441206888662133549 2537517540452583248300081)
  ·
    refine ⟨1903138155339437436225061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2537517540452583248300081 1903138155339437436225061)
    ·
      refine ⟨356838404126144519292199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1903138155339437436225061 356838404126144519292199)
      ·
        refine ⟨535257606189216778938299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356838404126144519292199 535257606189216778938299)
        ·
          refine ⟨802886409283825168407449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535257606189216778938299 802886409283825168407449)
          ·
            refine ⟨602164806962868876305587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802886409283825168407449 602164806962868876305587)
            ·
              refine ⟨903247210444303314458381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602164806962868876305587 903247210444303314458381)
              ·
                refine ⟨338717703916613742921893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 903247210444303314458381 338717703916613742921893)
                ·
                  refine ⟨63509569484365076797855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338717703916613742921893 63509569484365076797855)
                  ·
                    rfl

theorem cell21_278290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_278290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278290 prefixEnd_278290 := by exact prefixLift 278290
  have htrace : WordTrace (prefixWord ++ tailWord_278290) baseStart_278290 baseEnd_278290 := by
    simpa [prefixWord, tailWord_278290, baseEnd_278290] using wordTrace_append hprefix tailTrace_278290
  have hstable : (prefixWord ++ tailWord_278290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278290).length < 2 ^ (prefixWord ++ tailWord_278290).sum := by decide
  have hdescent : baseEnd_278290 < baseStart_278290 := by decide
  rcases family_descends (prefixWord ++ tailWord_278290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278332 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_278332 : Nat := 118140960795 + 278332 * 2 ^ 59
def prefixEnd_278332 : Nat := 4983230072969 + 3 ^ 40 * 278332 * 2
def baseEnd_278332 : Nat := 63519154456582337097769

theorem tailTrace_278332 : CollatzResearch.WordTrace tailWord_278332 prefixEnd_278332 63519154456582337097769 := by
  unfold tailWord_278332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075801013829087083114625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6767734685105449444152833 5075801013829087083114625)
  ·
    refine ⟨3806850760371815312335969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5075801013829087083114625 3806850760371815312335969)
    ·
      refine ⟨2855138070278861484251977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3806850760371815312335969 2855138070278861484251977)
      ·
        refine ⟨2141353552709146113188983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855138070278861484251977 2141353552709146113188983)
        ·
          refine ⟨3212030329063719169783475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141353552709146113188983 3212030329063719169783475)
          ·
            refine ⟨4818045493595578754675213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212030329063719169783475 4818045493595578754675213)
            ·
              refine ⟨1806767060098342033003205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4818045493595578754675213 1806767060098342033003205)
              ·
                refine ⟨338768823768439131188101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1806767060098342033003205 338768823768439131188101)
                ·
                  refine ⟨63519154456582337097769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338768823768439131188101 63519154456582337097769)
                  ·
                    rfl

theorem cell21_278332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_278332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278332 prefixEnd_278332 := by exact prefixLift 278332
  have htrace : WordTrace (prefixWord ++ tailWord_278332) baseStart_278332 baseEnd_278332 := by
    simpa [prefixWord, tailWord_278332, baseEnd_278332] using wordTrace_append hprefix tailTrace_278332
  have hstable : (prefixWord ++ tailWord_278332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278332).length < 2 ^ (prefixWord ++ tailWord_278332).sum := by decide
  have hdescent : baseEnd_278332 < baseStart_278332 := by decide
  rcases family_descends (prefixWord ++ tailWord_278332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278335 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 3]
def baseStart_278335 : Nat := 118140960795 + 278335 * 2 ^ 59
def prefixEnd_278335 : Nat := 4983230072969 + 3 ^ 40 * 278335 * 2
def baseEnd_278335 : Nat := 63519839097454998547763

theorem tailTrace_278335 : CollatzResearch.WordTrace tailWord_278335 prefixEnd_278335 63519839097454998547763 := by
  unfold tailWord_278335
  simp only [CollatzResearch.WordTrace]
  refine ⟨10151711446647305678588459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6767807631098203785725639 10151711446647305678588459)
  ·
    refine ⟨15227567169970958517882689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10151711446647305678588459 15227567169970958517882689)
    ·
      refine ⟨11420675377478218888412017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15227567169970958517882689 11420675377478218888412017)
      ·
        refine ⟨8565506533108664166309013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11420675377478218888412017 8565506533108664166309013)
        ·
          refine ⟨401508118739468632795735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8565506533108664166309013 401508118739468632795735)
          ·
            refine ⟨602262178109202949193603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401508118739468632795735 602262178109202949193603)
            ·
              refine ⟨903393267163804423790405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602262178109202949193603 903393267163804423790405)
              ·
                refine ⟨169386237593213329460701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 903393267163804423790405 169386237593213329460701)
                ·
                  refine ⟨63519839097454998547763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169386237593213329460701 63519839097454998547763)
                  ·
                    rfl

theorem cell21_278335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3].length) (baseStart_278335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278335 prefixEnd_278335 := by exact prefixLift 278335
  have htrace : WordTrace (prefixWord ++ tailWord_278335) baseStart_278335 baseEnd_278335 := by
    simpa [prefixWord, tailWord_278335, baseEnd_278335] using wordTrace_append hprefix tailTrace_278335
  have hstable : (prefixWord ++ tailWord_278335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278335).length < 2 ^ (prefixWord ++ tailWord_278335).sum := by decide
  have hdescent : baseEnd_278335 < baseStart_278335 := by decide
  rcases family_descends (prefixWord ++ tailWord_278335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278394 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_278394 : Nat := 118140960795 + 278394 * 2 ^ 59
def prefixEnd_278394 : Nat := 4983230072969 + 3 ^ 40 * 278394 * 2
def baseEnd_278394 : Nat := 63533303701284007064309

theorem tailTrace_278394 : CollatzResearch.WordTrace tailWord_278394 prefixEnd_278394 63533303701284007064309 := by
  unfold tailWord_278394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538465838358389688746559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6769242235622372503324157 2538465838358389688746559)
  ·
    refine ⟨3807698757537584533119839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2538465838358389688746559 3807698757537584533119839)
    ·
      refine ⟨5711548136306376799679759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807698757537584533119839 5711548136306376799679759)
      ·
        refine ⟨8567322204459565199519639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711548136306376799679759 8567322204459565199519639)
        ·
          refine ⟨12850983306689347799279459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8567322204459565199519639 12850983306689347799279459)
          ·
            refine ⟨19276474960034021698919189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12850983306689347799279459 19276474960034021698919189)
            ·
              refine ⟨903584763751594767136837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19276474960034021698919189 903584763751594767136837)
              ·
                refine ⟨169422143203424018838157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 903584763751594767136837 169422143203424018838157)
                ·
                  refine ⟨63533303701284007064309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169422143203424018838157 63533303701284007064309)
                  ·
                    rfl

theorem cell21_278394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_278394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278394 prefixEnd_278394 := by exact prefixLift 278394
  have htrace : WordTrace (prefixWord ++ tailWord_278394) baseStart_278394 baseEnd_278394 := by
    simpa [prefixWord, tailWord_278394, baseEnd_278394] using wordTrace_append hprefix tailTrace_278394
  have hstable : (prefixWord ++ tailWord_278394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278394).length < 2 ^ (prefixWord ++ tailWord_278394).sum := by decide
  have hdescent : baseEnd_278394 < baseStart_278394 := by decide
  rcases family_descends (prefixWord ++ tailWord_278394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278414 : List Nat := [4, 1, 1, 5, 2, 1, 2, 5]
def baseStart_278414 : Nat := 118140960795 + 278414 * 2 ^ 59
def prefixEnd_278414 : Nat := 4983230072969 + 3 ^ 40 * 278414 * 2
def baseEnd_278414 : Nat := 21179289324589472243645

theorem tailTrace_278414 : CollatzResearch.WordTrace tailWord_278414 prefixEnd_278414 21179289324589472243645 := by
  unfold tailWord_278414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269324101670137771339287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6769728542240734780476197 1269324101670137771339287)
  ·
    refine ⟨1903986152505206657008931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1269324101670137771339287 1903986152505206657008931)
    ·
      refine ⟨2855979228757809985513397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903986152505206657008931 2855979228757809985513397)
      ·
        refine ⟨267748052696044686141881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2855979228757809985513397 267748052696044686141881)
        ·
          refine ⟨200811039522033514606411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267748052696044686141881 200811039522033514606411)
          ·
            refine ⟨301216559283050271909617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200811039522033514606411 301216559283050271909617)
            ·
              refine ⟨225912419462287703932213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301216559283050271909617 225912419462287703932213)
              ·
                refine ⟨21179289324589472243645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225912419462287703932213 21179289324589472243645)
                ·
                  rfl

theorem cell21_278414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_278414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278414 prefixEnd_278414 := by exact prefixLift 278414
  have htrace : WordTrace (prefixWord ++ tailWord_278414) baseStart_278414 baseEnd_278414 := by
    simpa [prefixWord, tailWord_278414, baseEnd_278414] using wordTrace_append hprefix tailTrace_278414
  have hstable : (prefixWord ++ tailWord_278414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278414).length < 2 ^ (prefixWord ++ tailWord_278414).sum := by decide
  have hdescent : baseEnd_278414 < baseStart_278414 := by decide
  rcases family_descends (prefixWord ++ tailWord_278414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278428 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_278428 : Nat := 118140960795 + 278428 * 2 ^ 59
def prefixEnd_278428 : Nat := 4983230072969 + 3 ^ 40 * 278428 * 2
def baseEnd_278428 : Nat := 63541062964507503497573

theorem tailTrace_278428 : CollatzResearch.WordTrace tailWord_278428 prefixEnd_278428 63541062964507503497573 := by
  unfold tailWord_278428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077551717655191280861969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6770068956873588374482625 5077551717655191280861969)
  ·
    refine ⟨3808163788241393460646477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5077551717655191280861969 3808163788241393460646477)
    ·
      refine ⟨1428061420590522547742429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3808163788241393460646477 1428061420590522547742429)
      ·
        refine ⟨535523032721445955403411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1428061420590522547742429 535523032721445955403411)
        ·
          refine ⟨803284549082168933105117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535523032721445955403411 803284549082168933105117)
          ·
            refine ⟨301231705905813349914419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 803284549082168933105117 301231705905813349914419)
            ·
              refine ⟨451847558858720024871629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301231705905813349914419 451847558858720024871629)
              ·
                refine ⟨169442834572020009326861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451847558858720024871629 169442834572020009326861)
                ·
                  refine ⟨63541062964507503497573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169442834572020009326861 63541062964507503497573)
                  ·
                    rfl

theorem cell21_278428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_278428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278428 prefixEnd_278428 := by exact prefixLift 278428
  have htrace : WordTrace (prefixWord ++ tailWord_278428) baseStart_278428 baseEnd_278428 := by
    simpa [prefixWord, tailWord_278428, baseEnd_278428] using wordTrace_append hprefix tailTrace_278428
  have hstable : (prefixWord ++ tailWord_278428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278428).length < 2 ^ (prefixWord ++ tailWord_278428).sum := by decide
  have hdescent : baseEnd_278428 < baseStart_278428 := by decide
  rcases family_descends (prefixWord ++ tailWord_278428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278439 : List Nat := [1, 1, 6, 1, 2, 3, 7]
def baseStart_278439 : Nat := 118140960795 + 278439 * 2 ^ 59
def prefixEnd_278439 : Nat := 4983230072969 + 3 ^ 40 * 278439 * 2
def baseEnd_278439 : Nat := 7060397034930436534913

theorem tailTrace_278439 : CollatzResearch.WordTrace tailWord_278439 prefixEnd_278439 7060397034930436534913 := by
  unfold tailWord_278439
  simp only [CollatzResearch.WordTrace]
  refine ⟨10155504638270531440374371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6770336425513687626916247 10155504638270531440374371)
  ·
    refine ⟨15233256957405797160561557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10155504638270531440374371 15233256957405797160561557)
    ·
      refine ⟨714058919878396741901323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15233256957405797160561557 714058919878396741901323)
      ·
        refine ⟨1071088379817595112851985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714058919878396741901323 1071088379817595112851985)
        ·
          refine ⟨803316284863196334638989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071088379817595112851985 803316284863196334638989)
          ·
            refine ⟨301243606823698625489621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 803316284863196334638989 301243606823698625489621)
            ·
              refine ⟨7060397034930436534913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 301243606823698625489621 7060397034930436534913)
              ·
                rfl

theorem cell21_278439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 7].length) (baseStart_278439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278439 prefixEnd_278439 := by exact prefixLift 278439
  have htrace : WordTrace (prefixWord ++ tailWord_278439) baseStart_278439 baseEnd_278439 := by
    simpa [prefixWord, tailWord_278439, baseEnd_278439] using wordTrace_append hprefix tailTrace_278439
  have hstable : (prefixWord ++ tailWord_278439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278439).length < 2 ^ (prefixWord ++ tailWord_278439).sum := by decide
  have hdescent : baseEnd_278439 < baseStart_278439 := by decide
  rcases family_descends (prefixWord ++ tailWord_278439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278529 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_278529 : Nat := 118140960795 + 278529 * 2 ^ 59
def prefixEnd_278529 : Nat := 4983230072969 + 3 ^ 40 * 278529 * 2
def baseEnd_278529 : Nat := 63564112540553772314033

theorem tailTrace_278529 : CollatzResearch.WordTrace tailWord_278529 prefixEnd_278529 63564112540553772314033 := by
  unfold tailWord_278529
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158787207944476811150641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6772524805296317874100427 10158787207944476811150641)
  ·
    refine ⟨7619090405958357608362981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10158787207944476811150641 7619090405958357608362981)
    ·
      refine ⟨1428579451117192051568059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7619090405958357608362981 1428579451117192051568059)
      ·
        refine ⟨2142869176675788077352089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428579451117192051568059 2142869176675788077352089)
        ·
          refine ⟨1607151882506841058014067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2142869176675788077352089 1607151882506841058014067)
          ·
            refine ⟨2410727823760261587021101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607151882506841058014067 2410727823760261587021101)
            ·
              refine ⟨904022933910098095132913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2410727823760261587021101 904022933910098095132913)
              ·
                refine ⟨678017200432573571349685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904022933910098095132913 678017200432573571349685)
                ·
                  refine ⟨63564112540553772314033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678017200432573571349685 63564112540553772314033)
                  ·
                    rfl

theorem cell21_278529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_278529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278529 prefixEnd_278529 := by exact prefixLift 278529
  have htrace : WordTrace (prefixWord ++ tailWord_278529) baseStart_278529 baseEnd_278529 := by
    simpa [prefixWord, tailWord_278529, baseEnd_278529] using wordTrace_append hprefix tailTrace_278529
  have hstable : (prefixWord ++ tailWord_278529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278529).length < 2 ^ (prefixWord ++ tailWord_278529).sum := by decide
  have hdescent : baseEnd_278529 < baseStart_278529 := by decide
  rcases family_descends (prefixWord ++ tailWord_278529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278577 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 4]
def baseStart_278577 : Nat := 118140960795 + 278577 * 2 ^ 59
def prefixEnd_278577 : Nat := 4983230072969 + 3 ^ 40 * 278577 * 2
def baseEnd_278577 : Nat := 63575066794516355513935

theorem tailTrace_278577 : CollatzResearch.WordTrace tailWord_278577 prefixEnd_278577 63575066794516355513935 := by
  unfold tailWord_278577
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160537911770581008897985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6773691941180387339265323 10160537911770581008897985)
  ·
    refine ⟨7620403433827935756673489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10160537911770581008897985 7620403433827935756673489)
    ·
      refine ⟨5715302575370951817505117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7620403433827935756673489 5715302575370951817505117)
      ·
        refine ⟨2143238465764106931564419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5715302575370951817505117 2143238465764106931564419)
        ·
          refine ⟨3214857698646160397346629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143238465764106931564419 3214857698646160397346629)
          ·
            refine ⟨602785818496155074502493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3214857698646160397346629 602785818496155074502493)
            ·
              refine ⟨226044681936058152938435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 602785818496155074502493 226044681936058152938435)
              ·
                refine ⟨339067022904087229407653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226044681936058152938435 339067022904087229407653)
                ·
                  refine ⟨63575066794516355513935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339067022904087229407653 63575066794516355513935)
                  ·
                    rfl

theorem cell21_278577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_278577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278577 prefixEnd_278577 := by exact prefixLift 278577
  have htrace : WordTrace (prefixWord ++ tailWord_278577) baseStart_278577 baseEnd_278577 := by
    simpa [prefixWord, tailWord_278577, baseEnd_278577] using wordTrace_append hprefix tailTrace_278577
  have hstable : (prefixWord ++ tailWord_278577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278577).length < 2 ^ (prefixWord ++ tailWord_278577).sum := by decide
  have hdescent : baseEnd_278577 < baseStart_278577 := by decide
  rcases family_descends (prefixWord ++ tailWord_278577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278636 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_278636 : Nat := 118140960795 + 278636 * 2 ^ 59
def prefixEnd_278636 : Nat := 4983230072969 + 3 ^ 40 * 278636 * 2
def baseEnd_278636 : Nat := 63588531398345364030481

theorem tailTrace_278636 : CollatzResearch.WordTrace tailWord_278636 prefixEnd_278636 63588531398345364030481 := by
  unfold tailWord_278636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081344909278417042647881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6775126545704556056863841 5081344909278417042647881)
  ·
    refine ⟨3811008681958812781985911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5081344909278417042647881 3811008681958812781985911)
    ·
      refine ⟨5716513022938219172978867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811008681958812781985911 5716513022938219172978867)
      ·
        refine ⟨8574769534407328759468301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716513022938219172978867 8574769534407328759468301)
        ·
          refine ⟨3215538575402748284800613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8574769534407328759468301 3215538575402748284800613)
          ·
            refine ⟨602913482888015303400115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3215538575402748284800613 602913482888015303400115)
            ·
              refine ⟨904370224332022955100173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602913482888015303400115 904370224332022955100173)
              ·
                refine ⟨339138834124508608162565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 904370224332022955100173 339138834124508608162565)
                ·
                  refine ⟨63588531398345364030481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339138834124508608162565 63588531398345364030481)
                  ·
                    rfl

theorem cell21_278636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_278636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278636 prefixEnd_278636 := by exact prefixLift 278636
  have htrace : WordTrace (prefixWord ++ tailWord_278636) baseStart_278636 baseEnd_278636 := by
    simpa [prefixWord, tailWord_278636, baseEnd_278636] using wordTrace_append hprefix tailTrace_278636
  have hstable : (prefixWord ++ tailWord_278636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278636).length < 2 ^ (prefixWord ++ tailWord_278636).sum := by decide
  have hdescent : baseEnd_278636 < baseStart_278636 := by decide
  rcases family_descends (prefixWord ++ tailWord_278636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278757 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_278757 : Nat := 118140960795 + 278757 * 2 ^ 59
def prefixEnd_278757 : Nat := 4983230072969 + 3 ^ 40 * 278757 * 2
def baseEnd_278757 : Nat := 63616145246876042513567

theorem tailTrace_278757 : CollatzResearch.WordTrace tailWord_278757 prefixEnd_278757 63616145246876042513567 := by
  unfold tailWord_278757
  simp only [CollatzResearch.WordTrace]
  refine ⟨10167103051118471750450525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6778068700745647833633683 10167103051118471750450525)
  ·
    refine ⟨3812663644169426906418947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10167103051118471750450525 3812663644169426906418947)
    ·
      refine ⟨5718995466254140359628421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3812663644169426906418947 5718995466254140359628421)
      ·
        refine ⟨1072311649922651317430329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5718995466254140359628421 1072311649922651317430329)
        ·
          refine ⟨804233737441988488072747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072311649922651317430329 804233737441988488072747)
          ·
            refine ⟨1206350606162982732109121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804233737441988488072747 1206350606162982732109121)
            ·
              refine ⟨904762954622237049081841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206350606162982732109121 904762954622237049081841)
              ·
                refine ⟨678572215966677786811381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904762954622237049081841 678572215966677786811381)
                ·
                  refine ⟨63616145246876042513567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678572215966677786811381 63616145246876042513567)
                  ·
                    rfl

theorem cell21_278757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_278757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278757 prefixEnd_278757 := by exact prefixLift 278757
  have htrace : WordTrace (prefixWord ++ tailWord_278757) baseStart_278757 baseEnd_278757 := by
    simpa [prefixWord, tailWord_278757, baseEnd_278757] using wordTrace_append hprefix tailTrace_278757
  have hstable : (prefixWord ++ tailWord_278757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278757).length < 2 ^ (prefixWord ++ tailWord_278757).sum := by decide
  have hdescent : baseEnd_278757 < baseStart_278757 := by decide
  rcases family_descends (prefixWord ++ tailWord_278757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278791 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 5]
def baseStart_278791 : Nat := 118140960795 + 278791 * 2 ^ 59
def prefixEnd_278791 : Nat := 4983230072969 + 3 ^ 40 * 278791 * 2
def baseEnd_278791 : Nat := 63623904510099538946831

theorem tailTrace_278791 : CollatzResearch.WordTrace tailWord_278791 prefixEnd_278791 63623904510099538946831 := by
  unfold tailWord_278791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168343132995295557188227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6778895421996863704792151 10168343132995295557188227)
  ·
    refine ⟨15252514699492943335782341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10168343132995295557188227 15252514699492943335782341)
    ·
      refine ⟨2859846506154926875459189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15252514699492943335782341 2859846506154926875459189)
      ·
        refine ⟨268110609952024394574299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2859846506154926875459189 268110609952024394574299)
        ·
          refine ⟨402165914928036591861449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268110609952024394574299 402165914928036591861449)
          ·
            refine ⟨301624436196027443896087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402165914928036591861449 301624436196027443896087)
            ·
              refine ⟨452436654294041165844131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301624436196027443896087 452436654294041165844131)
              ·
                refine ⟨678654981441061748766197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452436654294041165844131 678654981441061748766197)
                ·
                  refine ⟨63623904510099538946831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678654981441061748766197 63623904510099538946831)
                  ·
                    rfl

theorem cell21_278791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_278791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278791 prefixEnd_278791 := by exact prefixLift 278791
  have htrace : WordTrace (prefixWord ++ tailWord_278791) baseStart_278791 baseEnd_278791 := by
    simpa [prefixWord, tailWord_278791, baseEnd_278791] using wordTrace_append hprefix tailTrace_278791
  have hstable : (prefixWord ++ tailWord_278791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278791).length < 2 ^ (prefixWord ++ tailWord_278791).sum := by decide
  have hdescent : baseEnd_278791 < baseStart_278791 := by decide
  rcases family_descends (prefixWord ++ tailWord_278791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278909 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_278909 : Nat := 118140960795 + 278909 * 2 ^ 59
def prefixEnd_278909 : Nat := 4983230072969 + 3 ^ 40 * 278909 * 2
def baseEnd_278909 : Nat := 63650833717757555979923

theorem tailTrace_278909 : CollatzResearch.WordTrace tailWord_278909 prefixEnd_278909 63650833717757555979923 := by
  unfold tailWord_278909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172646946567801709983781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6781764631045201139989187 10172646946567801709983781)
  ·
    refine ⟨1907371302481462820621959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10172646946567801709983781 1907371302481462820621959)
    ·
      refine ⟨2861056953722194230932939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907371302481462820621959 2861056953722194230932939)
      ·
        refine ⟨4291585430583291346399409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861056953722194230932939 4291585430583291346399409)
        ·
          refine ⟨3218689072937468509799557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291585430583291346399409 3218689072937468509799557)
          ·
            refine ⟨603504201175775345587417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3218689072937468509799557 603504201175775345587417)
            ·
              refine ⟨452628150881831509190563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603504201175775345587417 452628150881831509190563)
              ·
                refine ⟨678942226322747263785845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452628150881831509190563 678942226322747263785845)
                ·
                  refine ⟨63650833717757555979923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678942226322747263785845 63650833717757555979923)
                  ·
                    rfl

theorem cell21_278909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_278909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278909 prefixEnd_278909 := by exact prefixLift 278909
  have htrace : WordTrace (prefixWord ++ tailWord_278909) baseStart_278909 baseEnd_278909 := by
    simpa [prefixWord, tailWord_278909, baseEnd_278909] using wordTrace_append hprefix tailTrace_278909
  have hstable : (prefixWord ++ tailWord_278909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278909).length < 2 ^ (prefixWord ++ tailWord_278909).sum := by decide
  have hdescent : baseEnd_278909 < baseStart_278909 := by decide
  rcases family_descends (prefixWord ++ tailWord_278909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278937 : List Nat := [1, 2, 1, 2, 1, 4, 3, 7]
def baseStart_278937 : Nat := 118140960795 + 278937 * 2 ^ 59
def prefixEnd_278937 : Nat := 4983230072969 + 3 ^ 40 * 278937 * 2
def baseEnd_278937 : Nat := 21219074566411909837733

theorem tailTrace_278937 : CollatzResearch.WordTrace tailWord_278937 prefixEnd_278937 21219074566411909837733 := by
  unfold tailWord_278937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173668190466362492003065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6782445460310908328002043 10173668190466362492003065)
  ·
    refine ⟨7630251142849771869002299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10173668190466362492003065 7630251142849771869002299)
    ·
      refine ⟨11445376714274657803503449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630251142849771869002299 11445376714274657803503449)
      ·
        refine ⟨8584032535705993352627587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11445376714274657803503449 8584032535705993352627587)
        ·
          refine ⟨12876048803558990028941381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8584032535705993352627587 12876048803558990028941381)
          ·
            refine ⟨2414259150667310630426509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12876048803558990028941381 2414259150667310630426509)
            ·
              refine ⟨905347181500241486409941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2414259150667310630426509 905347181500241486409941)
              ·
                refine ⟨21219074566411909837733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 905347181500241486409941 21219074566411909837733)
                ·
                  rfl

theorem cell21_278937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_278937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_278937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_278937 prefixEnd_278937 := by exact prefixLift 278937
  have htrace : WordTrace (prefixWord ++ tailWord_278937) baseStart_278937 baseEnd_278937 := by
    simpa [prefixWord, tailWord_278937, baseEnd_278937] using wordTrace_append hprefix tailTrace_278937
  have hstable : (prefixWord ++ tailWord_278937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278937).length < 2 ^ (prefixWord ++ tailWord_278937).sum := by decide
  have hdescent : baseEnd_278937 < baseStart_278937 := by decide
  rcases family_descends (prefixWord ++ tailWord_278937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279013 : List Nat := [1, 3, 1, 5, 11]
def baseStart_279013 : Nat := 118140960795 + 279013 * 2 ^ 59
def prefixEnd_279013 : Nat := 4983230072969 + 3 ^ 40 * 279013 * 2
def baseEnd_279013 : Nat := 786105776971314645017

theorem tailTrace_279013 : CollatzResearch.WordTrace tailWord_279013 prefixEnd_279013 786105776971314645017 := by
  unfold tailWord_279013
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176440138191027471769693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6784293425460684981179795 10176440138191027471769693)
  ·
    refine ⟨3816165051821635301913635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10176440138191027471769693 3816165051821635301913635)
    ·
      refine ⟨5724247577732452952870453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816165051821635301913635 5724247577732452952870453)
      ·
        refine ⟨536648210412417464331605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5724247577732452952870453 536648210412417464331605)
        ·
          refine ⟨786105776971314645017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 536648210412417464331605 786105776971314645017)
          ·
            rfl

theorem cell21_279013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 11].length) (baseStart_279013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279013 prefixEnd_279013 := by exact prefixLift 279013
  have htrace : WordTrace (prefixWord ++ tailWord_279013) baseStart_279013 baseEnd_279013 := by
    simpa [prefixWord, tailWord_279013, baseEnd_279013] using wordTrace_append hprefix tailTrace_279013
  have hstable : (prefixWord ++ tailWord_279013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279013).length < 2 ^ (prefixWord ++ tailWord_279013).sum := by decide
  have hdescent : baseEnd_279013 < baseStart_279013 := by decide
  rcases family_descends (prefixWord ++ tailWord_279013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279016 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_279016 : Nat := 118140960795 + 279016 * 2 ^ 59
def prefixEnd_279016 : Nat := 4983230072969 + 3 ^ 40 * 279016 * 2
def baseEnd_279016 : Nat := 63675252575549147696371

theorem tailTrace_279016 : CollatzResearch.WordTrace tailWord_279016 prefixEnd_279016 63675252575549147696371 := by
  unfold tailWord_279016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088274778590079492064451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6784366371453439322752601 5088274778590079492064451)
  ·
    refine ⟨7632412167885119238096677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088274778590079492064451 7632412167885119238096677)
    ·
      refine ⟨1431077281478459857143127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7632412167885119238096677 1431077281478459857143127)
      ·
        refine ⟨2146615922217689785714691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431077281478459857143127 2146615922217689785714691)
        ·
          refine ⟨3219923883326534678572037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146615922217689785714691 3219923883326534678572037)
          ·
            refine ⟨603735728123725252232257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3219923883326534678572037 603735728123725252232257)
            ·
              refine ⟨452801796092793939174193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603735728123725252232257 452801796092793939174193)
              ·
                refine ⟨339601347069595454380645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452801796092793939174193 339601347069595454380645)
                ·
                  refine ⟨63675252575549147696371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339601347069595454380645 63675252575549147696371)
                  ·
                    rfl

theorem cell21_279016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_279016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279016 prefixEnd_279016 := by exact prefixLift 279016
  have htrace : WordTrace (prefixWord ++ tailWord_279016) baseStart_279016 baseEnd_279016 := by
    simpa [prefixWord, tailWord_279016, baseEnd_279016] using wordTrace_append hprefix tailTrace_279016
  have hstable : (prefixWord ++ tailWord_279016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279016).length < 2 ^ (prefixWord ++ tailWord_279016).sum := by decide
  have hdescent : baseEnd_279016 < baseStart_279016 := by decide
  rcases family_descends (prefixWord ++ tailWord_279016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279047 : List Nat := [1, 1, 4, 3, 3, 1, 3, 5]
def baseStart_279047 : Nat := 118140960795 + 279047 * 2 ^ 59
def prefixEnd_279047 : Nat := 4983230072969 + 3 ^ 40 * 279047 * 2
def baseEnd_279047 : Nat := 21227442399299994226547

theorem tailTrace_279047 : CollatzResearch.WordTrace tailWord_279047 prefixEnd_279047 21227442399299994226547 := by
  unfold tailWord_279047
  simp only [CollatzResearch.WordTrace]
  refine ⟨10177680220067851278507395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6785120146711900852338263 10177680220067851278507395)
  ·
    refine ⟨15266520330101776917761093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10177680220067851278507395 15266520330101776917761093)
    ·
      refine ⟨2862472561894083172080205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15266520330101776917761093 2862472561894083172080205)
      ·
        refine ⟨1073427210710281189530077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2862472561894083172080205 1073427210710281189530077)
        ·
          refine ⟨402535204016355446073779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1073427210710281189530077 402535204016355446073779)
          ·
            refine ⟨603802806024533169110669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402535204016355446073779 603802806024533169110669)
            ·
              refine ⟨226426052259199938416501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 603802806024533169110669 226426052259199938416501)
              ·
                refine ⟨21227442399299994226547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226426052259199938416501 21227442399299994226547)
                ·
                  rfl

theorem cell21_279047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 5].length) (baseStart_279047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279047 prefixEnd_279047 := by exact prefixLift 279047
  have htrace : WordTrace (prefixWord ++ tailWord_279047) baseStart_279047 baseEnd_279047 := by
    simpa [prefixWord, tailWord_279047, baseEnd_279047] using wordTrace_append hprefix tailTrace_279047
  have hstable : (prefixWord ++ tailWord_279047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279047).length < 2 ^ (prefixWord ++ tailWord_279047).sum := by decide
  have hdescent : baseEnd_279047 < baseStart_279047 := by decide
  rcases family_descends (prefixWord ++ tailWord_279047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279075 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_279075 : Nat := 118140960795 + 279075 * 2 ^ 59
def prefixEnd_279075 : Nat := 4983230072969 + 3 ^ 40 * 279075 * 2
def baseEnd_279075 : Nat := 63688717179378156212917

theorem tailTrace_279075 : CollatzResearch.WordTrace tailWord_279075 prefixEnd_279075 63688717179378156212917 := by
  unfold tailWord_279075
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178701463966412060526679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6785800975977608040351119 10178701463966412060526679)
  ·
    refine ⟨15268052195949618090790019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10178701463966412060526679 15268052195949618090790019)
    ·
      refine ⟨22902078293924427136185029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15268052195949618090790019 22902078293924427136185029)
      ·
        refine ⟨4294139680110830088034693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22902078293924427136185029 4294139680110830088034693)
        ·
          refine ⟨805151190020780641506505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4294139680110830088034693 805151190020780641506505)
          ·
            refine ⟨603863392515585481129879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805151190020780641506505 603863392515585481129879)
            ·
              refine ⟨905795088773378221694819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603863392515585481129879 905795088773378221694819)
              ·
                refine ⟨1358692633160067332542229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905795088773378221694819 1358692633160067332542229)
                ·
                  refine ⟨63688717179378156212917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1358692633160067332542229 63688717179378156212917)
                  ·
                    rfl

theorem cell21_279075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_279075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279075 prefixEnd_279075 := by exact prefixLift 279075
  have htrace : WordTrace (prefixWord ++ tailWord_279075) baseStart_279075 baseEnd_279075 := by
    simpa [prefixWord, tailWord_279075, baseEnd_279075] using wordTrace_append hprefix tailTrace_279075
  have hstable : (prefixWord ++ tailWord_279075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279075).length < 2 ^ (prefixWord ++ tailWord_279075).sum := by decide
  have hdescent : baseEnd_279075 < baseStart_279075 := by decide
  rcases family_descends (prefixWord ++ tailWord_279075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279137 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 5]
def baseStart_279137 : Nat := 118140960795 + 279137 * 2 ^ 59
def prefixEnd_279137 : Nat := 4983230072969 + 3 ^ 40 * 279137 * 2
def baseEnd_279137 : Nat := 63702866424079826179457

theorem tailTrace_279137 : CollatzResearch.WordTrace tailWord_279137 prefixEnd_279137 63702866424079826179457 := by
  unfold tailWord_279137
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180962789741796649283665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6787308526494531099522443 10180962789741796649283665)
  ·
    refine ⟨7635722092306347486962749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10180962789741796649283665 7635722092306347486962749)
    ·
      refine ⟨2863395784614880307611031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7635722092306347486962749 2863395784614880307611031)
      ·
        refine ⟨4295093676922320461416547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863395784614880307611031 4295093676922320461416547)
        ·
          refine ⟨6442640515383480692124821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295093676922320461416547 6442640515383480692124821)
          ·
            refine ⟨301998774158600657443351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6442640515383480692124821 301998774158600657443351)
            ·
              refine ⟨452998161237900986165027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301998774158600657443351 452998161237900986165027)
              ·
                refine ⟨679497241856851479247541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452998161237900986165027 679497241856851479247541)
                ·
                  refine ⟨63702866424079826179457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 679497241856851479247541 63702866424079826179457)
                  ·
                    rfl

theorem cell21_279137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_279137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279137 prefixEnd_279137 := by exact prefixLift 279137
  have htrace : WordTrace (prefixWord ++ tailWord_279137) baseStart_279137 baseEnd_279137 := by
    simpa [prefixWord, tailWord_279137, baseEnd_279137] using wordTrace_append hprefix tailTrace_279137
  have hstable : (prefixWord ++ tailWord_279137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279137).length < 2 ^ (prefixWord ++ tailWord_279137).sum := by decide
  have hdescent : baseEnd_279137 < baseStart_279137 := by decide
  rcases family_descends (prefixWord ++ tailWord_279137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279179 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_279179 : Nat := 118140960795 + 279179 * 2 ^ 59
def prefixEnd_279179 : Nat := 4983230072969 + 3 ^ 40 * 279179 * 2
def baseEnd_279179 : Nat := 63712451396297086479371

theorem tailTrace_279179 : CollatzResearch.WordTrace tailWord_279179 prefixEnd_279179 63712451396297086479371 := by
  unfold tailWord_279179
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182494655589637822312591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6788329770393091881541727 10182494655589637822312591)
  ·
    refine ⟨15273741983384456733468887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10182494655589637822312591 15273741983384456733468887)
    ·
      refine ⟨22910612975076685100203331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15273741983384456733468887 22910612975076685100203331)
      ·
        refine ⟨34365919462615027650304997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22910612975076685100203331 34365919462615027650304997)
        ·
          refine ⟨6443609899240317684432187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34365919462615027650304997 6443609899240317684432187)
          ·
            refine ⟨9665414848860476526648281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443609899240317684432187 9665414848860476526648281)
            ·
              refine ⟨7249061136645357394986211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9665414848860476526648281 7249061136645357394986211)
              ·
                refine ⟨10873591704968036092479317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7249061136645357394986211 10873591704968036092479317)
                ·
                  refine ⟨63712451396297086479371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10873591704968036092479317 63712451396297086479371)
                  ·
                    rfl

theorem cell21_279179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_279179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279179 prefixEnd_279179 := by exact prefixLift 279179
  have htrace : WordTrace (prefixWord ++ tailWord_279179) baseStart_279179 baseEnd_279179 := by
    simpa [prefixWord, tailWord_279179, baseEnd_279179] using wordTrace_append hprefix tailTrace_279179
  have hstable : (prefixWord ++ tailWord_279179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279179).length < 2 ^ (prefixWord ++ tailWord_279179).sum := by decide
  have hdescent : baseEnd_279179 < baseStart_279179 := by decide
  rcases family_descends (prefixWord ++ tailWord_279179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279188 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_279188 : Nat := 118140960795 + 279188 * 2 ^ 59
def prefixEnd_279188 : Nat := 4983230072969 + 3 ^ 40 * 279188 * 2
def baseEnd_279188 : Nat := 63714505318915070829353

theorem tailTrace_279188 : CollatzResearch.WordTrace tailWord_279188 prefixEnd_279188 63714505318915070829353 := by
  unfold tailWord_279188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091411456278516179695109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6788548608371354906260145 5091411456278516179695109)
  ·
    refine ⟨954639648052221783692833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5091411456278516179695109 954639648052221783692833)
    ·
      refine ⟨715979736039166337769625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 954639648052221783692833 715979736039166337769625)
      ·
        refine ⟨536984802029374753327219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 715979736039166337769625 536984802029374753327219)
        ·
          refine ⟨805477203044062129990829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536984802029374753327219 805477203044062129990829)
          ·
            refine ⟨302053951141523298746561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 805477203044062129990829 302053951141523298746561)
            ·
              refine ⟨226540463356142474059921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302053951141523298746561 226540463356142474059921)
              ·
                refine ⟨169905347517106855544941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226540463356142474059921 169905347517106855544941)
                ·
                  refine ⟨63714505318915070829353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169905347517106855544941 63714505318915070829353)
                  ·
                    rfl

theorem cell21_279188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_279188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279188 prefixEnd_279188 := by exact prefixLift 279188
  have htrace : WordTrace (prefixWord ++ tailWord_279188) baseStart_279188 baseEnd_279188 := by
    simpa [prefixWord, tailWord_279188, baseEnd_279188] using wordTrace_append hprefix tailTrace_279188
  have hstable : (prefixWord ++ tailWord_279188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279188).length < 2 ^ (prefixWord ++ tailWord_279188).sum := by decide
  have hdescent : baseEnd_279188 < baseStart_279188 := by decide
  rcases family_descends (prefixWord ++ tailWord_279188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279213 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_279213 : Nat := 118140960795 + 279213 * 2 ^ 59
def prefixEnd_279213 : Nat := 4983230072969 + 3 ^ 40 * 279213 * 2
def baseEnd_279213 : Nat := 63720210659520582912635

theorem tailTrace_279213 : CollatzResearch.WordTrace tailWord_279213 prefixEnd_279213 63720210659520582912635 := by
  unfold tailWord_279213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183734737466461629050293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6789156491644307752700195 10183734737466461629050293)
  ·
    refine ⟨954725131637480777723465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10183734737466461629050293 954725131637480777723465)
    ·
      refine ⟨716043848728110583292599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 954725131637480777723465 716043848728110583292599)
      ·
        refine ⟨1074065773092165874938899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716043848728110583292599 1074065773092165874938899)
        ·
          refine ⟨1611098659638248812408349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074065773092165874938899 1611098659638248812408349)
          ·
            refine ⟨604161997364343304653131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1611098659638248812408349 604161997364343304653131)
            ·
              refine ⟨906242996046514956979697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604161997364343304653131 906242996046514956979697)
              ·
                refine ⟨679682247034886217734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906242996046514956979697 679682247034886217734773)
                ·
                  refine ⟨63720210659520582912635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 679682247034886217734773 63720210659520582912635)
                  ·
                    rfl

theorem cell21_279213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_279213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279213 prefixEnd_279213 := by exact prefixLift 279213
  have htrace : WordTrace (prefixWord ++ tailWord_279213) baseStart_279213 baseEnd_279213 := by
    simpa [prefixWord, tailWord_279213, baseEnd_279213] using wordTrace_append hprefix tailTrace_279213
  have hstable : (prefixWord ++ tailWord_279213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279213).length < 2 ^ (prefixWord ++ tailWord_279213).sum := by decide
  have hdescent : baseEnd_279213 < baseStart_279213 := by decide
  rcases family_descends (prefixWord ++ tailWord_279213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279230 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_279230 : Nat := 118140960795 + 279230 * 2 ^ 59
def prefixEnd_279230 : Nat := 4983230072969 + 3 ^ 40 * 279230 * 2
def baseEnd_279230 : Nat := 63724090291132331129267

theorem tailTrace_279230 : CollatzResearch.WordTrace tailWord_279230 prefixEnd_279230 63724090291132331129267 := by
  unfold tailWord_279230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273044347300609191552393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6789569852269915688279429 1273044347300609191552393)
  ·
    refine ⟨954783260475456893664295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1273044347300609191552393 954783260475456893664295)
    ·
      refine ⟨1432174890713185340496443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954783260475456893664295 1432174890713185340496443)
      ·
        refine ⟨2148262336069778010744665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432174890713185340496443 2148262336069778010744665)
        ·
          refine ⟨1611196752052333508058499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2148262336069778010744665 1611196752052333508058499)
          ·
            refine ⟨2416795128078500262087749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611196752052333508058499 2416795128078500262087749)
            ·
              refine ⟨453149086514718799141453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2416795128078500262087749 453149086514718799141453)
              ·
                refine ⟨169930907443019549678045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453149086514718799141453 169930907443019549678045)
                ·
                  refine ⟨63724090291132331129267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169930907443019549678045 63724090291132331129267)
                  ·
                    rfl

theorem cell21_279230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_279230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279230 prefixEnd_279230 := by exact prefixLift 279230
  have htrace : WordTrace (prefixWord ++ tailWord_279230) baseStart_279230 baseEnd_279230 := by
    simpa [prefixWord, tailWord_279230, baseEnd_279230] using wordTrace_append hprefix tailTrace_279230
  have hstable : (prefixWord ++ tailWord_279230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279230).length < 2 ^ (prefixWord ++ tailWord_279230).sum := by decide
  have hdescent : baseEnd_279230 < baseStart_279230 := by decide
  rcases family_descends (prefixWord ++ tailWord_279230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279244 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_279244 : Nat := 118140960795 + 279244 * 2 ^ 59
def prefixEnd_279244 : Nat := 4983230072969 + 3 ^ 40 * 279244 * 2
def baseEnd_279244 : Nat := 63727285281871417895905

theorem tailTrace_279244 : CollatzResearch.WordTrace tailWord_279244 prefixEnd_279244 63727285281871417895905 := by
  unfold tailWord_279244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5092432700177076961714393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6789910266902769282285857 5092432700177076961714393)
  ·
    refine ⟨3819324525132807721285795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5092432700177076961714393 3819324525132807721285795)
    ·
      refine ⟨5728986787699211581928693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819324525132807721285795 5728986787699211581928693)
      ·
        refine ⟨537092511346801085805815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5728986787699211581928693 537092511346801085805815)
        ·
          refine ⟨805638767020201628708723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537092511346801085805815 805638767020201628708723)
          ·
            refine ⟨1208458150530302443063085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805638767020201628708723 1208458150530302443063085)
            ·
              refine ⟨453171806448863416148657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1208458150530302443063085 453171806448863416148657)
              ·
                refine ⟨339878854836647562111493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453171806448863416148657 339878854836647562111493)
                ·
                  refine ⟨63727285281871417895905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339878854836647562111493 63727285281871417895905)
                  ·
                    rfl

theorem cell21_279244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_279244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279244 prefixEnd_279244 := by exact prefixLift 279244
  have htrace : WordTrace (prefixWord ++ tailWord_279244) baseStart_279244 baseEnd_279244 := by
    simpa [prefixWord, tailWord_279244, baseEnd_279244] using wordTrace_append hprefix tailTrace_279244
  have hstable : (prefixWord ++ tailWord_279244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279244).length < 2 ^ (prefixWord ++ tailWord_279244).sum := by decide
  have hdescent : baseEnd_279244 < baseStart_279244 := by decide
  rcases family_descends (prefixWord ++ tailWord_279244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279303 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_279303 : Nat := 118140960795 + 279303 * 2 ^ 59
def prefixEnd_279303 : Nat := 4983230072969 + 3 ^ 40 * 279303 * 2
def baseEnd_279303 : Nat := 63740749885700426412451

theorem tailTrace_279303 : CollatzResearch.WordTrace tailWord_279303 prefixEnd_279303 63740749885700426412451 := by
  unfold tailWord_279303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187017307140406999826563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6791344871426937999884375 10187017307140406999826563)
  ·
    refine ⟨15280525960710610499739845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10187017307140406999826563 15280525960710610499739845)
    ·
      refine ⟨2865098617633239468701221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15280525960710610499739845 2865098617633239468701221)
      ·
        refine ⟨537205990806232400381479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2865098617633239468701221 537205990806232400381479)
        ·
          refine ⟨805808986209348600572219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537205990806232400381479 805808986209348600572219)
          ·
            refine ⟨1208713479314022900858329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805808986209348600572219 1208713479314022900858329)
            ·
              refine ⟨906535109485517175643747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208713479314022900858329 906535109485517175643747)
              ·
                refine ⟨1359802664228275763465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906535109485517175643747 1359802664228275763465621)
                ·
                  refine ⟨63740749885700426412451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1359802664228275763465621 63740749885700426412451)
                  ·
                    rfl

theorem cell21_279303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_279303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279303 prefixEnd_279303 := by exact prefixLift 279303
  have htrace : WordTrace (prefixWord ++ tailWord_279303) baseStart_279303 baseEnd_279303 := by
    simpa [prefixWord, tailWord_279303, baseEnd_279303] using wordTrace_append hprefix tailTrace_279303
  have hstable : (prefixWord ++ tailWord_279303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279303).length < 2 ^ (prefixWord ++ tailWord_279303).sum := by decide
  have hdescent : baseEnd_279303 < baseStart_279303 := by decide
  rcases family_descends (prefixWord ++ tailWord_279303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279306 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_279306 : Nat := 118140960795 + 279306 * 2 ^ 59
def prefixEnd_279306 : Nat := 4983230072969 + 3 ^ 40 * 279306 * 2
def baseEnd_279306 : Nat := 63741434526573087862445

theorem tailTrace_279306 : CollatzResearch.WordTrace tailWord_279306 prefixEnd_279306 63741434526573087862445 := by
  unfold tailWord_279306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546781681532384628046443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6791417817419692341457181 2546781681532384628046443)
  ·
    refine ⟨3820172522298576942069665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546781681532384628046443 3820172522298576942069665)
    ·
      refine ⟨2865129391723932706552249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3820172522298576942069665 2865129391723932706552249)
      ·
        refine ⟨2148847043792949529914187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2865129391723932706552249 2148847043792949529914187)
        ·
          refine ⟨3223270565689424294871281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148847043792949529914187 3223270565689424294871281)
          ·
            refine ⟨2417452924267068221153461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223270565689424294871281 2417452924267068221153461)
            ·
              refine ⟨226636211650037645733137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2417452924267068221153461 226636211650037645733137)
              ·
                refine ⟨169977158737528234299853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226636211650037645733137 169977158737528234299853)
                ·
                  refine ⟨63741434526573087862445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169977158737528234299853 63741434526573087862445)
                  ·
                    rfl

theorem cell21_279306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_279306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279306 prefixEnd_279306 := by exact prefixLift 279306
  have htrace : WordTrace (prefixWord ++ tailWord_279306) baseStart_279306 baseEnd_279306 := by
    simpa [prefixWord, tailWord_279306, baseEnd_279306] using wordTrace_append hprefix tailTrace_279306
  have hstable : (prefixWord ++ tailWord_279306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279306).length < 2 ^ (prefixWord ++ tailWord_279306).sum := by decide
  have hdescent : baseEnd_279306 < baseStart_279306 := by decide
  rcases family_descends (prefixWord ++ tailWord_279306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279317 : List Nat := [1, 3, 2, 1, 2, 2, 4, 6]
def baseStart_279317 : Nat := 118140960795 + 279317 * 2 ^ 59
def prefixEnd_279317 : Nat := 4983230072969 + 3 ^ 40 * 279317 * 2
def baseEnd_279317 : Nat := 21247981625479837726363

theorem tailTrace_279317 : CollatzResearch.WordTrace tailWord_279317 prefixEnd_279317 21247981625479837726363 := by
  unfold tailWord_279317
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187527929089687390836205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6791685286059791593890803 10187527929089687390836205)
  ·
    refine ⟨3820322973408632771563577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10187527929089687390836205 3820322973408632771563577)
    ·
      refine ⟨2865242230056474578672683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3820322973408632771563577 2865242230056474578672683)
      ·
        refine ⟨4297863345084711868009025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865242230056474578672683 4297863345084711868009025)
        ·
          refine ⟨3223397508813533901006769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4297863345084711868009025 3223397508813533901006769)
          ·
            refine ⟨2417548131610150425755077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223397508813533901006769 2417548131610150425755077)
            ·
              refine ⟨453290274676903204829077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2417548131610150425755077 453290274676903204829077)
              ·
                refine ⟨21247981625479837726363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 453290274676903204829077 21247981625479837726363)
                ·
                  rfl

theorem cell21_279317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_279317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279317 prefixEnd_279317 := by exact prefixLift 279317
  have htrace : WordTrace (prefixWord ++ tailWord_279317) baseStart_279317 baseEnd_279317 := by
    simpa [prefixWord, tailWord_279317, baseEnd_279317] using wordTrace_append hprefix tailTrace_279317
  have hstable : (prefixWord ++ tailWord_279317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279317).length < 2 ^ (prefixWord ++ tailWord_279317).sum := by decide
  have hdescent : baseEnd_279317 < baseStart_279317 := by decide
  rcases family_descends (prefixWord ++ tailWord_279317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279331 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_279331 : Nat := 118140960795 + 279331 * 2 ^ 59
def prefixEnd_279331 : Nat := 4983230072969 + 3 ^ 40 * 279331 * 2
def baseEnd_279331 : Nat := 63747139867178599945727

theorem tailTrace_279331 : CollatzResearch.WordTrace tailWord_279331 prefixEnd_279331 63747139867178599945727 := by
  unfold tailWord_279331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188038551038967781845847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6792025700692645187897231 10188038551038967781845847)
  ·
    refine ⟨15282057826558451672768771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10188038551038967781845847 15282057826558451672768771)
    ·
      refine ⟨22923086739837677509153157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15282057826558451672768771 22923086739837677509153157)
      ·
        refine ⟨4298078763719564532966217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22923086739837677509153157 4298078763719564532966217)
        ·
          refine ⟨3223559072789673399724663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4298078763719564532966217 3223559072789673399724663)
          ·
            refine ⟨4835338609184510099586995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223559072789673399724663 4835338609184510099586995)
            ·
              refine ⟨7253007913776765149380493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4835338609184510099586995 7253007913776765149380493)
              ·
                refine ⟨2719877967666286931017685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7253007913776765149380493 2719877967666286931017685)
                ·
                  refine ⟨63747139867178599945727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2719877967666286931017685 63747139867178599945727)
                  ·
                    rfl

theorem cell21_279331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_279331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279331 prefixEnd_279331 := by exact prefixLift 279331
  have htrace : WordTrace (prefixWord ++ tailWord_279331) baseStart_279331 baseEnd_279331 := by
    simpa [prefixWord, tailWord_279331, baseEnd_279331] using wordTrace_append hprefix tailTrace_279331
  have hstable : (prefixWord ++ tailWord_279331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279331).length < 2 ^ (prefixWord ++ tailWord_279331).sum := by decide
  have hdescent : baseEnd_279331 < baseStart_279331 := by decide
  rcases family_descends (prefixWord ++ tailWord_279331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279458 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_279458 : Nat := 118140960795 + 279458 * 2 ^ 59
def prefixEnd_279458 : Nat := 4983230072969 + 3 ^ 40 * 279458 * 2
def baseEnd_279458 : Nat := 63776122997454601328801

theorem tailTrace_279458 : CollatzResearch.WordTrace tailWord_279458 prefixEnd_279458 63776122997454601328801 := by
  unfold tailWord_279458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548167655394717117929757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6795113747719245647812685 2548167655394717117929757)
  ·
    refine ⟨955562870773018919223659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2548167655394717117929757 955562870773018919223659)
    ·
      refine ⟨1433344306159528378835489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955562870773018919223659 1433344306159528378835489)
      ·
        refine ⟨1075008229619646284126617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433344306159528378835489 1075008229619646284126617)
        ·
          refine ⟨806256172214734713094963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075008229619646284126617 806256172214734713094963)
          ·
            refine ⟨1209384258322102069642445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806256172214734713094963 1209384258322102069642445)
            ·
              refine ⟨453519096870788276115917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209384258322102069642445 453519096870788276115917)
              ·
                refine ⟨170069661326545603543469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453519096870788276115917 170069661326545603543469)
                ·
                  refine ⟨63776122997454601328801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170069661326545603543469 63776122997454601328801)
                  ·
                    rfl

theorem cell21_279458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_279458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279458 prefixEnd_279458 := by exact prefixLift 279458
  have htrace : WordTrace (prefixWord ++ tailWord_279458) baseStart_279458 baseEnd_279458 := by
    simpa [prefixWord, tailWord_279458, baseEnd_279458] using wordTrace_append hprefix tailTrace_279458
  have hstable : (prefixWord ++ tailWord_279458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279458).length < 2 ^ (prefixWord ++ tailWord_279458).sum := by decide
  have hdescent : baseEnd_279458 < baseStart_279458 := by decide
  rcases family_descends (prefixWord ++ tailWord_279458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279534 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_279534 : Nat := 118140960795 + 279534 * 2 ^ 59
def prefixEnd_279534 : Nat := 4983230072969 + 3 ^ 40 * 279534 * 2
def baseEnd_279534 : Nat := 63793467232895358061979

theorem tailTrace_279534 : CollatzResearch.WordTrace tailWord_279534 prefixEnd_279534 63793467232895358061979 := by
  unfold tailWord_279534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274430321162941681435707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6796961712869022300990437 1274430321162941681435707)
  ·
    refine ⟨1911645481744412522153561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1274430321162941681435707 1911645481744412522153561)
    ·
      refine ⟨1433734111308309391615171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911645481744412522153561 1433734111308309391615171)
      ·
        refine ⟨2150601166962464087422757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433734111308309391615171 2150601166962464087422757)
        ·
          refine ⟨403237718805462016391767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2150601166962464087422757 403237718805462016391767)
          ·
            refine ⟨604856578208193024587651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403237718805462016391767 604856578208193024587651)
            ·
              refine ⟨907284867312289536881477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604856578208193024587651 907284867312289536881477)
              ·
                refine ⟨170115912621054288165277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 907284867312289536881477 170115912621054288165277)
                ·
                  refine ⟨63793467232895358061979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170115912621054288165277 63793467232895358061979)
                  ·
                    rfl

theorem cell21_279534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_279534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279534 prefixEnd_279534 := by exact prefixLift 279534
  have htrace : WordTrace (prefixWord ++ tailWord_279534) baseStart_279534 baseEnd_279534 := by
    simpa [prefixWord, tailWord_279534, baseEnd_279534] using wordTrace_append hprefix tailTrace_279534
  have hstable : (prefixWord ++ tailWord_279534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279534).length < 2 ^ (prefixWord ++ tailWord_279534).sum := by decide
  have hdescent : baseEnd_279534 < baseStart_279534 := by decide
  rcases family_descends (prefixWord ++ tailWord_279534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279562 : List Nat := [3, 1, 2, 2, 3, 2, 3, 5]
def baseStart_279562 : Nat := 118140960795 + 279562 * 2 ^ 59
def prefixEnd_279562 : Nat := 4983230072969 + 3 ^ 40 * 279562 * 2
def baseEnd_279562 : Nat := 21266619071457843865085

theorem tailTrace_279562 : CollatzResearch.WordTrace tailWord_279562 prefixEnd_279562 21266619071457843865085 := by
  unfold tailWord_279562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549115953300523558376235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6797642542134729489003293 2549115953300523558376235)
  ·
    refine ⟨3823673929950785337564353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549115953300523558376235 3823673929950785337564353)
    ·
      refine ⟨2867755447463089003173265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3823673929950785337564353 2867755447463089003173265)
      ·
        refine ⟨2150816585597316752379949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2867755447463089003173265 2150816585597316752379949)
        ·
          refine ⟨806556219598993782142481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2150816585597316752379949 806556219598993782142481)
          ·
            refine ⟨604917164699245336606861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806556219598993782142481 604917164699245336606861)
            ·
              refine ⟨226843936762217001227573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 604917164699245336606861 226843936762217001227573)
              ·
                refine ⟨21266619071457843865085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226843936762217001227573 21266619071457843865085)
                ·
                  rfl

theorem cell21_279562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_279562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279562 prefixEnd_279562 := by exact prefixLift 279562
  have htrace : WordTrace (prefixWord ++ tailWord_279562) baseStart_279562 baseEnd_279562 := by
    simpa [prefixWord, tailWord_279562, baseEnd_279562] using wordTrace_append hprefix tailTrace_279562
  have hstable : (prefixWord ++ tailWord_279562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279562).length < 2 ^ (prefixWord ++ tailWord_279562).sum := by decide
  have hdescent : baseEnd_279562 < baseStart_279562 := by decide
  rcases family_descends (prefixWord ++ tailWord_279562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279621 : List Nat := [1, 3, 1, 1, 1, 3, 6, 5]
def baseStart_279621 : Nat := 118140960795 + 279621 * 2 ^ 59
def prefixEnd_279621 : Nat := 4983230072969 + 3 ^ 40 * 279621 * 2
def baseEnd_279621 : Nat := 21271107272734180037267

theorem tailTrace_279621 : CollatzResearch.WordTrace tailWord_279621 prefixEnd_279621 21271107272734180037267 := by
  unfold tailWord_279621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198615719988347309902717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799077146658898206601811 10198615719988347309902717)
  ·
    refine ⟨3824480894995630241213519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10198615719988347309902717 3824480894995630241213519)
    ·
      refine ⟨5736721342493445361820279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824480894995630241213519 5736721342493445361820279)
      ·
        refine ⟨8605082013740168042730419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736721342493445361820279 8605082013740168042730419)
        ·
          refine ⟨12907623020610252064095629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605082013740168042730419 12907623020610252064095629)
          ·
            refine ⟨4840358632728844524035861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12907623020610252064095629 4840358632728844524035861)
            ·
              refine ⟨226891810909164587064181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4840358632728844524035861 226891810909164587064181)
              ·
                refine ⟨21271107272734180037267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226891810909164587064181 21271107272734180037267)
                ·
                  rfl

theorem cell21_279621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 5].length) (baseStart_279621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279621 prefixEnd_279621 := by exact prefixLift 279621
  have htrace : WordTrace (prefixWord ++ tailWord_279621) baseStart_279621 baseEnd_279621 := by
    simpa [prefixWord, tailWord_279621, baseEnd_279621] using wordTrace_append hprefix tailTrace_279621
  have hstable : (prefixWord ++ tailWord_279621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279621).length < 2 ^ (prefixWord ++ tailWord_279621).sum := by decide
  have hdescent : baseEnd_279621 < baseStart_279621 := by decide
  rcases family_descends (prefixWord ++ tailWord_279621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279680 : List Nat := [2, 1, 1, 2, 1, 3, 4, 7]
def baseStart_279680 : Nat := 118140960795 + 279680 * 2 ^ 59
def prefixEnd_279680 : Nat := 4983230072969 + 3 ^ 40 * 279680 * 2
def baseEnd_279680 : Nat := 21275595474010516209449

theorem tailTrace_279680 : CollatzResearch.WordTrace tailWord_279680 prefixEnd_279680 21275595474010516209449 := by
  unfold tailWord_279680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100383813387300193150247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6800511751183066924200329 5100383813387300193150247)
  ·
    refine ⟨7650575720080950289725371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5100383813387300193150247 7650575720080950289725371)
    ·
      refine ⟨11475863580121425434588057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650575720080950289725371 11475863580121425434588057)
      ·
        refine ⟨8606897685091069075941043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11475863580121425434588057 8606897685091069075941043)
        ·
          refine ⟨12910346527636603613911565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8606897685091069075941043 12910346527636603613911565)
          ·
            refine ⟨4841379947863726355216837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12910346527636603613911565 4841379947863726355216837)
            ·
              refine ⟨907758740224448691603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4841379947863726355216837 907758740224448691603157)
              ·
                refine ⟨21275595474010516209449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 907758740224448691603157 21275595474010516209449)
                ·
                  rfl

theorem cell21_279680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_279680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279680 prefixEnd_279680 := by exact prefixLift 279680
  have htrace : WordTrace (prefixWord ++ tailWord_279680) baseStart_279680 baseEnd_279680 := by
    simpa [prefixWord, tailWord_279680, baseEnd_279680] using wordTrace_append hprefix tailTrace_279680
  have hstable : (prefixWord ++ tailWord_279680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279680).length < 2 ^ (prefixWord ++ tailWord_279680).sum := by decide
  have hdescent : baseEnd_279680 < baseStart_279680 := by decide
  rcases family_descends (prefixWord ++ tailWord_279680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279787 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_279787 : Nat := 118140960795 + 279787 * 2 ^ 59
def prefixEnd_279787 : Nat := 4983230072969 + 3 ^ 40 * 279787 * 2
def baseEnd_279787 : Nat := 63851205279823140344795

theorem tailTrace_279787 : CollatzResearch.WordTrace tailWord_279787 prefixEnd_279787 63851205279823140344795 := by
  unfold tailWord_279787
  simp only [CollatzResearch.WordTrace]
  refine ⟨10204670237386957660445615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6803113491591305106963743 10204670237386957660445615)
  ·
    refine ⟨15307005356080436490668423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10204670237386957660445615 15307005356080436490668423)
    ·
      refine ⟨22960508034120654736002635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15307005356080436490668423 22960508034120654736002635)
      ·
        refine ⟨34440762051180982104003953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22960508034120654736002635 34440762051180982104003953)
        ·
          refine ⟨25830571538385736578002965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34440762051180982104003953 25830571538385736578002965)
          ·
            refine ⟨1210808040861831402093889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25830571538385736578002965 1210808040861831402093889)
            ·
              refine ⟨908106030646373551570417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210808040861831402093889 908106030646373551570417)
              ·
                refine ⟨681079522984780163677813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908106030646373551570417 681079522984780163677813)
                ·
                  refine ⟨63851205279823140344795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681079522984780163677813 63851205279823140344795)
                  ·
                    rfl

theorem cell21_279787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_279787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279787 prefixEnd_279787 := by exact prefixLift 279787
  have htrace : WordTrace (prefixWord ++ tailWord_279787) baseStart_279787 baseEnd_279787 := by
    simpa [prefixWord, tailWord_279787, baseEnd_279787] using wordTrace_append hprefix tailTrace_279787
  have hstable : (prefixWord ++ tailWord_279787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279787).length < 2 ^ (prefixWord ++ tailWord_279787).sum := by decide
  have hdescent : baseEnd_279787 < baseStart_279787 := by decide
  rcases family_descends (prefixWord ++ tailWord_279787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279801 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_279801 : Nat := 118140960795 + 279801 * 2 ^ 59
def prefixEnd_279801 : Nat := 4983230072969 + 3 ^ 40 * 279801 * 2
def baseEnd_279801 : Nat := 63854400270562227111433

theorem tailTrace_279801 : CollatzResearch.WordTrace tailWord_279801 prefixEnd_279801 63854400270562227111433 := by
  unfold tailWord_279801
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205180859336238051455257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6803453906224158700970171 10205180859336238051455257)
  ·
    refine ⟨7653885644502178538591443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10205180859336238051455257 7653885644502178538591443)
    ·
      refine ⟨11480828466753267807887165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7653885644502178538591443 11480828466753267807887165)
      ·
        refine ⟨4305310675032475427957687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11480828466753267807887165 4305310675032475427957687)
        ·
          refine ⟨6457966012548713141936531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4305310675032475427957687 6457966012548713141936531)
          ·
            refine ⟨9686949018823069712904797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457966012548713141936531 9686949018823069712904797)
            ·
              refine ⟨3632605882058651142339299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9686949018823069712904797 3632605882058651142339299)
              ·
                refine ⟨5448908823087976713508949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632605882058651142339299 5448908823087976713508949)
                ·
                  refine ⟨63854400270562227111433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5448908823087976713508949 63854400270562227111433)
                  ·
                    rfl

theorem cell21_279801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_279801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279801 prefixEnd_279801 := by exact prefixLift 279801
  have htrace : WordTrace (prefixWord ++ tailWord_279801) baseStart_279801 baseEnd_279801 := by
    simpa [prefixWord, tailWord_279801, baseEnd_279801] using wordTrace_append hprefix tailTrace_279801
  have hstable : (prefixWord ++ tailWord_279801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279801).length < 2 ^ (prefixWord ++ tailWord_279801).sum := by decide
  have hdescent : baseEnd_279801 < baseStart_279801 := by decide
  rcases family_descends (prefixWord ++ tailWord_279801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279818 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_279818 : Nat := 118140960795 + 279818 * 2 ^ 59
def prefixEnd_279818 : Nat := 4983230072969 + 3 ^ 40 * 279818 * 2
def baseEnd_279818 : Nat := 63858279902173975328065

theorem tailTrace_279818 : CollatzResearch.WordTrace tailWord_279818 prefixEnd_279818 63858279902173975328065 := by
  unfold tailWord_279818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2551450225068662488706027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6803867266849766636549405 2551450225068662488706027)
  ·
    refine ⟨3827175337602993733059041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2551450225068662488706027 3827175337602993733059041)
    ·
      refine ⟨2870381503202245299794281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3827175337602993733059041 2870381503202245299794281)
      ·
        refine ⟨2152786127401683974845711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2870381503202245299794281 2152786127401683974845711)
        ·
          refine ⟨3229179191102525962268567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152786127401683974845711 3229179191102525962268567)
          ·
            refine ⟨4843768786653788943402851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229179191102525962268567 4843768786653788943402851)
            ·
              refine ⟨7265653179980683415104277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843768786653788943402851 7265653179980683415104277)
              ·
                refine ⟨340577492811594535083013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7265653179980683415104277 340577492811594535083013)
                ·
                  refine ⟨63858279902173975328065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340577492811594535083013 63858279902173975328065)
                  ·
                    rfl

theorem cell21_279818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_279818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279818 prefixEnd_279818 := by exact prefixLift 279818
  have htrace : WordTrace (prefixWord ++ tailWord_279818) baseStart_279818 baseEnd_279818 := by
    simpa [prefixWord, tailWord_279818, baseEnd_279818] using wordTrace_append hprefix tailTrace_279818
  have hstable : (prefixWord ++ tailWord_279818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279818).length < 2 ^ (prefixWord ++ tailWord_279818).sum := by decide
  have hdescent : baseEnd_279818 < baseStart_279818 := by decide
  rcases family_descends (prefixWord ++ tailWord_279818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279832 : List Nat := [2, 1, 2, 3, 1, 3, 1, 8]
def baseStart_279832 : Nat := 118140960795 + 279832 * 2 ^ 59
def prefixEnd_279832 : Nat := 4983230072969 + 3 ^ 40 * 279832 * 2
def baseEnd_279832 : Nat := 21287158297637687364901

theorem tailTrace_279832 : CollatzResearch.WordTrace tailWord_279832 prefixEnd_279832 21287158297637687364901 := by
  unfold tailWord_279832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103155761111965172916875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6804207681482620230555833 5103155761111965172916875)
  ·
    refine ⟨7654733641667947759375313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5103155761111965172916875 7654733641667947759375313)
    ·
      refine ⟨5741050231250960819531485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7654733641667947759375313 5741050231250960819531485)
      ·
        refine ⟨2152893836719110307324307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5741050231250960819531485 2152893836719110307324307)
        ·
          refine ⟨3229340755078665460986461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152893836719110307324307 3229340755078665460986461)
          ·
            refine ⟨1211002783154499547869923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3229340755078665460986461 1211002783154499547869923)
            ·
              refine ⟨1816504174731749321804885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211002783154499547869923 1816504174731749321804885)
              ·
                refine ⟨21287158297637687364901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1816504174731749321804885 21287158297637687364901)
                ·
                  rfl

theorem cell21_279832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_279832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279832 prefixEnd_279832 := by exact prefixLift 279832
  have htrace : WordTrace (prefixWord ++ tailWord_279832) baseStart_279832 baseEnd_279832 := by
    simpa [prefixWord, tailWord_279832, baseEnd_279832] using wordTrace_append hprefix tailTrace_279832
  have hstable : (prefixWord ++ tailWord_279832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279832).length < 2 ^ (prefixWord ++ tailWord_279832).sum := by decide
  have hdescent : baseEnd_279832 < baseStart_279832 := by decide
  rcases family_descends (prefixWord ++ tailWord_279832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279877 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_279877 : Nat := 118140960795 + 279877 * 2 ^ 59
def prefixEnd_279877 : Nat := 4983230072969 + 3 ^ 40 * 279877 * 2
def baseEnd_279877 : Nat := 63871744506002983844611

theorem tailTrace_279877 : CollatzResearch.WordTrace tailWord_279877 prefixEnd_279877 63871744506002983844611 := by
  unfold tailWord_279877
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207952807060903031221885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6805301871373935354147923 10207952807060903031221885)
  ·
    refine ⟨3827982302647838636708207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10207952807060903031221885 3827982302647838636708207)
    ·
      refine ⟨5741973453971757955062311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3827982302647838636708207 5741973453971757955062311)
      ·
        refine ⟨8612960180957636932593467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5741973453971757955062311 8612960180957636932593467)
        ·
          refine ⟨12919440271436455398890201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8612960180957636932593467 12919440271436455398890201)
          ·
            refine ⟨9689580203577341549167651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12919440271436455398890201 9689580203577341549167651)
            ·
              refine ⟨14534370305366012323751477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9689580203577341549167651 14534370305366012323751477)
              ·
                refine ⟨1362597216128063655351701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14534370305366012323751477 1362597216128063655351701)
                ·
                  refine ⟨63871744506002983844611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1362597216128063655351701 63871744506002983844611)
                  ·
                    rfl

theorem cell21_279877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_279877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279877 prefixEnd_279877 := by exact prefixLift 279877
  have htrace : WordTrace (prefixWord ++ tailWord_279877) baseStart_279877 baseEnd_279877 := by
    simpa [prefixWord, tailWord_279877, baseEnd_279877] using wordTrace_append hprefix tailTrace_279877
  have hstable : (prefixWord ++ tailWord_279877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279877).length < 2 ^ (prefixWord ++ tailWord_279877).sum := by decide
  have hdescent : baseEnd_279877 < baseStart_279877 := by decide
  rcases family_descends (prefixWord ++ tailWord_279877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279914 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_279914 : Nat := 118140960795 + 279914 * 2 ^ 59
def prefixEnd_279914 : Nat := 4983230072969 + 3 ^ 40 * 279914 * 2
def baseEnd_279914 : Nat := 63880188410099141727869

theorem tailTrace_279914 : CollatzResearch.WordTrace tailWord_279914 prefixEnd_279914 63880188410099141727869 := by
  unfold tailWord_279914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552325576981714587579699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6806201538617905566879197 2552325576981714587579699)
  ·
    refine ⟨3828488365472571881369549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2552325576981714587579699 3828488365472571881369549)
    ·
      refine ⟨1435683137052214455513581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3828488365472571881369549 1435683137052214455513581)
      ·
        refine ⟨538381176394580420817593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1435683137052214455513581 538381176394580420817593)
        ·
          refine ⟨403785882295935315613195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538381176394580420817593 403785882295935315613195)
          ·
            refine ⟨605678823443902973419793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403785882295935315613195 605678823443902973419793)
            ·
              refine ⟨454259117582927230064845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605678823443902973419793 454259117582927230064845)
              ·
                refine ⟨170347169093597711274317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 454259117582927230064845 170347169093597711274317)
                ·
                  refine ⟨63880188410099141727869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170347169093597711274317 63880188410099141727869)
                  ·
                    rfl

theorem cell21_279914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_279914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279914 prefixEnd_279914 := by exact prefixLift 279914
  have htrace : WordTrace (prefixWord ++ tailWord_279914) baseStart_279914 baseEnd_279914 := by
    simpa [prefixWord, tailWord_279914, baseEnd_279914] using wordTrace_append hprefix tailTrace_279914
  have hstable : (prefixWord ++ tailWord_279914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279914).length < 2 ^ (prefixWord ++ tailWord_279914).sum := by decide
  have hdescent : baseEnd_279914 < baseStart_279914 := by decide
  rcases family_descends (prefixWord ++ tailWord_279914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279925 : List Nat := [1, 3, 4, 1, 3, 1, 8]
def baseStart_279925 : Nat := 118140960795 + 279925 * 2 ^ 59
def prefixEnd_279925 : Nat := 4983230072969 + 3 ^ 40 * 279925 * 2
def baseEnd_279925 : Nat := 7098077639996174116057

theorem tailTrace_279925 : CollatzResearch.WordTrace tailWord_279925 prefixEnd_279925 7098077639996174116057 := by
  unfold tailWord_279925
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209703510887007228969229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6806469007258004819312819 10209703510887007228969229)
  ·
    refine ⟨3828638816582627710863461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10209703510887007228969229 3828638816582627710863461)
    ·
      refine ⟨717869778109242695786899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3828638816582627710863461 717869778109242695786899)
      ·
        refine ⟨1076804667163864043680349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717869778109242695786899 1076804667163864043680349)
        ·
          refine ⟨403801750186449016380131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1076804667163864043680349 403801750186449016380131)
          ·
            refine ⟨605702625279673524570197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403801750186449016380131 605702625279673524570197)
            ·
              refine ⟨7098077639996174116057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 605702625279673524570197 7098077639996174116057)
              ·
                rfl

theorem cell21_279925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 8].length) (baseStart_279925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279925 prefixEnd_279925 := by exact prefixLift 279925
  have htrace : WordTrace (prefixWord ++ tailWord_279925) baseStart_279925 baseEnd_279925 := by
    simpa [prefixWord, tailWord_279925, baseEnd_279925] using wordTrace_append hprefix tailTrace_279925
  have hstable : (prefixWord ++ tailWord_279925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279925).length < 2 ^ (prefixWord ++ tailWord_279925).sum := by decide
  have hdescent : baseEnd_279925 < baseStart_279925 := by decide
  rcases family_descends (prefixWord ++ tailWord_279925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279939 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_279939 : Nat := 118140960795 + 279939 * 2 ^ 59
def prefixEnd_279939 : Nat := 4983230072969 + 3 ^ 40 * 279939 * 2
def baseEnd_279939 : Nat := 63885893750704653811151

theorem tailTrace_279939 : CollatzResearch.WordTrace tailWord_279939 prefixEnd_279939 63885893750704653811151 := by
  unfold tailWord_279939
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210214132836287619978871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6806809421890858413319247 10210214132836287619978871)
  ·
    refine ⟨15315321199254431429968307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210214132836287619978871 15315321199254431429968307)
    ·
      refine ⟨22972981798881647144952461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15315321199254431429968307 22972981798881647144952461)
      ·
        refine ⟨8614868174580617679357173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22972981798881647144952461 8614868174580617679357173)
        ·
          refine ⟨807643891366932907439735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8614868174580617679357173 807643891366932907439735)
          ·
            refine ⟨1211465837050399361159603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807643891366932907439735 1211465837050399361159603)
            ·
              refine ⟨1817198755575599041739405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211465837050399361159603 1817198755575599041739405)
              ·
                refine ⟨681449533340849640652277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817198755575599041739405 681449533340849640652277)
                ·
                  refine ⟨63885893750704653811151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681449533340849640652277 63885893750704653811151)
                  ·
                    rfl

theorem cell21_279939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_279939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279939 prefixEnd_279939 := by exact prefixLift 279939
  have htrace : WordTrace (prefixWord ++ tailWord_279939) baseStart_279939 baseEnd_279939 := by
    simpa [prefixWord, tailWord_279939, baseEnd_279939] using wordTrace_append hprefix tailTrace_279939
  have hstable : (prefixWord ++ tailWord_279939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279939).length < 2 ^ (prefixWord ++ tailWord_279939).sum := by decide
  have hdescent : baseEnd_279939 < baseStart_279939 := by decide
  rcases family_descends (prefixWord ++ tailWord_279939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279956 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_279956 : Nat := 118140960795 + 279956 * 2 ^ 59
def prefixEnd_279956 : Nat := 4983230072969 + 3 ^ 40 * 279956 * 2
def baseEnd_279956 : Nat := 63889773382316402027783

theorem tailTrace_279956 : CollatzResearch.WordTrace tailWord_279956 prefixEnd_279956 63889773382316402027783 := by
  unfold tailWord_279956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5105417086887349761673861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6807222782516466348898481 5105417086887349761673861)
  ·
    refine ⟨957265703791378080313849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5105417086887349761673861 957265703791378080313849)
    ·
      refine ⟨717949277843533560235387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 957265703791378080313849 717949277843533560235387)
      ·
        refine ⟨1076923916765300340353081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717949277843533560235387 1076923916765300340353081)
        ·
          refine ⟨807692937573975255264811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076923916765300340353081 807692937573975255264811)
          ·
            refine ⟨1211539406360962882897217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807692937573975255264811 1211539406360962882897217)
            ·
              refine ⟨908654554770722162172913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211539406360962882897217 908654554770722162172913)
              ·
                refine ⟨681490916078041621629685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908654554770722162172913 681490916078041621629685)
                ·
                  refine ⟨63889773382316402027783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681490916078041621629685 63889773382316402027783)
                  ·
                    rfl

theorem cell21_279956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_279956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279956 prefixEnd_279956 := by exact prefixLift 279956
  have htrace : WordTrace (prefixWord ++ tailWord_279956) baseStart_279956 baseEnd_279956 := by
    simpa [prefixWord, tailWord_279956, baseEnd_279956] using wordTrace_append hprefix tailTrace_279956
  have hstable : (prefixWord ++ tailWord_279956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279956).length < 2 ^ (prefixWord ++ tailWord_279956).sum := by decide
  have hdescent : baseEnd_279956 < baseStart_279956 := by decide
  rcases family_descends (prefixWord ++ tailWord_279956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279970 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_279970 : Nat := 118140960795 + 279970 * 2 ^ 59
def prefixEnd_279970 : Nat := 4983230072969 + 3 ^ 40 * 279970 * 2
def baseEnd_279970 : Nat := 63892968373055488794421

theorem tailTrace_279970 : CollatzResearch.WordTrace tailWord_279970 prefixEnd_279970 63892968373055488794421 := by
  unfold tailWord_279970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552836198930994978589341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6807563197149319942904909 2552836198930994978589341)
  ·
    refine ⟨957313574599123116971003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2552836198930994978589341 957313574599123116971003)
    ·
      refine ⟨1435970361898684675456505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957313574599123116971003 1435970361898684675456505)
      ·
        refine ⟨1076977771424013506592379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1435970361898684675456505 1076977771424013506592379)
        ·
          refine ⟨1615466657136020259888569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076977771424013506592379 1615466657136020259888569)
          ·
            refine ⟨1211599992852015194916427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615466657136020259888569 1211599992852015194916427)
            ·
              refine ⟨1817399989278022792374641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211599992852015194916427 1817399989278022792374641)
              ·
                refine ⟨1363049991958517094280981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817399989278022792374641 1363049991958517094280981)
                ·
                  refine ⟨63892968373055488794421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1363049991958517094280981 63892968373055488794421)
                  ·
                    rfl

theorem cell21_279970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_279970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_279970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_279970 prefixEnd_279970 := by exact prefixLift 279970
  have htrace : WordTrace (prefixWord ++ tailWord_279970) baseStart_279970 baseEnd_279970 := by
    simpa [prefixWord, tailWord_279970, baseEnd_279970] using wordTrace_append hprefix tailTrace_279970
  have hstable : (prefixWord ++ tailWord_279970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279970).length < 2 ^ (prefixWord ++ tailWord_279970).sum := by decide
  have hdescent : baseEnd_279970 < baseStart_279970 := by decide
  rcases family_descends (prefixWord ++ tailWord_279970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280004 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_280004 : Nat := 118140960795 + 280004 * 2 ^ 59
def prefixEnd_280004 : Nat := 4983230072969 + 3 ^ 40 * 280004 * 2
def baseEnd_280004 : Nat := 63900727636278985227685

theorem tailTrace_280004 : CollatzResearch.WordTrace tailWord_280004 prefixEnd_280004 63900727636278985227685 := by
  unfold tailWord_280004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106292438800401860547533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6808389918400535814063377 5106292438800401860547533)
  ·
    refine ⟨1914859664550150697705325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5106292438800401860547533 1914859664550150697705325)
    ·
      refine ⟨718072374206306511639497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1914859664550150697705325 718072374206306511639497)
      ·
        refine ⟨538554280654729883729623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718072374206306511639497 538554280654729883729623)
        ·
          refine ⟨807831420982094825594435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538554280654729883729623 807831420982094825594435)
          ·
            refine ⟨1211747131473142238391653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807831420982094825594435 1211747131473142238391653)
            ·
              refine ⟨227202587151214169698435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1211747131473142238391653 227202587151214169698435)
              ·
                refine ⟨340803880726821254547653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227202587151214169698435 340803880726821254547653)
                ·
                  refine ⟨63900727636278985227685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340803880726821254547653 63900727636278985227685)
                  ·
                    rfl

theorem cell21_280004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_280004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280004 prefixEnd_280004 := by exact prefixLift 280004
  have htrace : WordTrace (prefixWord ++ tailWord_280004) baseStart_280004 baseEnd_280004 := by
    simpa [prefixWord, tailWord_280004, baseEnd_280004] using wordTrace_append hprefix tailTrace_280004
  have hstable : (prefixWord ++ tailWord_280004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280004).length < 2 ^ (prefixWord ++ tailWord_280004).sum := by decide
  have hdescent : baseEnd_280004 < baseStart_280004 := by decide
  rcases family_descends (prefixWord ++ tailWord_280004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280049 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 3]
def baseStart_280049 : Nat := 118140960795 + 280049 * 2 ^ 59
def prefixEnd_280049 : Nat := 4983230072969 + 3 ^ 40 * 280049 * 2
def baseEnd_280049 : Nat := 63910997249368906977593

theorem tailTrace_280049 : CollatzResearch.WordTrace tailWord_280049 prefixEnd_280049 63910997249368906977593 := by
  unfold tailWord_280049
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214226162437776406483201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6809484108291850937655467 10214226162437776406483201)
  ·
    refine ⟨7660669621828332304862401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10214226162437776406483201 7660669621828332304862401)
    ·
      refine ⟨5745502216371249228646801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7660669621828332304862401 5745502216371249228646801)
      ·
        refine ⟨4309126662278436921485101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5745502216371249228646801 4309126662278436921485101)
        ·
          refine ⟨1615922498354413845556913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4309126662278436921485101 1615922498354413845556913)
          ·
            refine ⟨1211941873765810384167685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615922498354413845556913 1211941873765810384167685)
            ·
              refine ⟨227239101331089447031441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1211941873765810384167685 227239101331089447031441)
              ·
                refine ⟨170429325998317085273581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227239101331089447031441 170429325998317085273581)
                ·
                  refine ⟨63910997249368906977593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170429325998317085273581 63910997249368906977593)
                  ·
                    rfl

theorem cell21_280049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_280049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280049 prefixEnd_280049 := by exact prefixLift 280049
  have htrace : WordTrace (prefixWord ++ tailWord_280049) baseStart_280049 baseEnd_280049 := by
    simpa [prefixWord, tailWord_280049, baseEnd_280049] using wordTrace_append hprefix tailTrace_280049
  have hstable : (prefixWord ++ tailWord_280049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280049).length < 2 ^ (prefixWord ++ tailWord_280049).sum := by decide
  have hdescent : baseEnd_280049 < baseStart_280049 := by decide
  rcases family_descends (prefixWord ++ tailWord_280049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280060 : List Nat := [2, 2, 2, 1, 2, 1, 5, 6]
def baseStart_280060 : Nat := 118140960795 + 280060 * 2 ^ 59
def prefixEnd_280060 : Nat := 4983230072969 + 3 ^ 40 * 280060 * 2
def baseEnd_280060 : Nat := 21304502533078444098079

theorem tailTrace_280060 : CollatzResearch.WordTrace tailWord_280060 prefixEnd_280060 21304502533078444098079 := by
  unfold tailWord_280060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5107313682698962642566817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6809751576931950190089089 5107313682698962642566817)
  ·
    refine ⟨3830485262024221981925113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5107313682698962642566817 3830485262024221981925113)
    ·
      refine ⟨2872863946518166486443835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3830485262024221981925113 2872863946518166486443835)
      ·
        refine ⟨4309295919777249729665753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872863946518166486443835 4309295919777249729665753)
        ·
          refine ⟨3231971939832937297249315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4309295919777249729665753 3231971939832937297249315)
          ·
            refine ⟨4847957909749405945873973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231971939832937297249315 4847957909749405945873973)
            ·
              refine ⟨454496054039006807425685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4847957909749405945873973 454496054039006807425685)
              ·
                refine ⟨21304502533078444098079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 454496054039006807425685 21304502533078444098079)
                ·
                  rfl

theorem cell21_280060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_280060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280060 prefixEnd_280060 := by exact prefixLift 280060
  have htrace : WordTrace (prefixWord ++ tailWord_280060) baseStart_280060 baseEnd_280060 := by
    simpa [prefixWord, tailWord_280060, baseEnd_280060] using wordTrace_append hprefix tailTrace_280060
  have hstable : (prefixWord ++ tailWord_280060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280060).length < 2 ^ (prefixWord ++ tailWord_280060).sum := by decide
  have hdescent : baseEnd_280060 < baseStart_280060 := by decide
  rcases family_descends (prefixWord ++ tailWord_280060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280167 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_280167 : Nat := 118140960795 + 280167 * 2 ^ 59
def prefixEnd_280167 : Nat := 4983230072969 + 3 ^ 40 * 280167 * 2
def baseEnd_280167 : Nat := 63937926457026924010685

theorem tailTrace_280167 : CollatzResearch.WordTrace tailWord_280167 prefixEnd_280167 63937926457026924010685 := by
  unfold tailWord_280167
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218529976010282559278755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6812353317340188372852503 10218529976010282559278755)
  ·
    refine ⟨15327794964015423838918133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10218529976010282559278755 15327794964015423838918133)
    ·
      refine ⟨1436980777876445984898575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15327794964015423838918133 1436980777876445984898575)
      ·
        refine ⟨2155471166814668977347863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436980777876445984898575 2155471166814668977347863)
        ·
          refine ⟨3233206750222003466021795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155471166814668977347863 3233206750222003466021795)
          ·
            refine ⟨4849810125333005199032693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233206750222003466021795 4849810125333005199032693)
            ·
              refine ⟨454669699249969237409315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4849810125333005199032693 454669699249969237409315)
              ·
                refine ⟨682004548874953856113973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454669699249969237409315 682004548874953856113973)
                ·
                  refine ⟨63937926457026924010685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 682004548874953856113973 63937926457026924010685)
                  ·
                    rfl

theorem cell21_280167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_280167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280167 prefixEnd_280167 := by exact prefixLift 280167
  have htrace : WordTrace (prefixWord ++ tailWord_280167) baseStart_280167 baseEnd_280167 := by
    simpa [prefixWord, tailWord_280167, baseEnd_280167] using wordTrace_append hprefix tailTrace_280167
  have hstable : (prefixWord ++ tailWord_280167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280167).length < 2 ^ (prefixWord ++ tailWord_280167).sum := by decide
  have hdescent : baseEnd_280167 < baseStart_280167 := by decide
  rcases family_descends (prefixWord ++ tailWord_280167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280173 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 4]
def baseStart_280173 : Nat := 118140960795 + 280173 * 2 ^ 59
def prefixEnd_280173 : Nat := 4983230072969 + 3 ^ 40 * 280173 * 2
def baseEnd_280173 : Nat := 63939295738772246910673

theorem tailTrace_280173 : CollatzResearch.WordTrace tailWord_280173 prefixEnd_280173 63939295738772246910673 := by
  unfold tailWord_280173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218748813988545583997173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6812499209325697055998115 10218748813988545583997173)
  ·
    refine ⟨958007701311426148499735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10218748813988545583997173 958007701311426148499735)
    ·
      refine ⟨1437011551967139222749603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958007701311426148499735 1437011551967139222749603)
      ·
        refine ⟨2155517327950708834124405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437011551967139222749603 2155517327950708834124405)
        ·
          refine ⟨202079749495378953199163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2155517327950708834124405 202079749495378953199163)
          ·
            refine ⟨303119624243068429798745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202079749495378953199163 303119624243068429798745)
            ·
              refine ⟨227339718182301322349059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303119624243068429798745 227339718182301322349059)
              ·
                refine ⟨341009577273451983523589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227339718182301322349059 341009577273451983523589)
                ·
                  refine ⟨63939295738772246910673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341009577273451983523589 63939295738772246910673)
                  ·
                    rfl

theorem cell21_280173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_280173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280173 prefixEnd_280173 := by exact prefixLift 280173
  have htrace : WordTrace (prefixWord ++ tailWord_280173) baseStart_280173 baseEnd_280173 := by
    simpa [prefixWord, tailWord_280173, baseEnd_280173] using wordTrace_append hprefix tailTrace_280173
  have hstable : (prefixWord ++ tailWord_280173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280173).length < 2 ^ (prefixWord ++ tailWord_280173).sum := by decide
  have hdescent : baseEnd_280173 < baseStart_280173 := by decide
  rcases family_descends (prefixWord ++ tailWord_280173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280212 : List Nat := [2, 4, 2, 2, 11]
def baseStart_280212 : Nat := 118140960795 + 280212 * 2 ^ 59
def prefixEnd_280212 : Nat := 4983230072969 + 3 ^ 40 * 280212 * 2
def baseEnd_280212 : Nat := 789483902100207972353

theorem tailTrace_280212 : CollatzResearch.WordTrace tailWord_280212 prefixEnd_280212 789483902100207972353 := by
  unfold tailWord_280212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110085630423627622333445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6813447507231503496444593 5110085630423627622333445)
  ·
    refine ⟨958141055704430179187521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5110085630423627622333445 958141055704430179187521)
    ·
      refine ⟨718605791778322634390641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958141055704430179187521 718605791778322634390641)
      ·
        refine ⟨538954343833741975792981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718605791778322634390641 538954343833741975792981)
        ·
          refine ⟨789483902100207972353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 538954343833741975792981 789483902100207972353)
          ·
            rfl

theorem cell21_280212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 11].length) (baseStart_280212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280212 prefixEnd_280212 := by exact prefixLift 280212
  have htrace : WordTrace (prefixWord ++ tailWord_280212) baseStart_280212 baseEnd_280212 := by
    simpa [prefixWord, tailWord_280212, baseEnd_280212] using wordTrace_append hprefix tailTrace_280212
  have hstable : (prefixWord ++ tailWord_280212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280212).length < 2 ^ (prefixWord ++ tailWord_280212).sum := by decide
  have hdescent : baseEnd_280212 < baseStart_280212 := by decide
  rcases family_descends (prefixWord ++ tailWord_280212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280274 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_280274 : Nat := 118140960795 + 280274 * 2 ^ 59
def prefixEnd_280274 : Nat := 4983230072969 + 3 ^ 40 * 280274 * 2
def baseEnd_280274 : Nat := 63962345314818515727133

theorem tailTrace_280274 : CollatzResearch.WordTrace tailWord_280274 prefixEnd_280274 63962345314818515727133 := by
  unfold tailWord_280274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555608146655659958355969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6814955057748426555615917 2555608146655659958355969)
  ·
    refine ⟨1916706109991744968766977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2555608146655659958355969 1916706109991744968766977)
    ·
      refine ⟨1437529582493808726575233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1916706109991744968766977 1437529582493808726575233)
      ·
        refine ⟨1078147186870356544931425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437529582493808726575233 1078147186870356544931425)
        ·
          refine ⟨808610390152767408698569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078147186870356544931425 808610390152767408698569)
          ·
            refine ⟨606457792614575556523927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808610390152767408698569 606457792614575556523927)
            ·
              refine ⟨909686688921863334785891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606457792614575556523927 909686688921863334785891)
              ·
                refine ⟨1364530033382795002178837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909686688921863334785891 1364530033382795002178837)
                ·
                  refine ⟨63962345314818515727133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1364530033382795002178837 63962345314818515727133)
                  ·
                    rfl

theorem cell21_280274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_280274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280274 prefixEnd_280274 := by exact prefixLift 280274
  have htrace : WordTrace (prefixWord ++ tailWord_280274) baseStart_280274 baseEnd_280274 := by
    simpa [prefixWord, tailWord_280274, baseEnd_280274] using wordTrace_append hprefix tailTrace_280274
  have hstable : (prefixWord ++ tailWord_280274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280274).length < 2 ^ (prefixWord ++ tailWord_280274).sum := by decide
  have hdescent : baseEnd_280274 < baseStart_280274 := by decide
  rcases family_descends (prefixWord ++ tailWord_280274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280305 : List Nat := [1, 2, 2, 2, 2, 5, 2, 5]
def baseStart_280305 : Nat := 118140960795 + 280305 * 2 ^ 59
def prefixEnd_280305 : Nat := 4983230072969 + 3 ^ 40 * 280305 * 2
def baseEnd_280305 : Nat := 21323139979056450236801

theorem tailTrace_280305 : CollatzResearch.WordTrace tailWord_280305 prefixEnd_280305 21323139979056450236801 := by
  unfold tailWord_280305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223563249510332127802369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6815708833006888085201579 10223563249510332127802369)
  ·
    refine ⟨7667672437132749095851777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10223563249510332127802369 7667672437132749095851777)
    ·
      refine ⟨5750754327849561821888833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7667672437132749095851777 5750754327849561821888833)
      ·
        refine ⟨4313065745887171366416625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5750754327849561821888833 4313065745887171366416625)
        ·
          refine ⟨3234799309415378524812469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4313065745887171366416625 3234799309415378524812469)
          ·
            refine ⟨303262435257691736701169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3234799309415378524812469 303262435257691736701169)
            ·
              refine ⟨227446826443268802525877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303262435257691736701169 227446826443268802525877)
              ·
                refine ⟨21323139979056450236801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227446826443268802525877 21323139979056450236801)
                ·
                  rfl

theorem cell21_280305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 5].length) (baseStart_280305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280305 prefixEnd_280305 := by exact prefixLift 280305
  have htrace : WordTrace (prefixWord ++ tailWord_280305) baseStart_280305 baseEnd_280305 := by
    simpa [prefixWord, tailWord_280305, baseEnd_280305] using wordTrace_append hprefix tailTrace_280305
  have hstable : (prefixWord ++ tailWord_280305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280305).length < 2 ^ (prefixWord ++ tailWord_280305).sum := by decide
  have hdescent : baseEnd_280305 < baseStart_280305 := by decide
  rcases family_descends (prefixWord ++ tailWord_280305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280409 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_280409 : Nat := 118140960795 + 280409 * 2 ^ 59
def prefixEnd_280409 : Nat := 4983230072969 + 3 ^ 40 * 280409 * 2
def baseEnd_280409 : Nat := 63993154154088280976857

theorem tailTrace_280409 : CollatzResearch.WordTrace tailWord_280409 prefixEnd_280409 63993154154088280976857 := by
  unfold tailWord_280409
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227356441133557889588281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6818237627422371926392187 10227356441133557889588281)
  ·
    refine ⟨7670517330850168417191211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10227356441133557889588281 7670517330850168417191211)
    ·
      refine ⟨11505775996275252625786817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7670517330850168417191211 11505775996275252625786817)
      ·
        refine ⟨8629331997206439469340113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11505775996275252625786817 8629331997206439469340113)
        ·
          refine ⟨6471998997904829602005085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8629331997206439469340113 6471998997904829602005085)
          ·
            refine ⟨2426999624214311100751907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6471998997904829602005085 2426999624214311100751907)
            ·
              refine ⟨3640499436321466651127861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426999624214311100751907 3640499436321466651127861)
              ·
                refine ⟨341296822155137498543237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3640499436321466651127861 341296822155137498543237)
                ·
                  refine ⟨63993154154088280976857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341296822155137498543237 63993154154088280976857)
                  ·
                    rfl

theorem cell21_280409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_280409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280409 prefixEnd_280409 := by exact prefixLift 280409
  have htrace : WordTrace (prefixWord ++ tailWord_280409) baseStart_280409 baseEnd_280409 := by
    simpa [prefixWord, tailWord_280409, baseEnd_280409] using wordTrace_append hprefix tailTrace_280409
  have hstable : (prefixWord ++ tailWord_280409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280409).length < 2 ^ (prefixWord ++ tailWord_280409).sum := by decide
  have hdescent : baseEnd_280409 < baseStart_280409 := by decide
  rcases family_descends (prefixWord ++ tailWord_280409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280412 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_280412 : Nat := 118140960795 + 280412 * 2 ^ 59
def prefixEnd_280412 : Nat := 4983230072969 + 3 ^ 40 * 280412 * 2
def baseEnd_280412 : Nat := 63993838794960942426851

theorem tailTrace_280412 : CollatzResearch.WordTrace tailWord_280412 prefixEnd_280412 63993838794960942426851 := by
  unfold tailWord_280412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5113732930061344700973745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6818310573415126267964993 5113732930061344700973745)
  ·
    refine ⟨3835299697546008525730309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5113732930061344700973745 3835299697546008525730309)
    ·
      refine ⟨719118693289876598574433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3835299697546008525730309 719118693289876598574433)
      ·
        refine ⟨539339019967407448930825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 719118693289876598574433 539339019967407448930825)
        ·
          refine ⟨404504264975555586698119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539339019967407448930825 404504264975555586698119)
          ·
            refine ⟨606756397463333380047179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404504264975555586698119 606756397463333380047179)
            ·
              refine ⟨910134596195000070070769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606756397463333380047179 910134596195000070070769)
              ·
                refine ⟨682600947146250052553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910134596195000070070769 682600947146250052553077)
                ·
                  refine ⟨63993838794960942426851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 682600947146250052553077 63993838794960942426851)
                  ·
                    rfl

theorem cell21_280412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_280412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280412 prefixEnd_280412 := by exact prefixLift 280412
  have htrace : WordTrace (prefixWord ++ tailWord_280412) baseStart_280412 baseEnd_280412 := by
    simpa [prefixWord, tailWord_280412, baseEnd_280412] using wordTrace_append hprefix tailTrace_280412
  have hstable : (prefixWord ++ tailWord_280412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280412).length < 2 ^ (prefixWord ++ tailWord_280412).sum := by decide
  have hdescent : baseEnd_280412 < baseStart_280412 := by decide
  rcases family_descends (prefixWord ++ tailWord_280412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280544 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_280544 : Nat := 118140960795 + 280544 * 2 ^ 59
def prefixEnd_280544 : Nat := 4983230072969 + 3 ^ 40 * 280544 * 2
def baseEnd_280544 : Nat := 64023962993358046226581

theorem tailTrace_280544 : CollatzResearch.WordTrace tailWord_280544 prefixEnd_280544 64023962993358046226581 := by
  unfold tailWord_280544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5116140147822237972876343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6821520197096317297168457 5116140147822237972876343)
  ·
    refine ⟨7674210221733356959314515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5116140147822237972876343 7674210221733356959314515)
    ·
      refine ⟨11511315332600035438971773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7674210221733356959314515 11511315332600035438971773)
      ·
        refine ⟨4316743249725013289614415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11511315332600035438971773 4316743249725013289614415)
        ·
          refine ⟨6475114874587519934421623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316743249725013289614415 6475114874587519934421623)
          ·
            refine ⟨9712672311881279901632435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475114874587519934421623 9712672311881279901632435)
            ·
              refine ⟨14569008467821919852448653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9712672311881279901632435 14569008467821919852448653)
              ·
                refine ⟨5463378175433219944668245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14569008467821919852448653 5463378175433219944668245)
                ·
                  refine ⟨64023962993358046226581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5463378175433219944668245 64023962993358046226581)
                  ·
                    rfl

theorem cell21_280544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_280544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280544 prefixEnd_280544 := by exact prefixLift 280544
  have htrace : WordTrace (prefixWord ++ tailWord_280544) baseStart_280544 baseEnd_280544 := by
    simpa [prefixWord, tailWord_280544, baseEnd_280544] using wordTrace_append hprefix tailTrace_280544
  have hstable : (prefixWord ++ tailWord_280544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280544).length < 2 ^ (prefixWord ++ tailWord_280544).sum := by decide
  have hdescent : baseEnd_280544 < baseStart_280544 := by decide
  rcases family_descends (prefixWord ++ tailWord_280544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280612 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_280612 : Nat := 118140960795 + 280612 * 2 ^ 59
def prefixEnd_280612 : Nat := 4983230072969 + 3 ^ 40 * 280612 * 2
def baseEnd_280612 : Nat := 64039481519805039093109

theorem tailTrace_280612 : CollatzResearch.WordTrace tailWord_280612 prefixEnd_280612 64039481519805039093109 := by
  unfold tailWord_280612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117380229699061779614045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6823173639598749039485393 5117380229699061779614045)
  ·
    refine ⟨1919017586137148167355267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5117380229699061779614045 1919017586137148167355267)
    ·
      refine ⟨2878526379205722251032901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1919017586137148167355267 2878526379205722251032901)
      ·
        refine ⟨539723696101072922068669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2878526379205722251032901 539723696101072922068669)
        ·
          refine ⟨202396386037902345775751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539723696101072922068669 202396386037902345775751)
          ·
            refine ⟨303594579056853518663627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202396386037902345775751 303594579056853518663627)
            ·
              refine ⟨455391868585280277995441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303594579056853518663627 455391868585280277995441)
              ·
                refine ⟨341543901438960208496581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455391868585280277995441 341543901438960208496581)
                ·
                  refine ⟨64039481519805039093109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341543901438960208496581 64039481519805039093109)
                  ·
                    rfl

theorem cell21_280612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_280612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280612 prefixEnd_280612 := by exact prefixLift 280612
  have htrace : WordTrace (prefixWord ++ tailWord_280612) baseStart_280612 baseEnd_280612 := by
    simpa [prefixWord, tailWord_280612, baseEnd_280612] using wordTrace_append hprefix tailTrace_280612
  have hstable : (prefixWord ++ tailWord_280612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280612).length < 2 ^ (prefixWord ++ tailWord_280612).sum := by decide
  have hdescent : baseEnd_280612 < baseStart_280612 := by decide
  rcases family_descends (prefixWord ++ tailWord_280612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280668 : List Nat := [2, 2, 4, 1, 1, 4, 7]
def baseStart_280668 : Nat := 118140960795 + 280668 * 2 ^ 59
def prefixEnd_280668 : Nat := 4983230072969 + 3 ^ 40 * 280668 * 2
def baseEnd_280668 : Nat := 7116917942529042906629

theorem tailTrace_280668 : CollatzResearch.WordTrace tailWord_280668 prefixEnd_280668 7116917942529042906629 := by
  unfold tailWord_280668
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118401473597622561633329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6824535298130163415511105 5118401473597622561633329)
  ·
    refine ⟨3838801105198216921224997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5118401473597622561633329 3838801105198216921224997)
    ·
      refine ⟨719775207224665672729687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3838801105198216921224997 719775207224665672729687)
      ·
        refine ⟨1079662810836998509094531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719775207224665672729687 1079662810836998509094531)
        ·
          refine ⟨1619494216255497763641797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079662810836998509094531 1619494216255497763641797)
          ·
            refine ⟨303655165547905830682837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1619494216255497763641797 303655165547905830682837)
            ·
              refine ⟨7116917942529042906629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 303655165547905830682837 7116917942529042906629)
              ·
                rfl

theorem cell21_280668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 7].length) (baseStart_280668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280668 prefixEnd_280668 := by exact prefixLift 280668
  have htrace : WordTrace (prefixWord ++ tailWord_280668) baseStart_280668 baseEnd_280668 := by
    simpa [prefixWord, tailWord_280668, baseEnd_280668] using wordTrace_append hprefix tailTrace_280668
  have hstable : (prefixWord ++ tailWord_280668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280668).length < 2 ^ (prefixWord ++ tailWord_280668).sum := by decide
  have hdescent : baseEnd_280668 < baseStart_280668 := by decide
  rcases family_descends (prefixWord ++ tailWord_280668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280674 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_280674 : Nat := 118140960795 + 280674 * 2 ^ 59
def prefixEnd_280674 : Nat := 4983230072969 + 3 ^ 40 * 280674 * 2
def baseEnd_280674 : Nat := 64053630764506709059649

theorem tailTrace_280674 : CollatzResearch.WordTrace tailWord_280674 prefixEnd_280674 64053630764506709059649 := by
  unfold tailWord_280674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559255446293377036996269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6824681190115672098656717 2559255446293377036996269)
  ·
    refine ⟨959720792360016388873601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2559255446293377036996269 959720792360016388873601)
    ·
      refine ⟨719790594270012291655201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959720792360016388873601 719790594270012291655201)
      ·
        refine ⟨539842945702509218741401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 719790594270012291655201 539842945702509218741401)
        ·
          refine ⟨404882209276881914056051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539842945702509218741401 404882209276881914056051)
          ·
            refine ⟨607323313915322871084077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404882209276881914056051 607323313915322871084077)
            ·
              refine ⟨227746242718246076656529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607323313915322871084077 227746242718246076656529)
              ·
                refine ⟨170809682038684557492397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227746242718246076656529 170809682038684557492397)
                ·
                  refine ⟨64053630764506709059649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170809682038684557492397 64053630764506709059649)
                  ·
                    rfl

theorem cell21_280674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_280674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280674 prefixEnd_280674 := by exact prefixLift 280674
  have htrace : WordTrace (prefixWord ++ tailWord_280674) baseStart_280674 baseEnd_280674 := by
    simpa [prefixWord, tailWord_280674, baseEnd_280674] using wordTrace_append hprefix tailTrace_280674
  have hstable : (prefixWord ++ tailWord_280674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280674).length < 2 ^ (prefixWord ++ tailWord_280674).sum := by decide
  have hdescent : baseEnd_280674 < baseStart_280674 := by decide
  rcases family_descends (prefixWord ++ tailWord_280674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280727 : List Nat := [1, 1, 3, 3, 4, 9]
def baseStart_280727 : Nat := 118140960795 + 280727 * 2 ^ 59
def prefixEnd_280727 : Nat := 4983230072969 + 3 ^ 40 * 280727 * 2
def baseEnd_280727 : Nat := 2372804669873718321341

theorem tailTrace_280727 : CollatzResearch.WordTrace tailWord_280727 prefixEnd_280727 2372804669873718321341 := by
  unfold tailWord_280727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10238954853981498199664435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6825969902654332133109623 10238954853981498199664435)
  ·
    refine ⟨15358432280972247299496653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10238954853981498199664435 15358432280972247299496653)
    ·
      refine ⟨5759412105364592737311245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15358432280972247299496653 5759412105364592737311245)
      ·
        refine ⟨2159779539511722276491717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5759412105364592737311245 2159779539511722276491717)
        ·
          refine ⟨404958663658447926842197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2159779539511722276491717 404958663658447926842197)
          ·
            refine ⟨2372804669873718321341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 404958663658447926842197 2372804669873718321341)
            ·
              rfl

theorem cell21_280727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 9].length) (baseStart_280727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280727 prefixEnd_280727 := by exact prefixLift 280727
  have htrace : WordTrace (prefixWord ++ tailWord_280727) baseStart_280727 baseEnd_280727 := by
    simpa [prefixWord, tailWord_280727, baseEnd_280727] using wordTrace_append hprefix tailTrace_280727
  have hstable : (prefixWord ++ tailWord_280727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280727).length < 2 ^ (prefixWord ++ tailWord_280727).sum := by decide
  have hdescent : baseEnd_280727 < baseStart_280727 := by decide
  rcases family_descends (prefixWord ++ tailWord_280727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280733 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 3]
def baseStart_280733 : Nat := 118140960795 + 280733 * 2 ^ 59
def prefixEnd_280733 : Nat := 4983230072969 + 3 ^ 40 * 280733 * 2
def baseEnd_280733 : Nat := 64067095368335717576195

theorem tailTrace_280733 : CollatzResearch.WordTrace tailWord_280733 prefixEnd_280733 64067095368335717576195 := by
  unfold tailWord_280733
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239173691959761224382853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6826115794639840816255235 10239173691959761224382853)
  ·
    refine ⟨1919845067242455229571785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10239173691959761224382853 1919845067242455229571785)
    ·
      refine ⟨1439883800431841422178839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1919845067242455229571785 1439883800431841422178839)
      ·
        refine ⟨2159825700647762133268259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439883800431841422178839 2159825700647762133268259)
        ·
          refine ⟨3239738550971643199902389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159825700647762133268259 3239738550971643199902389)
          ·
            refine ⟨303725489153591549990849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3239738550971643199902389 303725489153591549990849)
            ·
              refine ⟨227794116865193662493137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303725489153591549990849 227794116865193662493137)
              ·
                refine ⟨170845587648895246869853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227794116865193662493137 170845587648895246869853)
                ·
                  refine ⟨64067095368335717576195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170845587648895246869853 64067095368335717576195)
                  ·
                    rfl

theorem cell21_280733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_280733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280733 prefixEnd_280733 := by exact prefixLift 280733
  have htrace : WordTrace (prefixWord ++ tailWord_280733) baseStart_280733 baseEnd_280733 := by
    simpa [prefixWord, tailWord_280733, baseEnd_280733] using wordTrace_append hprefix tailTrace_280733
  have hstable : (prefixWord ++ tailWord_280733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280733).length < 2 ^ (prefixWord ++ tailWord_280733).sum := by decide
  have hdescent : baseEnd_280733 < baseStart_280733 := by decide
  rcases family_descends (prefixWord ++ tailWord_280733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280986 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_280986 : Nat := 118140960795 + 280986 * 2 ^ 59
def prefixEnd_280986 : Nat := 4983230072969 + 3 ^ 40 * 280986 * 2
def baseEnd_280986 : Nat := 64124833415263499859011

theorem tailTrace_280986 : CollatzResearch.WordTrace tailWord_280986 prefixEnd_280986 64124833415263499859011 := by
  unfold tailWord_280986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562100340010796358335703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6832267573362123622228541 2562100340010796358335703)
  ·
    refine ⟨3843150510016194537503555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2562100340010796358335703 3843150510016194537503555)
    ·
      refine ⟨5764725765024291806255333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3843150510016194537503555 5764725765024291806255333)
      ·
        refine ⟨1080886080942054713672875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5764725765024291806255333 1080886080942054713672875)
        ·
          refine ⟨1621329121413082070509313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080886080942054713672875 1621329121413082070509313)
          ·
            refine ⟨1215996841059811552881985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621329121413082070509313 1215996841059811552881985)
            ·
              refine ⟨911997630794858664661489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215996841059811552881985 911997630794858664661489)
              ·
                refine ⟨683998223096143998496117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911997630794858664661489 683998223096143998496117)
                ·
                  refine ⟨64124833415263499859011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 683998223096143998496117 64124833415263499859011)
                  ·
                    rfl

theorem cell21_280986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_280986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280986 prefixEnd_280986 := by exact prefixLift 280986
  have htrace : WordTrace (prefixWord ++ tailWord_280986) baseStart_280986 baseEnd_280986 := by
    simpa [prefixWord, tailWord_280986, baseEnd_280986] using wordTrace_append hprefix tailTrace_280986
  have hstable : (prefixWord ++ tailWord_280986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280986).length < 2 ^ (prefixWord ++ tailWord_280986).sum := by decide
  have hdescent : baseEnd_280986 < baseStart_280986 := by decide
  rcases family_descends (prefixWord ++ tailWord_280986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280989 : List Nat := [1, 4, 2, 1, 4, 2, 2, 5]
def baseStart_280989 : Nat := 118140960795 + 280989 * 2 ^ 59
def prefixEnd_280989 : Nat := 4983230072969 + 3 ^ 40 * 280989 * 2
def baseEnd_280989 : Nat := 21375172685378720436335

theorem tailTrace_280989 : CollatzResearch.WordTrace tailWord_280989 prefixEnd_280989 21375172685378720436335 := by
  unfold tailWord_280989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10248510779032316945702021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6832340519354877963801347 10248510779032316945702021)
  ·
    refine ⟨1921595771068559427319129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10248510779032316945702021 1921595771068559427319129)
    ·
      refine ⟨1441196828301419570489347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1921595771068559427319129 1441196828301419570489347)
      ·
        refine ⟨2161795242452129355734021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441196828301419570489347 2161795242452129355734021)
        ·
          refine ⟨405336607959774254200129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2161795242452129355734021 405336607959774254200129)
          ·
            refine ⟨304002455969830690650097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405336607959774254200129 304002455969830690650097)
            ·
              refine ⟨228001841977373017987573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304002455969830690650097 228001841977373017987573)
              ·
                refine ⟨21375172685378720436335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228001841977373017987573 21375172685378720436335)
                ·
                  rfl

theorem cell21_280989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 5].length) (baseStart_280989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_280989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_280989 prefixEnd_280989 := by exact prefixLift 280989
  have htrace : WordTrace (prefixWord ++ tailWord_280989) baseStart_280989 baseEnd_280989 := by
    simpa [prefixWord, tailWord_280989, baseEnd_280989] using wordTrace_append hprefix tailTrace_280989
  have hstable : (prefixWord ++ tailWord_280989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280989).length < 2 ^ (prefixWord ++ tailWord_280989).sum := by decide
  have hdescent : baseEnd_280989 < baseStart_280989 := by decide
  rcases family_descends (prefixWord ++ tailWord_280989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281031 : List Nat := [1, 1, 4, 1, 1, 5, 2, 6]
def baseStart_281031 : Nat := 118140960795 + 281031 * 2 ^ 59
def prefixEnd_281031 : Nat := 4983230072969 + 3 ^ 40 * 281031 * 2
def baseEnd_281031 : Nat := 21378367676117807202973

theorem tailTrace_281031 : CollatzResearch.WordTrace tailWord_281031 prefixEnd_281031 21378367676117807202973 := by
  unfold tailWord_281031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250042644880158118730947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6833361763253438745820631 10250042644880158118730947)
  ·
    refine ⟨15375063967320237178096421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10250042644880158118730947 15375063967320237178096421)
    ·
      refine ⟨2882824493872544470893079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15375063967320237178096421 2882824493872544470893079)
      ·
        refine ⟨4324236740808816706339619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882824493872544470893079 4324236740808816706339619)
        ·
          refine ⟨6486355111213225059509429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324236740808816706339619 6486355111213225059509429)
          ·
            refine ⟨608095791676239849329009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6486355111213225059509429 608095791676239849329009)
            ·
              refine ⟨456071843757179886996757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608095791676239849329009 456071843757179886996757)
              ·
                refine ⟨21378367676117807202973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456071843757179886996757 21378367676117807202973)
                ·
                  rfl

theorem cell21_281031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_281031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281031 prefixEnd_281031 := by exact prefixLift 281031
  have htrace : WordTrace (prefixWord ++ tailWord_281031) baseStart_281031 baseEnd_281031 := by
    simpa [prefixWord, tailWord_281031, baseEnd_281031] using wordTrace_append hprefix tailTrace_281031
  have hstable : (prefixWord ++ tailWord_281031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281031).length < 2 ^ (prefixWord ++ tailWord_281031).sum := by decide
  have hdescent : baseEnd_281031 < baseStart_281031 := by decide
  rcases family_descends (prefixWord ++ tailWord_281031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281107 : List Nat := [1, 1, 1, 2, 1, 5, 5, 5]
def baseStart_281107 : Nat := 118140960795 + 281107 * 2 ^ 59
def prefixEnd_281107 : Nat := 4983230072969 + 3 ^ 40 * 281107 * 2
def baseEnd_281107 : Nat := 21384149087931392780699

theorem tailTrace_281107 : CollatzResearch.WordTrace tailWord_281107 prefixEnd_281107 21384149087931392780699 := by
  unfold tailWord_281107
  simp only [CollatzResearch.WordTrace]
  refine ⟨10252814592604823098497575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6835209728403215398998383 10252814592604823098497575)
  ·
    refine ⟨15379221888907234647746363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10252814592604823098497575 15379221888907234647746363)
    ·
      refine ⟨23068832833360851971619545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15379221888907234647746363 23068832833360851971619545)
      ·
        refine ⟨17301624625020638978714659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23068832833360851971619545 17301624625020638978714659)
        ·
          refine ⟨25952436937530958468071989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17301624625020638978714659 25952436937530958468071989)
          ·
            refine ⟨2433040962893527356381749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25952436937530958468071989 2433040962893527356381749)
            ·
              refine ⟨228097590271268189660789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2433040962893527356381749 228097590271268189660789)
              ·
                refine ⟨21384149087931392780699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228097590271268189660789 21384149087931392780699)
                ·
                  rfl

theorem cell21_281107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 5].length) (baseStart_281107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281107 prefixEnd_281107 := by exact prefixLift 281107
  have htrace : WordTrace (prefixWord ++ tailWord_281107) baseStart_281107 baseEnd_281107 := by
    simpa [prefixWord, tailWord_281107, baseEnd_281107] using wordTrace_append hprefix tailTrace_281107
  have hstable : (prefixWord ++ tailWord_281107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281107).length < 2 ^ (prefixWord ++ tailWord_281107).sum := by decide
  have hdescent : baseEnd_281107 < baseStart_281107 := by decide
  rcases family_descends (prefixWord ++ tailWord_281107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281121 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_281121 : Nat := 118140960795 + 281121 * 2 ^ 59
def prefixEnd_281121 : Nat := 4983230072969 + 3 ^ 40 * 281121 * 2
def baseEnd_281121 : Nat := 64155642254533265108735

theorem tailTrace_281121 : CollatzResearch.WordTrace tailWord_281121 prefixEnd_281121 64155642254533265108735 := by
  unfold tailWord_281121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253325214554103489507217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6835550143036068993004811 10253325214554103489507217)
  ·
    refine ⟨7689993910915577617130413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10253325214554103489507217 7689993910915577617130413)
    ·
      refine ⟨2883747716593341606423905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7689993910915577617130413 2883747716593341606423905)
      ·
        refine ⟨2162810787445006204817929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883747716593341606423905 2162810787445006204817929)
        ·
          refine ⟨1622108090583754653613447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162810787445006204817929 1622108090583754653613447)
          ·
            refine ⟨2433162135875631980420171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622108090583754653613447 2433162135875631980420171)
            ·
              refine ⟨3649743203813447970630257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433162135875631980420171 3649743203813447970630257)
              ·
                refine ⟨2737307402860085977972693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649743203813447970630257 2737307402860085977972693)
                ·
                  refine ⟨64155642254533265108735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2737307402860085977972693 64155642254533265108735)
                  ·
                    rfl

theorem cell21_281121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_281121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281121 prefixEnd_281121 := by exact prefixLift 281121
  have htrace : WordTrace (prefixWord ++ tailWord_281121) baseStart_281121 baseEnd_281121 := by
    simpa [prefixWord, tailWord_281121, baseEnd_281121] using wordTrace_append hprefix tailTrace_281121
  have hstable : (prefixWord ++ tailWord_281121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281121).length < 2 ^ (prefixWord ++ tailWord_281121).sum := by decide
  have hdescent : baseEnd_281121 < baseStart_281121 := by decide
  rcases family_descends (prefixWord ++ tailWord_281121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281124 : List Nat := [2, 3, 1, 5, 1, 1, 8]
def baseStart_281124 : Nat := 118140960795 + 281124 * 2 ^ 59
def prefixEnd_281124 : Nat := 4983230072969 + 3 ^ 40 * 281124 * 2
def baseEnd_281124 : Nat := 7128480766156214062081

theorem tailTrace_281124 : CollatzResearch.WordTrace tailWord_281124 prefixEnd_281124 7128480766156214062081 := by
  unfold tailWord_281124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126717316771617500933213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6835623089028823334577617 5126717316771617500933213)
  ·
    refine ⟨1922518993789356562849955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5126717316771617500933213 1922518993789356562849955)
    ·
      refine ⟨2883778490684034844274933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922518993789356562849955 2883778490684034844274933)
      ·
        refine ⟨270354233501628266650775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2883778490684034844274933 270354233501628266650775)
        ·
          refine ⟨405531350252442399976163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270354233501628266650775 405531350252442399976163)
          ·
            refine ⟨608297025378663599964245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405531350252442399976163 608297025378663599964245)
            ·
              refine ⟨7128480766156214062081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 608297025378663599964245 7128480766156214062081)
              ·
                rfl

theorem cell21_281124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 8].length) (baseStart_281124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281124 prefixEnd_281124 := by exact prefixLift 281124
  have htrace : WordTrace (prefixWord ++ tailWord_281124) baseStart_281124 baseEnd_281124 := by
    simpa [prefixWord, tailWord_281124, baseEnd_281124] using wordTrace_append hprefix tailTrace_281124
  have hstable : (prefixWord ++ tailWord_281124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281124).length < 2 ^ (prefixWord ++ tailWord_281124).sum := by decide
  have hdescent : baseEnd_281124 < baseStart_281124 := by decide
  rcases family_descends (prefixWord ++ tailWord_281124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281152 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_281152 : Nat := 118140960795 + 281152 * 2 ^ 59
def prefixEnd_281152 : Nat := 4983230072969 + 3 ^ 40 * 281152 * 2
def baseEnd_281152 : Nat := 64162716876884100092005

theorem tailTrace_281152 : CollatzResearch.WordTrace tailWord_281152 prefixEnd_281152 64162716876884100092005 := by
  unfold tailWord_281152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127227938720897891942855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6836303918294530522590473 5127227938720897891942855)
  ·
    refine ⟨7690841908081346837914283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5127227938720897891942855 7690841908081346837914283)
    ·
      refine ⟨11536262862122020256871425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7690841908081346837914283 11536262862122020256871425)
      ·
        refine ⟨8652197146591515192653569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11536262862122020256871425 8652197146591515192653569)
        ·
          refine ⟨6489147859943636394490177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8652197146591515192653569 6489147859943636394490177)
          ·
            refine ⟨4866860894957727295867633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6489147859943636394490177 4866860894957727295867633)
            ·
              refine ⟨3650145671218295471900725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4866860894957727295867633 3650145671218295471900725)
              ·
                refine ⟨342201156676715200490693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3650145671218295471900725 342201156676715200490693)
                ·
                  refine ⟨64162716876884100092005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342201156676715200490693 64162716876884100092005)
                  ·
                    rfl

theorem cell21_281152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_281152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281152 prefixEnd_281152 := by exact prefixLift 281152
  have htrace : WordTrace (prefixWord ++ tailWord_281152) baseStart_281152 baseEnd_281152 := by
    simpa [prefixWord, tailWord_281152, baseEnd_281152] using wordTrace_append hprefix tailTrace_281152
  have hstable : (prefixWord ++ tailWord_281152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281152).length < 2 ^ (prefixWord ++ tailWord_281152).sum := by decide
  have hdescent : baseEnd_281152 < baseStart_281152 := by decide
  rcases family_descends (prefixWord ++ tailWord_281152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281158 : List Nat := [6, 1, 1, 1, 2, 3, 2, 5]
def baseStart_281158 : Nat := 118140960795 + 281158 * 2 ^ 59
def prefixEnd_281158 : Nat := 4983230072969 + 3 ^ 40 * 281158 * 2
def baseEnd_281158 : Nat := 21388028719543140997331

theorem tailTrace_281158 : CollatzResearch.WordTrace tailWord_281158 prefixEnd_281158 21388028719543140997331 := by
  unfold tailWord_281158
  simp only [CollatzResearch.WordTrace]
  refine ⟨320458584856876837768879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6836449810280039205736085 320458584856876837768879)
  ·
    refine ⟨480687877285315256653319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320458584856876837768879 480687877285315256653319)
    ·
      refine ⟨721031815927972884979979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480687877285315256653319 721031815927972884979979)
      ·
        refine ⟨1081547723891959327469969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721031815927972884979979 1081547723891959327469969)
        ·
          refine ⟨811160792918969495602477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081547723891959327469969 811160792918969495602477)
          ·
            refine ⟨304185297344613560850929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 811160792918969495602477 304185297344613560850929)
            ·
              refine ⟨228138973008460170638197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304185297344613560850929 228138973008460170638197)
              ·
                refine ⟨21388028719543140997331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228138973008460170638197 21388028719543140997331)
                ·
                  rfl

theorem cell21_281158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_281158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281158 prefixEnd_281158 := by exact prefixLift 281158
  have htrace : WordTrace (prefixWord ++ tailWord_281158) baseStart_281158 baseEnd_281158 := by
    simpa [prefixWord, tailWord_281158, baseEnd_281158] using wordTrace_append hprefix tailTrace_281158
  have hstable : (prefixWord ++ tailWord_281158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281158).length < 2 ^ (prefixWord ++ tailWord_281158).sum := by decide
  have hdescent : baseEnd_281158 < baseStart_281158 := by decide
  rcases family_descends (prefixWord ++ tailWord_281158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281172 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_281172 : Nat := 118140960795 + 281172 * 2 ^ 59
def prefixEnd_281172 : Nat := 4983230072969 + 3 ^ 40 * 281172 * 2
def baseEnd_281172 : Nat := 64167281149368509758631

theorem tailTrace_281172 : CollatzResearch.WordTrace tailWord_281172 prefixEnd_281172 64167281149368509758631 := by
  unfold tailWord_281172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127592668684669599806885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6836790224912892799742513 5127592668684669599806885)
  ·
    refine ⟨961423625378375549963791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5127592668684669599806885 961423625378375549963791)
    ·
      refine ⟨1442135438067563324945687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961423625378375549963791 1442135438067563324945687)
      ·
        refine ⟨2163203157101344987418531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442135438067563324945687 2163203157101344987418531)
        ·
          refine ⟨3244804735652017481127797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163203157101344987418531 3244804735652017481127797)
          ·
            refine ⟨304200443967376638855731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3244804735652017481127797 304200443967376638855731)
            ·
              refine ⟨456300665951064958283597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304200443967376638855731 456300665951064958283597)
              ·
                refine ⟨171112749731649359356349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456300665951064958283597 171112749731649359356349)
                ·
                  refine ⟨64167281149368509758631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171112749731649359356349 64167281149368509758631)
                  ·
                    rfl

theorem cell21_281172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_281172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281172 prefixEnd_281172 := by exact prefixLift 281172
  have htrace : WordTrace (prefixWord ++ tailWord_281172) baseStart_281172 baseEnd_281172 := by
    simpa [prefixWord, tailWord_281172, baseEnd_281172] using wordTrace_append hprefix tailTrace_281172
  have hstable : (prefixWord ++ tailWord_281172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281172).length < 2 ^ (prefixWord ++ tailWord_281172).sum := by decide
  have hdescent : baseEnd_281172 < baseStart_281172 := by decide
  rcases family_descends (prefixWord ++ tailWord_281172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281211 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_281211 : Nat := 118140960795 + 281211 * 2 ^ 59
def prefixEnd_281211 : Nat := 4983230072969 + 3 ^ 40 * 281211 * 2
def baseEnd_281211 : Nat := 64176181480713108608551

theorem tailTrace_281211 : CollatzResearch.WordTrace tailWord_281211 prefixEnd_281211 64176181480713108608551 := by
  unfold tailWord_281211
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256607784228048860283487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6837738522818699240188991 10256607784228048860283487)
  ·
    refine ⟨15384911676342073290425231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10256607784228048860283487 15384911676342073290425231)
    ·
      refine ⟨23077367514513109935637847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15384911676342073290425231 23077367514513109935637847)
      ·
        refine ⟨34616051271769664903456771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23077367514513109935637847 34616051271769664903456771)
        ·
          refine ⟨51924076907654497355185157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34616051271769664903456771 51924076907654497355185157)
          ·
            refine ⟨9735764420185218254097217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51924076907654497355185157 9735764420185218254097217)
            ·
              refine ⟨7301823315138913690572913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735764420185218254097217 7301823315138913690572913)
              ·
                refine ⟨5476367486354185267929685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7301823315138913690572913 5476367486354185267929685)
                ·
                  refine ⟨64176181480713108608551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5476367486354185267929685 64176181480713108608551)
                  ·
                    rfl

theorem cell21_281211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_281211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281211 prefixEnd_281211 := by exact prefixLift 281211
  have htrace : WordTrace (prefixWord ++ tailWord_281211) baseStart_281211 baseEnd_281211 := by
    simpa [prefixWord, tailWord_281211, baseEnd_281211] using wordTrace_append hprefix tailTrace_281211
  have hstable : (prefixWord ++ tailWord_281211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281211).length < 2 ^ (prefixWord ++ tailWord_281211).sum := by decide
  have hdescent : baseEnd_281211 < baseStart_281211 := by decide
  rcases family_descends (prefixWord ++ tailWord_281211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281262 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_281262 : Nat := 118140960795 + 281262 * 2 ^ 59
def prefixEnd_281262 : Nat := 4983230072969 + 3 ^ 40 * 281262 * 2
def baseEnd_281262 : Nat := 64187820375548353258447

theorem tailTrace_281262 : CollatzResearch.WordTrace tailWord_281262 prefixEnd_281262 64187820375548353258447 := by
  unfold tailWord_281262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282308488380410571298755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6838978604695523046926693 1282308488380410571298755)
  ·
    refine ⟨1923462732570615856948133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1282308488380410571298755 1923462732570615856948133)
    ·
      refine ⟨360649262356990473177775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1923462732570615856948133 360649262356990473177775)
      ·
        refine ⟨540973893535485709766663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360649262356990473177775 540973893535485709766663)
        ·
          refine ⟨811460840303228564649995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540973893535485709766663 811460840303228564649995)
          ·
            refine ⟨1217191260454842846974993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811460840303228564649995 1217191260454842846974993)
            ·
              refine ⟨912893445341132135231245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217191260454842846974993 912893445341132135231245)
              ·
                refine ⟨342335042002924550711717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912893445341132135231245 342335042002924550711717)
                ·
                  refine ⟨64187820375548353258447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342335042002924550711717 64187820375548353258447)
                  ·
                    rfl

theorem cell21_281262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_281262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281262 prefixEnd_281262 := by exact prefixLift 281262
  have htrace : WordTrace (prefixWord ++ tailWord_281262) baseStart_281262 baseEnd_281262 := by
    simpa [prefixWord, tailWord_281262, baseEnd_281262] using wordTrace_append hprefix tailTrace_281262
  have hstable : (prefixWord ++ tailWord_281262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281262).length < 2 ^ (prefixWord ++ tailWord_281262).sum := by decide
  have hdescent : baseEnd_281262 < baseStart_281262 := by decide
  rcases family_descends (prefixWord ++ tailWord_281262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281304 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_281304 : Nat := 118140960795 + 281304 * 2 ^ 59
def prefixEnd_281304 : Nat := 4983230072969 + 3 ^ 40 * 281304 * 2
def baseEnd_281304 : Nat := 64197405347765613558361

theorem tailTrace_281304 : CollatzResearch.WordTrace tailWord_281304 prefixEnd_281304 64197405347765613558361 := by
  unfold tailWord_281304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129999886445562871709483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6839999848594083828945977 5129999886445562871709483)
  ·
    refine ⟨7694999829668344307564225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129999886445562871709483 7694999829668344307564225)
    ·
      refine ⟨5771249872251258230673169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7694999829668344307564225 5771249872251258230673169)
      ·
        refine ⟨4328437404188443673004877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5771249872251258230673169 4328437404188443673004877)
        ·
          refine ⟨1623164026570666377376829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4328437404188443673004877 1623164026570666377376829)
          ·
            refine ⟨608686509963999891516311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1623164026570666377376829 608686509963999891516311)
            ·
              refine ⟨913029764945999837274467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608686509963999891516311 913029764945999837274467)
              ·
                refine ⟨1369544647418999755911701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913029764945999837274467 1369544647418999755911701)
                ·
                  refine ⟨64197405347765613558361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1369544647418999755911701 64197405347765613558361)
                  ·
                    rfl

theorem cell21_281304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_281304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281304 prefixEnd_281304 := by exact prefixLift 281304
  have htrace : WordTrace (prefixWord ++ tailWord_281304) baseStart_281304 baseEnd_281304 := by
    simpa [prefixWord, tailWord_281304, baseEnd_281304] using wordTrace_append hprefix tailTrace_281304
  have hstable : (prefixWord ++ tailWord_281304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281304).length < 2 ^ (prefixWord ++ tailWord_281304).sum := by decide
  have hdescent : baseEnd_281304 < baseStart_281304 := by decide
  rcases family_descends (prefixWord ++ tailWord_281304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281363 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_281363 : Nat := 118140960795 + 281363 * 2 ^ 59
def prefixEnd_281363 : Nat := 4983230072969 + 3 ^ 40 * 281363 * 2
def baseEnd_281363 : Nat := 64210869951594622074907

theorem tailTrace_281363 : CollatzResearch.WordTrace tailWord_281363 prefixEnd_281363 64210869951594622074907 := by
  unfold tailWord_281363
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262151679677378819816743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6841434453118252546544495 10262151679677378819816743)
  ·
    refine ⟨15393227519516068229725115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10262151679677378819816743 15393227519516068229725115)
    ·
      refine ⟨23089841279274102344587673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15393227519516068229725115 23089841279274102344587673)
      ·
        refine ⟨17317380959455576758440755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23089841279274102344587673 17317380959455576758440755)
        ·
          refine ⟨25976071439183365137661133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17317380959455576758440755 25976071439183365137661133)
          ·
            refine ⟨9741026789693761926622925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25976071439183365137661133 9741026789693761926622925)
            ·
              refine ⟨3652885046135160722483597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9741026789693761926622925 3652885046135160722483597)
              ·
                refine ⟨1369831892300685270931349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3652885046135160722483597 1369831892300685270931349)
                ·
                  refine ⟨64210869951594622074907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1369831892300685270931349 64210869951594622074907)
                  ·
                    rfl

theorem cell21_281363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_281363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281363 prefixEnd_281363 := by exact prefixLift 281363
  have htrace : WordTrace (prefixWord ++ tailWord_281363) baseStart_281363 baseEnd_281363 := by
    simpa [prefixWord, tailWord_281363, baseEnd_281363] using wordTrace_append hprefix tailTrace_281363
  have hstable : (prefixWord ++ tailWord_281363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281363).length < 2 ^ (prefixWord ++ tailWord_281363).sum := by decide
  have hdescent : baseEnd_281363 < baseStart_281363 := by decide
  rcases family_descends (prefixWord ++ tailWord_281363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281394 : List Nat := [3, 2, 1, 1, 3, 1, 1, 9]
def baseStart_281394 : Nat := 118140960795 + 281394 * 2 ^ 59
def prefixEnd_281394 : Nat := 4983230072969 + 3 ^ 40 * 281394 * 2
def baseEnd_281394 : Nat := 21405981524648485686059

theorem tailTrace_281394 : CollatzResearch.WordTrace tailWord_281394 prefixEnd_281394 21405981524648485686059 := by
  unfold tailWord_281394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565820585641267778548809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6842188228376714076130157 2565820585641267778548809)
  ·
    refine ⟨1924365439230950833911607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2565820585641267778548809 1924365439230950833911607)
    ·
      refine ⟨2886548158846426250867411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1924365439230950833911607 2886548158846426250867411)
      ·
        refine ⟨4329822238269639376301117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886548158846426250867411 4329822238269639376301117)
        ·
          refine ⟨1623683339351114766112919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4329822238269639376301117 1623683339351114766112919)
          ·
            refine ⟨2435525009026672149169379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623683339351114766112919 2435525009026672149169379)
            ·
              refine ⟨3653287513540008223754069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435525009026672149169379 3653287513540008223754069)
              ·
                refine ⟨21405981524648485686059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3653287513540008223754069 21405981524648485686059)
                ·
                  rfl

theorem cell21_281394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_281394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281394 prefixEnd_281394 := by exact prefixLift 281394
  have htrace : WordTrace (prefixWord ++ tailWord_281394) baseStart_281394 baseEnd_281394 := by
    simpa [prefixWord, tailWord_281394, baseEnd_281394] using wordTrace_append hprefix tailTrace_281394
  have hstable : (prefixWord ++ tailWord_281394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281394).length < 2 ^ (prefixWord ++ tailWord_281394).sum := by decide
  have hdescent : baseEnd_281394 < baseStart_281394 := by decide
  rcases family_descends (prefixWord ++ tailWord_281394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281428 : List Nat := [2, 4, 1, 1, 4, 2, 1, 6]
def baseStart_281428 : Nat := 118140960795 + 281428 * 2 ^ 59
def prefixEnd_281428 : Nat := 4983230072969 + 3 ^ 40 * 281428 * 2
def baseEnd_281428 : Nat := 21408567945722984497147

theorem tailTrace_281428 : CollatzResearch.WordTrace tailWord_281428 prefixEnd_281428 21408567945722984497147 := by
  unfold tailWord_281428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132261212220947460466469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6843014949627929947288625 5132261212220947460466469)
  ·
    refine ⟨962298977291427648837463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5132261212220947460466469 962298977291427648837463)
    ·
      refine ⟨1443448465937141473256195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962298977291427648837463 1443448465937141473256195)
      ·
        refine ⟨2165172698905712209884293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443448465937141473256195 2165172698905712209884293)
        ·
          refine ⟨405969881044821039353305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2165172698905712209884293 405969881044821039353305)
          ·
            refine ⟨304477410783615779514979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405969881044821039353305 304477410783615779514979)
            ·
              refine ⟨456716116175423669272469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304477410783615779514979 456716116175423669272469)
              ·
                refine ⟨21408567945722984497147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456716116175423669272469 21408567945722984497147)
                ·
                  rfl

theorem cell21_281428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_281428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281428 prefixEnd_281428 := by exact prefixLift 281428
  have htrace : WordTrace (prefixWord ++ tailWord_281428) baseStart_281428 baseEnd_281428 := by
    simpa [prefixWord, tailWord_281428, baseEnd_281428] using wordTrace_append hprefix tailTrace_281428
  have hstable : (prefixWord ++ tailWord_281428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281428).length < 2 ^ (prefixWord ++ tailWord_281428).sum := by decide
  have hdescent : baseEnd_281428 < baseStart_281428 := by decide
  rcases family_descends (prefixWord ++ tailWord_281428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281501 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_281501 : Nat := 118140960795 + 281501 * 2 ^ 59
def prefixEnd_281501 : Nat := 4983230072969 + 3 ^ 40 * 281501 * 2
def baseEnd_281501 : Nat := 64242363431737048774625

theorem tailTrace_281501 : CollatzResearch.WordTrace tailWord_281501 prefixEnd_281501 64242363431737048774625 := by
  unfold tailWord_281501
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267184953177428388340357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6844789968784952258893571 10267184953177428388340357)
  ·
    refine ⟨1925097178720767822813817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10267184953177428388340357 1925097178720767822813817)
    ·
      refine ⟨1443822884040575867110363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1925097178720767822813817 1443822884040575867110363)
      ·
        refine ⟨2165734326060863800665545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443822884040575867110363 2165734326060863800665545)
        ·
          refine ⟨1624300744545647850499159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165734326060863800665545 1624300744545647850499159)
          ·
            refine ⟨2436451116818471775748739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624300744545647850499159 2436451116818471775748739)
            ·
              refine ⟨3654676675227707663623109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436451116818471775748739 3654676675227707663623109)
              ·
                refine ⟨685251876605195186929333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3654676675227707663623109 685251876605195186929333)
                ·
                  refine ⟨64242363431737048774625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 685251876605195186929333 64242363431737048774625)
                  ·
                    rfl

theorem cell21_281501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_281501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281501 prefixEnd_281501 := by exact prefixLift 281501
  have htrace : WordTrace (prefixWord ++ tailWord_281501) baseStart_281501 baseEnd_281501 := by
    simpa [prefixWord, tailWord_281501, baseEnd_281501] using wordTrace_append hprefix tailTrace_281501
  have hstable : (prefixWord ++ tailWord_281501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281501).length < 2 ^ (prefixWord ++ tailWord_281501).sum := by decide
  have hdescent : baseEnd_281501 < baseStart_281501 := by decide
  rcases family_descends (prefixWord ++ tailWord_281501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281586 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_281586 : Nat := 118140960795 + 281586 * 2 ^ 59
def prefixEnd_281586 : Nat := 4983230072969 + 3 ^ 40 * 281586 * 2
def baseEnd_281586 : Nat := 64261761589795789857785

theorem tailTrace_281586 : CollatzResearch.WordTrace tailWord_281586 prefixEnd_281586 64261761589795789857785 := by
  unfold tailWord_281586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567571289467371976296153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6846856771912991936789741 2567571289467371976296153)
  ·
    refine ⟨1925678467100528982222115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2567571289467371976296153 1925678467100528982222115)
    ·
      refine ⟨2888517700650793473333173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925678467100528982222115 2888517700650793473333173)
      ·
        refine ⟨270798534436011888124985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2888517700650793473333173 270798534436011888124985)
        ·
          refine ⟨203098900827008916093739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270798534436011888124985 203098900827008916093739)
          ·
            refine ⟨304648351240513374140609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203098900827008916093739 304648351240513374140609)
            ·
              refine ⟨228486263430385030605457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304648351240513374140609 228486263430385030605457)
              ·
                refine ⟨171364697572788772954093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228486263430385030605457 171364697572788772954093)
                ·
                  refine ⟨64261761589795789857785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171364697572788772954093 64261761589795789857785)
                  ·
                    rfl

theorem cell21_281586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_281586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281586 prefixEnd_281586 := by exact prefixLift 281586
  have htrace : WordTrace (prefixWord ++ tailWord_281586) baseStart_281586 baseEnd_281586 := by
    simpa [prefixWord, tailWord_281586, baseEnd_281586] using wordTrace_append hprefix tailTrace_281586
  have hstable : (prefixWord ++ tailWord_281586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281586).length < 2 ^ (prefixWord ++ tailWord_281586).sum := by decide
  have hdescent : baseEnd_281586 < baseStart_281586 := by decide
  rcases family_descends (prefixWord ++ tailWord_281586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281608 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_281608 : Nat := 118140960795 + 281608 * 2 ^ 59
def prefixEnd_281608 : Nat := 4983230072969 + 3 ^ 40 * 281608 * 2
def baseEnd_281608 : Nat := 64266782289528640491073

theorem tailTrace_281608 : CollatzResearch.WordTrace tailWord_281608 prefixEnd_281608 64266782289528640491073 := by
  unfold tailWord_281608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135543781894892831242739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6847391709193190441656985 5135543781894892831242739)
  ·
    refine ⟨7703315672842339246864109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5135543781894892831242739 7703315672842339246864109)
    ·
      refine ⟨2888743377315877217574041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7703315672842339246864109 2888743377315877217574041)
      ·
        refine ⟨2166557532986907913180531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2888743377315877217574041 2166557532986907913180531)
        ·
          refine ⟨3249836299480361869770797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166557532986907913180531 3249836299480361869770797)
          ·
            refine ⟨1218688612305135701164049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3249836299480361869770797 1218688612305135701164049)
            ·
              refine ⟨914016459228851775873037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218688612305135701164049 914016459228851775873037)
              ·
                refine ⟨342756172210819415952389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914016459228851775873037 342756172210819415952389)
                ·
                  refine ⟨64266782289528640491073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342756172210819415952389 64266782289528640491073)
                  ·
                    rfl

theorem cell21_281608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_281608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281608 prefixEnd_281608 := by exact prefixLift 281608
  have htrace : WordTrace (prefixWord ++ tailWord_281608) baseStart_281608 baseEnd_281608 := by
    simpa [prefixWord, tailWord_281608, baseEnd_281608] using wordTrace_append hprefix tailTrace_281608
  have hstable : (prefixWord ++ tailWord_281608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281608).length < 2 ^ (prefixWord ++ tailWord_281608).sum := by decide
  have hdescent : baseEnd_281608 < baseStart_281608 := by decide
  rcases family_descends (prefixWord ++ tailWord_281608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281639 : List Nat := [1, 1, 7, 1, 1, 2, 8]
def baseStart_281639 : Nat := 118140960795 + 281639 * 2 ^ 59
def prefixEnd_281639 : Nat := 4983230072969 + 3 ^ 40 * 281639 * 2
def baseEnd_281639 : Nat := 7141539656875497274927

theorem tailTrace_281639 : CollatzResearch.WordTrace tailWord_281639 prefixEnd_281639 7141539656875497274927 := by
  unfold tailWord_281639
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272218226677477956863971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6848145484451651971242647 10272218226677477956863971)
  ·
    refine ⟨15408327340016216935295957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10272218226677477956863971 15408327340016216935295957)
    ·
      refine ⟨361132672031630084420999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15408327340016216935295957 361132672031630084420999)
      ·
        refine ⟨541699008047445126631499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361132672031630084420999 541699008047445126631499)
        ·
          refine ⟨812548512071167689947249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541699008047445126631499 812548512071167689947249)
          ·
            refine ⟨609411384053375767460437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812548512071167689947249 609411384053375767460437)
            ·
              refine ⟨7141539656875497274927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 609411384053375767460437 7141539656875497274927)
              ·
                rfl

theorem cell21_281639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 8].length) (baseStart_281639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281639 prefixEnd_281639 := by exact prefixLift 281639
  have htrace : WordTrace (prefixWord ++ tailWord_281639) baseStart_281639 baseEnd_281639 := by
    simpa [prefixWord, tailWord_281639, baseEnd_281639] using wordTrace_append hprefix tailTrace_281639
  have hstable : (prefixWord ++ tailWord_281639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281639).length < 2 ^ (prefixWord ++ tailWord_281639).sum := by decide
  have hdescent : baseEnd_281639 < baseStart_281639 := by decide
  rcases family_descends (prefixWord ++ tailWord_281639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281642 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_281642 : Nat := 118140960795 + 281642 * 2 ^ 59
def prefixEnd_281642 : Nat := 4983230072969 + 3 ^ 40 * 281642 * 2
def baseEnd_281642 : Nat := 64274541552752136924337

theorem tailTrace_281642 : CollatzResearch.WordTrace tailWord_281642 prefixEnd_281642 64274541552752136924337 := by
  unfold tailWord_281642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568081911416652367305795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6848218430444406312815453 2568081911416652367305795)
  ·
    refine ⟨3852122867124978550958693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568081911416652367305795 3852122867124978550958693)
    ·
      refine ⟨722273037585933478304755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3852122867124978550958693 722273037585933478304755)
      ·
        refine ⟨1083409556378900217457133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722273037585933478304755 1083409556378900217457133)
        ·
          refine ⟨406278583642087581546425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1083409556378900217457133 406278583642087581546425)
          ·
            refine ⟨304708937731565686159819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406278583642087581546425 304708937731565686159819)
            ·
              refine ⟨457063406597348529239729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304708937731565686159819 457063406597348529239729)
              ·
                refine ⟨342797554948011396929797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457063406597348529239729 342797554948011396929797)
                ·
                  refine ⟨64274541552752136924337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342797554948011396929797 64274541552752136924337)
                  ·
                    rfl

theorem cell21_281642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_281642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281642 prefixEnd_281642 := by exact prefixLift 281642
  have htrace : WordTrace (prefixWord ++ tailWord_281642) baseStart_281642 baseEnd_281642 := by
    simpa [prefixWord, tailWord_281642, baseEnd_281642] using wordTrace_append hprefix tailTrace_281642
  have hstable : (prefixWord ++ tailWord_281642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281642).length < 2 ^ (prefixWord ++ tailWord_281642).sum := by decide
  have hdescent : baseEnd_281642 < baseStart_281642 := by decide
  rcases family_descends (prefixWord ++ tailWord_281642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281704 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_281704 : Nat := 118140960795 + 281704 * 2 ^ 59
def prefixEnd_281704 : Nat := 4983230072969 + 3 ^ 40 * 281704 * 2
def baseEnd_281704 : Nat := 64288690797453806890877

theorem tailTrace_281704 : CollatzResearch.WordTrace tailWord_281704 prefixEnd_281704 64288690797453806890877 := by
  unfold tailWord_281704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137294485720997028990083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6849725980961329371986777 5137294485720997028990083)
  ·
    refine ⟨7705941728581495543485125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137294485720997028990083 7705941728581495543485125)
    ·
      refine ⟨1444864074109030414403461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7705941728581495543485125 1444864074109030414403461)
      ·
        refine ⟨270912013895443202700649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1444864074109030414403461 270912013895443202700649)
        ·
          refine ⟨203184010421582402025487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270912013895443202700649 203184010421582402025487)
          ·
            refine ⟨304776015632373603038231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203184010421582402025487 304776015632373603038231)
            ·
              refine ⟨457164023448560404557347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304776015632373603038231 457164023448560404557347)
              ·
                refine ⟨685746035172840606836021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457164023448560404557347 685746035172840606836021)
                ·
                  refine ⟨64288690797453806890877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 685746035172840606836021 64288690797453806890877)
                  ·
                    rfl

theorem cell21_281704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_281704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281704 prefixEnd_281704 := by exact prefixLift 281704
  have htrace : WordTrace (prefixWord ++ tailWord_281704) baseStart_281704 baseEnd_281704 := by
    simpa [prefixWord, tailWord_281704, baseEnd_281704] using wordTrace_append hprefix tailTrace_281704
  have hstable : (prefixWord ++ tailWord_281704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281704).length < 2 ^ (prefixWord ++ tailWord_281704).sum := by decide
  have hdescent : baseEnd_281704 < baseStart_281704 := by decide
  rcases family_descends (prefixWord ++ tailWord_281704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281760 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_281760 : Nat := 118140960795 + 281760 * 2 ^ 59
def prefixEnd_281760 : Nat := 4983230072969 + 3 ^ 40 * 281760 * 2
def baseEnd_281760 : Nat := 64301470760410153957429

theorem tailTrace_281760 : CollatzResearch.WordTrace tailWord_281760 prefixEnd_281760 64301470760410153957429 := by
  unfold tailWord_281760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138315729619557811009367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6851087639492743748012489 5138315729619557811009367)
  ·
    refine ⟨7707473594429336716514051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5138315729619557811009367 7707473594429336716514051)
    ·
      refine ⟨11561210391644005074771077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7707473594429336716514051 11561210391644005074771077)
      ·
        refine ⟨2167726948433250951519577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11561210391644005074771077 2167726948433250951519577)
        ·
          refine ⟨1625795211324938213639683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167726948433250951519577 1625795211324938213639683)
          ·
            refine ⟨2438692816987407320459525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625795211324938213639683 2438692816987407320459525)
            ·
              refine ⟨457254903185138872586161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2438692816987407320459525 457254903185138872586161)
              ·
                refine ⟨342941177388854154439621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457254903185138872586161 342941177388854154439621)
                ·
                  refine ⟨64301470760410153957429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342941177388854154439621 64301470760410153957429)
                  ·
                    rfl

theorem cell21_281760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_281760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281760 prefixEnd_281760 := by exact prefixLift 281760
  have htrace : WordTrace (prefixWord ++ tailWord_281760) baseStart_281760 baseEnd_281760 := by
    simpa [prefixWord, tailWord_281760, baseEnd_281760] using wordTrace_append hprefix tailTrace_281760
  have hstable : (prefixWord ++ tailWord_281760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281760).length < 2 ^ (prefixWord ++ tailWord_281760).sum := by decide
  have hdescent : baseEnd_281760 < baseStart_281760 := by decide
  rcases family_descends (prefixWord ++ tailWord_281760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281988 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_281988 : Nat := 118140960795 + 281988 * 2 ^ 59
def prefixEnd_281988 : Nat := 4983230072969 + 3 ^ 40 * 281988 * 2
def baseEnd_281988 : Nat := 64353503466732424156963

theorem tailTrace_281988 : CollatzResearch.WordTrace tailWord_281988 prefixEnd_281988 64353503466732424156963 := by
  unfold tailWord_281988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142473651206555280659309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6856631534942073707545745 5142473651206555280659309)
  ·
    refine ⟨1928427619202458230247241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5142473651206555280659309 1928427619202458230247241)
    ·
      refine ⟨1446320714401843672685431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1928427619202458230247241 1446320714401843672685431)
      ·
        refine ⟨2169481071602765509028147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446320714401843672685431 2169481071602765509028147)
        ·
          refine ⟨3254221607404148263542221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169481071602765509028147 3254221607404148263542221)
          ·
            refine ⟨1220333102776555598828333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3254221607404148263542221 1220333102776555598828333)
            ·
              refine ⟨457624913541208349560625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220333102776555598828333 457624913541208349560625)
              ·
                refine ⟨343218685155906262170469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457624913541208349560625 343218685155906262170469)
                ·
                  refine ⟨64353503466732424156963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343218685155906262170469 64353503466732424156963)
                  ·
                    rfl

theorem cell21_281988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_281988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_281988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_281988 prefixEnd_281988 := by exact prefixLift 281988
  have htrace : WordTrace (prefixWord ++ tailWord_281988) baseStart_281988 baseEnd_281988 := by
    simpa [prefixWord, tailWord_281988, baseEnd_281988] using wordTrace_append hprefix tailTrace_281988
  have hstable : (prefixWord ++ tailWord_281988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281988).length < 2 ^ (prefixWord ++ tailWord_281988).sum := by decide
  have hdescent : baseEnd_281988 < baseStart_281988 := by decide
  rcases family_descends (prefixWord ++ tailWord_281988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282016 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_282016 : Nat := 118140960795 + 282016 * 2 ^ 59
def prefixEnd_282016 : Nat := 4983230072969 + 3 ^ 40 * 282016 * 2
def baseEnd_282016 : Nat := 64359893448210597690239

theorem tailTrace_282016 : CollatzResearch.WordTrace tailWord_282016 prefixEnd_282016 64359893448210597690239 := by
  unfold tailWord_282016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142984273155835671668951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6857312364207780895558601 5142984273155835671668951)
  ·
    refine ⟨7714476409733753507503427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5142984273155835671668951 7714476409733753507503427)
    ·
      refine ⟨11571714614600630261255141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7714476409733753507503427 11571714614600630261255141)
      ·
        refine ⟨2169696490237618173985339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11571714614600630261255141 2169696490237618173985339)
        ·
          refine ⟨3254544735356427260978009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169696490237618173985339 3254544735356427260978009)
          ·
            refine ⟨2440908551517320445733507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3254544735356427260978009 2440908551517320445733507)
            ·
              refine ⟨3661362827275980668600261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440908551517320445733507 3661362827275980668600261)
              ·
                refine ⟨686505530114246375362549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3661362827275980668600261 686505530114246375362549)
                ·
                  refine ⟨64359893448210597690239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 686505530114246375362549 64359893448210597690239)
                  ·
                    rfl

theorem cell21_282016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_282016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282016 prefixEnd_282016 := by exact prefixLift 282016
  have htrace : WordTrace (prefixWord ++ tailWord_282016) baseStart_282016 baseEnd_282016 := by
    simpa [prefixWord, tailWord_282016, baseEnd_282016] using wordTrace_append hprefix tailTrace_282016
  have hstable : (prefixWord ++ tailWord_282016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282016).length < 2 ^ (prefixWord ++ tailWord_282016).sum := by decide
  have hdescent : baseEnd_282016 < baseStart_282016 := by decide
  rcases family_descends (prefixWord ++ tailWord_282016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282168 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_282168 : Nat := 118140960795 + 282168 * 2 ^ 59
def prefixEnd_282168 : Nat := 4983230072969 + 3 ^ 40 * 282168 * 2
def baseEnd_282168 : Nat := 64394581919092111156595

theorem tailTrace_282168 : CollatzResearch.WordTrace tailWord_282168 prefixEnd_282168 64394581919092111156595 := by
  unfold tailWord_282168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145756220880500651435579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6861008294507334201914105 5145756220880500651435579)
  ·
    refine ⟨7718634331320750977153369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5145756220880500651435579 7718634331320750977153369)
    ·
      refine ⟨5788975748490563232865027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7718634331320750977153369 5788975748490563232865027)
      ·
        refine ⟨8683463622735844849297541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5788975748490563232865027 8683463622735844849297541)
        ·
          refine ⟨1628149429262970909243289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8683463622735844849297541 1628149429262970909243289)
          ·
            refine ⟨1221112071947228181932467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628149429262970909243289 1221112071947228181932467)
            ·
              refine ⟨1831668107920842272898701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221112071947228181932467 1831668107920842272898701)
              ·
                refine ⟨686875540470315852337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1831668107920842272898701 686875540470315852337013)
                ·
                  refine ⟨64394581919092111156595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 686875540470315852337013 64394581919092111156595)
                  ·
                    rfl

theorem cell21_282168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_282168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282168 prefixEnd_282168 := by exact prefixLift 282168
  have htrace : WordTrace (prefixWord ++ tailWord_282168) baseStart_282168 baseEnd_282168 := by
    simpa [prefixWord, tailWord_282168, baseEnd_282168] using wordTrace_append hprefix tailTrace_282168
  have hstable : (prefixWord ++ tailWord_282168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282168).length < 2 ^ (prefixWord ++ tailWord_282168).sum := by decide
  have hdescent : baseEnd_282168 < baseStart_282168 := by decide
  rcases family_descends (prefixWord ++ tailWord_282168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282213 : List Nat := [1, 3, 1, 3, 3, 1, 9]
def baseStart_282213 : Nat := 118140960795 + 282213 * 2 ^ 59
def prefixEnd_282213 : Nat := 4983230072969 + 3 ^ 40 * 282213 * 2
def baseEnd_282213 : Nat := 7156094614686892545167

theorem tailTrace_282213 : CollatzResearch.WordTrace tailWord_282213 prefixEnd_282213 7156094614686892545167 := by
  unfold tailWord_282213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293153726597973988259293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6862102484398649325506195 10293153726597973988259293)
  ·
    refine ⟨3859932647474240245597235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10293153726597973988259293 3859932647474240245597235)
    ·
      refine ⟨5789898971211360368395853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859932647474240245597235 5789898971211360368395853)
      ·
        refine ⟨2171212114204260138148445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5789898971211360368395853 2171212114204260138148445)
        ·
          refine ⟨814204542826597551805667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2171212114204260138148445 814204542826597551805667)
          ·
            refine ⟨1221306814239896327708501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814204542826597551805667 1221306814239896327708501)
            ·
              refine ⟨7156094614686892545167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1221306814239896327708501 7156094614686892545167)
              ·
                rfl

theorem cell21_282213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 9].length) (baseStart_282213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282213 prefixEnd_282213 := by exact prefixLift 282213
  have htrace : WordTrace (prefixWord ++ tailWord_282213) baseStart_282213 baseEnd_282213 := by
    simpa [prefixWord, tailWord_282213, baseEnd_282213] using wordTrace_append hprefix tailTrace_282213
  have hstable : (prefixWord ++ tailWord_282213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282213).length < 2 ^ (prefixWord ++ tailWord_282213).sum := by decide
  have hdescent : baseEnd_282213 < baseStart_282213 := by decide
  rcases family_descends (prefixWord ++ tailWord_282213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282230 : List Nat := [5, 1, 1, 2, 2, 1, 1, 8]
def baseStart_282230 : Nat := 118140960795 + 282230 * 2 ^ 59
def prefixEnd_282230 : Nat := 4983230072969 + 3 ^ 40 * 282230 * 2
def baseEnd_282230 : Nat := 21469577054597927041045

theorem tailTrace_282230 : CollatzResearch.WordTrace tailWord_282230 prefixEnd_282230 21469577054597927041045 := by
  unfold tailWord_282230
  simp only [CollatzResearch.WordTrace]
  refine ⟨643360860471024118226759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6862515845024257261085429 643360860471024118226759)
  ·
    refine ⟨965041290706536177340139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 643360860471024118226759 965041290706536177340139)
    ·
      refine ⟨1447561936059804266010209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965041290706536177340139 1447561936059804266010209)
      ·
        refine ⟨1085671452044853199507657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447561936059804266010209 1085671452044853199507657)
        ·
          refine ⟨814253589033639899630743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085671452044853199507657 814253589033639899630743)
          ·
            refine ⟨1221380383550459849446115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814253589033639899630743 1221380383550459849446115)
            ·
              refine ⟨1832070575325689774169173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221380383550459849446115 1832070575325689774169173)
              ·
                refine ⟨21469577054597927041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1832070575325689774169173 21469577054597927041045)
                ·
                  rfl

theorem cell21_282230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_282230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282230 prefixEnd_282230 := by exact prefixLift 282230
  have htrace : WordTrace (prefixWord ++ tailWord_282230) baseStart_282230 baseEnd_282230 := by
    simpa [prefixWord, tailWord_282230, baseEnd_282230] using wordTrace_append hprefix tailTrace_282230
  have hstable : (prefixWord ++ tailWord_282230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282230).length < 2 ^ (prefixWord ++ tailWord_282230).sum := by decide
  have hdescent : baseEnd_282230 < baseStart_282230 := by decide
  rcases family_descends (prefixWord ++ tailWord_282230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282275 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_282275 : Nat := 118140960795 + 282275 * 2 ^ 59
def prefixEnd_282275 : Nat := 4983230072969 + 3 ^ 40 * 282275 * 2
def baseEnd_282275 : Nat := 64419000776883702873043

theorem tailTrace_282275 : CollatzResearch.WordTrace tailWord_282275 prefixEnd_282275 64419000776883702873043 := by
  unfold tailWord_282275
  simp only [CollatzResearch.WordTrace]
  refine ⟨10295415052373358577016279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6863610034915572384677519 10295415052373358577016279)
  ·
    refine ⟨15443122578560037865524419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10295415052373358577016279 15443122578560037865524419)
    ·
      refine ⟨23164683867840056798286629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15443122578560037865524419 23164683867840056798286629)
      ·
        refine ⟨4343378225220010649678743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23164683867840056798286629 4343378225220010649678743)
        ·
          refine ⟨6515067337830015974518115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343378225220010649678743 6515067337830015974518115)
          ·
            refine ⟨9772601006745023961777173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515067337830015974518115 9772601006745023961777173)
            ·
              refine ⟨458090672191172998208305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9772601006745023961777173 458090672191172998208305)
              ·
                refine ⟨343568004143379748656229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458090672191172998208305 343568004143379748656229)
                ·
                  refine ⟨64419000776883702873043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343568004143379748656229 64419000776883702873043)
                  ·
                    rfl

theorem cell21_282275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_282275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282275 prefixEnd_282275 := by exact prefixLift 282275
  have htrace : WordTrace (prefixWord ++ tailWord_282275) baseStart_282275 baseEnd_282275 := by
    simpa [prefixWord, tailWord_282275, baseEnd_282275] using wordTrace_append hprefix tailTrace_282275
  have hstable : (prefixWord ++ tailWord_282275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282275).length < 2 ^ (prefixWord ++ tailWord_282275).sum := by decide
  have hdescent : baseEnd_282275 < baseStart_282275 := by decide
  rcases family_descends (prefixWord ++ tailWord_282275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282337 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_282337 : Nat := 118140960795 + 282337 * 2 ^ 59
def prefixEnd_282337 : Nat := 4983230072969 + 3 ^ 40 * 282337 * 2
def baseEnd_282337 : Nat := 64433150021585372839583

theorem tailTrace_282337 : CollatzResearch.WordTrace tailWord_282337 prefixEnd_282337 64433150021585372839583 := by
  unfold tailWord_282337
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297676378148743165773265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6865117585432495443848843 10297676378148743165773265)
  ·
    refine ⟨7723257283611557374329949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10297676378148743165773265 7723257283611557374329949)
    ·
      refine ⟨2896221481354334015373731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7723257283611557374329949 2896221481354334015373731)
      ·
        refine ⟨4344332222031501023060597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2896221481354334015373731 4344332222031501023060597)
        ·
          refine ⟨407281145815453220911931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4344332222031501023060597 407281145815453220911931)
          ·
            refine ⟨610921718723179831367897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407281145815453220911931 610921718723179831367897)
            ·
              refine ⟨458191289042384873525923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610921718723179831367897 458191289042384873525923)
              ·
                refine ⟨687286933563577310288885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458191289042384873525923 687286933563577310288885)
                ·
                  refine ⟨64433150021585372839583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 687286933563577310288885 64433150021585372839583)
                  ·
                    rfl

theorem cell21_282337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_282337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282337 prefixEnd_282337 := by exact prefixLift 282337
  have htrace : WordTrace (prefixWord ++ tailWord_282337) baseStart_282337 baseEnd_282337 := by
    simpa [prefixWord, tailWord_282337, baseEnd_282337] using wordTrace_append hprefix tailTrace_282337
  have hstable : (prefixWord ++ tailWord_282337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282337).length < 2 ^ (prefixWord ++ tailWord_282337).sum := by decide
  have hdescent : baseEnd_282337 < baseStart_282337 := by decide
  rcases family_descends (prefixWord ++ tailWord_282337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282374 : List Nat := [6, 2, 2, 1, 1, 2, 7]
def baseStart_282374 : Nat := 118140960795 + 282374 * 2 ^ 59
def prefixEnd_282374 : Nat := 4983230072969 + 3 ^ 40 * 282374 * 2
def baseEnd_282374 : Nat := 7160177102853503413649

theorem tailTrace_282374 : CollatzResearch.WordTrace tailWord_282374 prefixEnd_282374 7160177102853503413649 := by
  unfold tailWord_282374
  simp only [CollatzResearch.WordTrace]
  refine ⟨321844558719209327652193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6866017252676465656580117 321844558719209327652193)
  ·
    refine ⟨241383419039406995739145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 321844558719209327652193 241383419039406995739145)
    ·
      refine ⟨181037564279555246804359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241383419039406995739145 181037564279555246804359)
      ·
        refine ⟨271556346419332870206539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181037564279555246804359 271556346419332870206539)
        ·
          refine ⟨407334519628999305309809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271556346419332870206539 407334519628999305309809)
          ·
            refine ⟨305500889721749478982357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407334519628999305309809 305500889721749478982357)
            ·
              refine ⟨7160177102853503413649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 305500889721749478982357 7160177102853503413649)
              ·
                rfl

theorem cell21_282374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 7].length) (baseStart_282374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282374 prefixEnd_282374 := by exact prefixLift 282374
  have htrace : WordTrace (prefixWord ++ tailWord_282374) baseStart_282374 baseEnd_282374 := by
    simpa [prefixWord, tailWord_282374, baseEnd_282374] using wordTrace_append hprefix tailTrace_282374
  have hstable : (prefixWord ++ tailWord_282374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282374).length < 2 ^ (prefixWord ++ tailWord_282374).sum := by decide
  have hdescent : baseEnd_282374 < baseStart_282374 := by decide
  rcases family_descends (prefixWord ++ tailWord_282374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282379 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_282379 : Nat := 118140960795 + 282379 * 2 ^ 59
def prefixEnd_282379 : Nat := 4983230072969 + 3 ^ 40 * 282379 * 2
def baseEnd_282379 : Nat := 64442734993802633139497

theorem tailTrace_282379 : CollatzResearch.WordTrace tailWord_282379 prefixEnd_282379 64442734993802633139497 := by
  unfold tailWord_282379
  simp only [CollatzResearch.WordTrace]
  refine ⟨10299208243996584338802191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6866138829331056225868127 10299208243996584338802191)
  ·
    refine ⟨15448812365994876508203287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10299208243996584338802191 15448812365994876508203287)
    ·
      refine ⟨23173218548992314762304931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15448812365994876508203287 23173218548992314762304931)
      ·
        refine ⟨34759827823488472143457397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23173218548992314762304931 34759827823488472143457397)
        ·
          refine ⟨3258733858452044263449131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34759827823488472143457397 3258733858452044263449131)
          ·
            refine ⟨4888100787678066395173697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258733858452044263449131 4888100787678066395173697)
            ·
              refine ⟨3666075590758549796380273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4888100787678066395173697 3666075590758549796380273)
              ·
                refine ⟨2749556693068912347285205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3666075590758549796380273 2749556693068912347285205)
                ·
                  refine ⟨64442734993802633139497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2749556693068912347285205 64442734993802633139497)
                  ·
                    rfl

theorem cell21_282379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_282379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282379 prefixEnd_282379 := by exact prefixLift 282379
  have htrace : WordTrace (prefixWord ++ tailWord_282379) baseStart_282379 baseEnd_282379 := by
    simpa [prefixWord, tailWord_282379, baseEnd_282379] using wordTrace_append hprefix tailTrace_282379
  have hstable : (prefixWord ++ tailWord_282379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282379).length < 2 ^ (prefixWord ++ tailWord_282379).sum := by decide
  have hdescent : baseEnd_282379 < baseStart_282379 := by decide
  rcases family_descends (prefixWord ++ tailWord_282379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282388 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_282388 : Nat := 118140960795 + 282388 * 2 ^ 59
def prefixEnd_282388 : Nat := 4983230072969 + 3 ^ 40 * 282388 * 2
def baseEnd_282388 : Nat := 64444788916420617489479

theorem tailTrace_282388 : CollatzResearch.WordTrace tailWord_282388 prefixEnd_282388 64444788916420617489479 := by
  unfold tailWord_282388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149768250481989437939909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6866357667309319250586545 5149768250481989437939909)
  ·
    refine ⟨965581546965373019613733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5149768250481989437939909 965581546965373019613733)
    ·
      refine ⟨181046540056007441177575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 965581546965373019613733 181046540056007441177575)
      ·
        refine ⟨271569810084011161766363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181046540056007441177575 271569810084011161766363)
        ·
          refine ⟨407354715126016742649545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271569810084011161766363 407354715126016742649545)
          ·
            refine ⟨305516036344512556987159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407354715126016742649545 305516036344512556987159)
            ·
              refine ⟨458274054516768835480739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305516036344512556987159 458274054516768835480739)
              ·
                refine ⟨687411081775153253221109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458274054516768835480739 687411081775153253221109)
                ·
                  refine ⟨64444788916420617489479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 687411081775153253221109 64444788916420617489479)
                  ·
                    rfl

theorem cell21_282388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_282388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282388 prefixEnd_282388 := by exact prefixLift 282388
  have htrace : WordTrace (prefixWord ++ tailWord_282388) baseStart_282388 baseEnd_282388 := by
    simpa [prefixWord, tailWord_282388, baseEnd_282388] using wordTrace_append hprefix tailTrace_282388
  have hstable : (prefixWord ++ tailWord_282388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282388).length < 2 ^ (prefixWord ++ tailWord_282388).sum := by decide
  have hdescent : baseEnd_282388 < baseStart_282388 := by decide
  rcases family_descends (prefixWord ++ tailWord_282388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282444 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_282444 : Nat := 118140960795 + 282444 * 2 ^ 59
def prefixEnd_282444 : Nat := 4983230072969 + 3 ^ 40 * 282444 * 2
def baseEnd_282444 : Nat := 64457568879376964556031

theorem tailTrace_282444 : CollatzResearch.WordTrace tailWord_282444 prefixEnd_282444 64457568879376964556031 := by
  unfold tailWord_282444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150789494380550219959193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6867719325840733626612257 5150789494380550219959193)
  ·
    refine ⟨3863092120785412664969395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5150789494380550219959193 3863092120785412664969395)
    ·
      refine ⟨5794638181178118997454093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863092120785412664969395 5794638181178118997454093)
      ·
        refine ⟨2172989317941794624045285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5794638181178118997454093 2172989317941794624045285)
        ·
          refine ⟨407435497114086492008491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2172989317941794624045285 407435497114086492008491)
          ·
            refine ⟨611153245671129738012737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407435497114086492008491 611153245671129738012737)
            ·
              refine ⟨458364934253347303509553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611153245671129738012737 458364934253347303509553)
              ·
                refine ⟨343773700690010477632165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458364934253347303509553 343773700690010477632165)
                ·
                  refine ⟨64457568879376964556031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343773700690010477632165 64457568879376964556031)
                  ·
                    rfl

theorem cell21_282444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_282444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282444 prefixEnd_282444 := by exact prefixLift 282444
  have htrace : WordTrace (prefixWord ++ tailWord_282444) baseStart_282444 baseEnd_282444 := by
    simpa [prefixWord, tailWord_282444, baseEnd_282444] using wordTrace_append hprefix tailTrace_282444
  have hstable : (prefixWord ++ tailWord_282444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282444).length < 2 ^ (prefixWord ++ tailWord_282444).sum := by decide
  have hdescent : baseEnd_282444 < baseStart_282444 := by decide
  rcases family_descends (prefixWord ++ tailWord_282444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282472 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_282472 : Nat := 118140960795 + 282472 * 2 ^ 59
def prefixEnd_282472 : Nat := 4983230072969 + 3 ^ 40 * 282472 * 2
def baseEnd_282472 : Nat := 64463958860855138089307

theorem tailTrace_282472 : CollatzResearch.WordTrace tailWord_282472 prefixEnd_282472 64463958860855138089307 := by
  unfold tailWord_282472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151300116329830610968835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6868400155106440814625113 5151300116329830610968835)
  ·
    refine ⟨7726950174494745916453253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5151300116329830610968835 7726950174494745916453253)
    ·
      refine ⟨1448803157717764859334985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7726950174494745916453253 1448803157717764859334985)
      ·
        refine ⟨1086602368288323644501239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1448803157717764859334985 1086602368288323644501239)
        ·
          refine ⟨1629903552432485466751859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086602368288323644501239 1629903552432485466751859)
          ·
            refine ⟨2444855328648728200127789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629903552432485466751859 2444855328648728200127789)
            ·
              refine ⟨916820748243273075047921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444855328648728200127789 916820748243273075047921)
              ·
                refine ⟨687615561182454806285941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916820748243273075047921 687615561182454806285941)
                ·
                  refine ⟨64463958860855138089307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 687615561182454806285941 64463958860855138089307)
                  ·
                    rfl

theorem cell21_282472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_282472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282472 prefixEnd_282472 := by exact prefixLift 282472
  have htrace : WordTrace (prefixWord ++ tailWord_282472) baseStart_282472 baseEnd_282472 := by
    simpa [prefixWord, tailWord_282472, baseEnd_282472] using wordTrace_append hprefix tailTrace_282472
  have hstable : (prefixWord ++ tailWord_282472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282472).length < 2 ^ (prefixWord ++ tailWord_282472).sum := by decide
  have hdescent : baseEnd_282472 < baseStart_282472 := by decide
  rcases family_descends (prefixWord ++ tailWord_282472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282489 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 3]
def baseStart_282489 : Nat := 118140960795 + 282489 * 2 ^ 59
def prefixEnd_282489 : Nat := 4983230072969 + 3 ^ 40 * 282489 * 2
def baseEnd_282489 : Nat := 64467838492466886305939

theorem tailTrace_282489 : CollatzResearch.WordTrace tailWord_282489 prefixEnd_282489 64467838492466886305939 := by
  unfold tailWord_282489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303220273598073125306521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6868813515732048750204347 10303220273598073125306521)
  ·
    refine ⟨7727415205198554843979891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10303220273598073125306521 7727415205198554843979891)
    ·
      refine ⟨11591122807797832265969837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727415205198554843979891 11591122807797832265969837)
      ·
        refine ⟨4346671052924187099738689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11591122807797832265969837 4346671052924187099738689)
        ·
          refine ⟨3260003289693140324804017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4346671052924187099738689 3260003289693140324804017)
          ·
            refine ⟨2445002467269855243603013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3260003289693140324804017 2445002467269855243603013)
            ·
              refine ⟨458437962613097858175565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2445002467269855243603013 458437962613097858175565)
              ·
                refine ⟨171914235979911696815837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 458437962613097858175565 171914235979911696815837)
                ·
                  refine ⟨64467838492466886305939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171914235979911696815837 64467838492466886305939)
                  ·
                    rfl

theorem cell21_282489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_282489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282489 prefixEnd_282489 := by exact prefixLift 282489
  have htrace : WordTrace (prefixWord ++ tailWord_282489) baseStart_282489 baseEnd_282489 := by
    simpa [prefixWord, tailWord_282489, baseEnd_282489] using wordTrace_append hprefix tailTrace_282489
  have hstable : (prefixWord ++ tailWord_282489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282489).length < 2 ^ (prefixWord ++ tailWord_282489).sum := by decide
  have hdescent : baseEnd_282489 < baseStart_282489 := by decide
  rcases family_descends (prefixWord ++ tailWord_282489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282503 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_282503 : Nat := 118140960795 + 282503 * 2 ^ 59
def prefixEnd_282503 : Nat := 4983230072969 + 3 ^ 40 * 282503 * 2
def baseEnd_282503 : Nat := 64471033483205973072577

theorem tailTrace_282503 : CollatzResearch.WordTrace tailWord_282503 prefixEnd_282503 64471033483205973072577 := by
  unfold tailWord_282503
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303730895547353516316163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6869153930364902344210775 10303730895547353516316163)
  ·
    refine ⟨15455596343321030274474245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10303730895547353516316163 15455596343321030274474245)
    ·
      refine ⟨2897924314372693176463921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15455596343321030274474245 2897924314372693176463921)
      ·
        refine ⟨2173443235779519882347941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2897924314372693176463921 2173443235779519882347941)
        ·
          refine ⟨407520606708659977940239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2173443235779519882347941 407520606708659977940239)
          ·
            refine ⟨611280910062989966910359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407520606708659977940239 611280910062989966910359)
            ·
              refine ⟨916921365094484950365539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611280910062989966910359 916921365094484950365539)
              ·
                refine ⟨1375382047641727425548309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916921365094484950365539 1375382047641727425548309)
                ·
                  refine ⟨64471033483205973072577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1375382047641727425548309 64471033483205973072577)
                  ·
                    rfl

theorem cell21_282503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_282503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282503 prefixEnd_282503 := by exact prefixLift 282503
  have htrace : WordTrace (prefixWord ++ tailWord_282503) baseStart_282503 baseEnd_282503 := by
    simpa [prefixWord, tailWord_282503, baseEnd_282503] using wordTrace_append hprefix tailTrace_282503
  have hstable : (prefixWord ++ tailWord_282503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282503).length < 2 ^ (prefixWord ++ tailWord_282503).sum := by decide
  have hdescent : baseEnd_282503 < baseStart_282503 := by decide
  rcases family_descends (prefixWord ++ tailWord_282503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282576 : List Nat := [2, 1, 1, 1, 1, 2, 5, 8]
def baseStart_282576 : Nat := 118140960795 + 282576 * 2 ^ 59
def prefixEnd_282576 : Nat := 4983230072969 + 3 ^ 40 * 282576 * 2
def baseEnd_282576 : Nat := 21495897692591356118587

theorem tailTrace_282576 : CollatzResearch.WordTrace tailWord_282576 prefixEnd_282576 21495897692591356118587 := by
  unfold tailWord_282576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153196712141443491861791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6870928949521924655815721 5153196712141443491861791)
  ·
    refine ⟨7729795068212165237792687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5153196712141443491861791 7729795068212165237792687)
    ·
      refine ⟨11594692602318247856689031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729795068212165237792687 11594692602318247856689031)
      ·
        refine ⟨17392038903477371785033547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594692602318247856689031 17392038903477371785033547)
        ·
          refine ⟨26088058355216057677550321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17392038903477371785033547 26088058355216057677550321)
          ·
            refine ⟨19566043766412043258162741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26088058355216057677550321 19566043766412043258162741)
            ·
              refine ⟨1834316603101129055452757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19566043766412043258162741 1834316603101129055452757)
              ·
                refine ⟨21495897692591356118587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1834316603101129055452757 21495897692591356118587)
                ·
                  rfl

theorem cell21_282576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_282576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282576 prefixEnd_282576 := by exact prefixLift 282576
  have htrace : WordTrace (prefixWord ++ tailWord_282576) baseStart_282576 baseEnd_282576 := by
    simpa [prefixWord, tailWord_282576, baseEnd_282576] using wordTrace_append hprefix tailTrace_282576
  have hstable : (prefixWord ++ tailWord_282576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282576).length < 2 ^ (prefixWord ++ tailWord_282576).sum := by decide
  have hdescent : baseEnd_282576 < baseStart_282576 := by decide
  rcases family_descends (prefixWord ++ tailWord_282576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282644 : List Nat := [2, 4, 3, 2, 1, 1, 3, 5]
def baseStart_282644 : Nat := 118140960795 + 282644 * 2 ^ 59
def prefixEnd_282644 : Nat := 4983230072969 + 3 ^ 40 * 282644 * 2
def baseEnd_282644 : Nat := 21501070534740353740763

theorem tailTrace_282644 : CollatzResearch.WordTrace tailWord_282644 prefixEnd_282644 21501070534740353740763 := by
  unfold tailWord_282644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154436794018267298599493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6872582392024356398132657 5154436794018267298599493)
  ·
    refine ⟨966456898878425118487405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5154436794018267298599493 966456898878425118487405)
    ·
      refine ⟨362421337079409419432777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 966456898878425118487405 362421337079409419432777)
      ·
        refine ⟨271816002809557064574583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362421337079409419432777 271816002809557064574583)
        ·
          refine ⟨407724004214335596861875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271816002809557064574583 407724004214335596861875)
          ·
            refine ⟨611586006321503395292813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407724004214335596861875 611586006321503395292813)
            ·
              refine ⟨229344752370563773234805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611586006321503395292813 229344752370563773234805)
              ·
                refine ⟨21501070534740353740763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229344752370563773234805 21501070534740353740763)
                ·
                  rfl

theorem cell21_282644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_282644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282644 prefixEnd_282644 := by exact prefixLift 282644
  have htrace : WordTrace (prefixWord ++ tailWord_282644) baseStart_282644 baseEnd_282644 := by
    simpa [prefixWord, tailWord_282644, baseEnd_282644] using wordTrace_append hprefix tailTrace_282644
  have hstable : (prefixWord ++ tailWord_282644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282644).length < 2 ^ (prefixWord ++ tailWord_282644).sum := by decide
  have hdescent : baseEnd_282644 < baseStart_282644 := by decide
  rcases family_descends (prefixWord ++ tailWord_282644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282734 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_282734 : Nat := 118140960795 + 282734 * 2 ^ 59
def prefixEnd_282734 : Nat := 4983230072969 + 3 ^ 40 * 282734 * 2
def baseEnd_282734 : Nat := 64523750830400904722105

theorem tailTrace_282734 : CollatzResearch.WordTrace tailWord_282734 prefixEnd_282734 64523750830400904722105 := by
  unfold tailWord_282734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289019519713809995996907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6874770771806986645316837 1289019519713809995996907)
  ·
    refine ⟨1933529279570714993995361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289019519713809995996907 1933529279570714993995361)
    ·
      refine ⟨1450146959678036245496521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1933529279570714993995361 1450146959678036245496521)
      ·
        refine ⟨1087610219758527184122391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450146959678036245496521 1087610219758527184122391)
        ·
          refine ⟨1631415329637790776183587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087610219758527184122391 1631415329637790776183587)
          ·
            refine ⟨2447122994456686164275381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631415329637790776183587 2447122994456686164275381)
            ·
              refine ⟨229417780730314327900817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2447122994456686164275381 229417780730314327900817)
              ·
                refine ⟨172063335547735745925613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229417780730314327900817 172063335547735745925613)
                ·
                  refine ⟨64523750830400904722105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172063335547735745925613 64523750830400904722105)
                  ·
                    rfl

theorem cell21_282734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_282734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282734 prefixEnd_282734 := by exact prefixLift 282734
  have htrace : WordTrace (prefixWord ++ tailWord_282734) baseStart_282734 baseEnd_282734 := by
    simpa [prefixWord, tailWord_282734, baseEnd_282734] using wordTrace_append hprefix tailTrace_282734
  have hstable : (prefixWord ++ tailWord_282734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282734).length < 2 ^ (prefixWord ++ tailWord_282734).sum := by decide
  have hdescent : baseEnd_282734 < baseStart_282734 := by decide
  rcases family_descends (prefixWord ++ tailWord_282734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282745 : List Nat := [1, 2, 1, 3, 4, 2, 2, 6]
def baseStart_282745 : Nat := 118140960795 + 282745 * 2 ^ 59
def prefixEnd_282745 : Nat := 4983230072969 + 3 ^ 40 * 282745 * 2
def baseEnd_282745 : Nat := 21508753726755776679583

theorem tailTrace_282745 : CollatzResearch.WordTrace tailWord_282745 prefixEnd_282745 21508753726755776679583 := by
  unfold tailWord_282745
  simp only [CollatzResearch.WordTrace]
  refine ⟨10312557360670628846625689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6875038240447085897750459 10312557360670628846625689)
  ·
    refine ⟨7734418020502971634969267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10312557360670628846625689 7734418020502971634969267)
    ·
      refine ⟨11601627030754457452453901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7734418020502971634969267 11601627030754457452453901)
      ·
        refine ⟨4350610136532921544670213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11601627030754457452453901 4350610136532921544670213)
        ·
          refine ⟨815739400599922789625665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4350610136532921544670213 815739400599922789625665)
          ·
            refine ⟨611804550449942092219249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815739400599922789625665 611804550449942092219249)
            ·
              refine ⟨458853412837456569164437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611804550449942092219249 458853412837456569164437)
              ·
                refine ⟨21508753726755776679583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 458853412837456569164437 21508753726755776679583)
                ·
                  rfl

theorem cell21_282745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_282745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282745 prefixEnd_282745 := by exact prefixLift 282745
  have htrace : WordTrace (prefixWord ++ tailWord_282745) baseStart_282745 baseEnd_282745 := by
    simpa [prefixWord, tailWord_282745, baseEnd_282745] using wordTrace_append hprefix tailTrace_282745
  have hstable : (prefixWord ++ tailWord_282745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282745).length < 2 ^ (prefixWord ++ tailWord_282745).sum := by decide
  have hdescent : baseEnd_282745 < baseStart_282745 := by decide
  rcases family_descends (prefixWord ++ tailWord_282745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282748 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_282748 : Nat := 118140960795 + 282748 * 2 ^ 59
def prefixEnd_282748 : Nat := 4983230072969 + 3 ^ 40 * 282748 * 2
def baseEnd_282748 : Nat := 64526945821139991488743

theorem tailTrace_282748 : CollatzResearch.WordTrace tailWord_282748 prefixEnd_282748 64526945821139991488743 := by
  unfold tailWord_282748
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156333389829880179492449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6875111186439840239323265 5156333389829880179492449)
  ·
    refine ⟨3867250042372410134619337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5156333389829880179492449 3867250042372410134619337)
    ·
      refine ⟨2900437531779307600964503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3867250042372410134619337 2900437531779307600964503)
      ·
        refine ⟨4350656297668961401446755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900437531779307600964503 4350656297668961401446755)
        ·
          refine ⟨6525984446503442102170133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350656297668961401446755 6525984446503442102170133)
          ·
            refine ⟨305905520929848848539225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6525984446503442102170133 305905520929848848539225)
            ·
              refine ⟨229429140697386636404419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305905520929848848539225 229429140697386636404419)
              ·
                refine ⟨344143711046079954606629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229429140697386636404419 344143711046079954606629)
                ·
                  refine ⟨64526945821139991488743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344143711046079954606629 64526945821139991488743)
                  ·
                    rfl

theorem cell21_282748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_282748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282748 prefixEnd_282748 := by exact prefixLift 282748
  have htrace : WordTrace (prefixWord ++ tailWord_282748) baseStart_282748 baseEnd_282748 := by
    simpa [prefixWord, tailWord_282748, baseEnd_282748] using wordTrace_append hprefix tailTrace_282748
  have hstable : (prefixWord ++ tailWord_282748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282748).length < 2 ^ (prefixWord ++ tailWord_282748).sum := by decide
  have hdescent : baseEnd_282748 < baseStart_282748 := by decide
  rcases family_descends (prefixWord ++ tailWord_282748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282759 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_282759 : Nat := 118140960795 + 282759 * 2 ^ 59
def prefixEnd_282759 : Nat := 4983230072969 + 3 ^ 40 * 282759 * 2
def baseEnd_282759 : Nat := 64529456171006416805387

theorem tailTrace_282759 : CollatzResearch.WordTrace tailWord_282759 prefixEnd_282759 64529456171006416805387 := by
  unfold tailWord_282759
  simp only [CollatzResearch.WordTrace]
  refine ⟨10313067982619909237635331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6875378655079939491756887 10313067982619909237635331)
  ·
    refine ⟨15469601973929863856452997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10313067982619909237635331 15469601973929863856452997)
    ·
      refine ⟨2900550370111849473084937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15469601973929863856452997 2900550370111849473084937)
      ·
        refine ⟨2175412777583887104813703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2900550370111849473084937 2175412777583887104813703)
        ·
          refine ⟨3263119166375830657220555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175412777583887104813703 3263119166375830657220555)
          ·
            refine ⟨4894678749563745985830833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263119166375830657220555 4894678749563745985830833)
            ·
              refine ⟨3671009062172809489373125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4894678749563745985830833 3671009062172809489373125)
              ·
                refine ⟨688314199157401779257461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3671009062172809489373125 688314199157401779257461)
                ·
                  refine ⟨64529456171006416805387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688314199157401779257461 64529456171006416805387)
                  ·
                    rfl

theorem cell21_282759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_282759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282759 prefixEnd_282759 := by exact prefixLift 282759
  have htrace : WordTrace (prefixWord ++ tailWord_282759) baseStart_282759 baseEnd_282759 := by
    simpa [prefixWord, tailWord_282759, baseEnd_282759] using wordTrace_append hprefix tailTrace_282759
  have hstable : (prefixWord ++ tailWord_282759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282759).length < 2 ^ (prefixWord ++ tailWord_282759).sum := by decide
  have hdescent : baseEnd_282759 < baseStart_282759 := by decide
  rcases family_descends (prefixWord ++ tailWord_282759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282838 : List Nat := [5, 2, 1, 2, 1, 2, 8]
def baseStart_282838 : Nat := 118140960795 + 282838 * 2 ^ 59
def prefixEnd_282838 : Nat := 4983230072969 + 3 ^ 40 * 282838 * 2
def baseEnd_282838 : Nat := 7171942783035537220951

theorem tailTrace_282838 : CollatzResearch.WordTrace tailWord_282838 prefixEnd_282838 7171942783035537220951 := by
  unfold tailWord_282838
  simp only [CollatzResearch.WordTrace]
  refine ⟨644746834333356608110073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6877299566222470486507445 644746834333356608110073)
  ·
    refine ⟨483560125750017456082555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 644746834333356608110073 483560125750017456082555)
    ·
      refine ⟨725340188625026184123833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483560125750017456082555 725340188625026184123833)
      ·
        refine ⟨544005141468769638092875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725340188625026184123833 544005141468769638092875)
        ·
          refine ⟨816007712203154457139313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544005141468769638092875 816007712203154457139313)
          ·
            refine ⟨612005784152365842854485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816007712203154457139313 612005784152365842854485)
            ·
              refine ⟨7171942783035537220951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 612005784152365842854485 7171942783035537220951)
              ·
                rfl

theorem cell21_282838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 8].length) (baseStart_282838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282838 prefixEnd_282838 := by exact prefixLift 282838
  have htrace : WordTrace (prefixWord ++ tailWord_282838) baseStart_282838 baseEnd_282838 := by
    simpa [prefixWord, tailWord_282838, baseEnd_282838] using wordTrace_append hprefix tailTrace_282838
  have hstable : (prefixWord ++ tailWord_282838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282838).length < 2 ^ (prefixWord ++ tailWord_282838).sum := by decide
  have hdescent : baseEnd_282838 < baseStart_282838 := by decide
  rcases family_descends (prefixWord ++ tailWord_282838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282917 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 4]
def baseStart_282917 : Nat := 118140960795 + 282917 * 2 ^ 59
def prefixEnd_282917 : Nat := 4983230072969 + 3 ^ 40 * 282917 * 2
def baseEnd_282917 : Nat := 64565513923633253171731

theorem tailTrace_282917 : CollatzResearch.WordTrace tailWord_282917 prefixEnd_282917 64565513923633253171731 := by
  unfold tailWord_282917
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318830716047502221887005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6879220477365001481258003 10318830716047502221887005)
  ·
    refine ⟨3869561518517813333207627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10318830716047502221887005 3869561518517813333207627)
    ·
      refine ⟨5804342277776719999811441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869561518517813333207627 5804342277776719999811441)
      ·
        refine ⟨4353256708332539999858581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804342277776719999811441 4353256708332539999858581)
        ·
          refine ⟨204058908203087812493371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4353256708332539999858581 204058908203087812493371)
          ·
            refine ⟨306088362304631718740057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204058908203087812493371 306088362304631718740057)
            ·
              refine ⟨229566271728473789055043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306088362304631718740057 229566271728473789055043)
              ·
                refine ⟨344349407592710683582565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229566271728473789055043 344349407592710683582565)
                ·
                  refine ⟨64565513923633253171731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344349407592710683582565 64565513923633253171731)
                  ·
                    rfl

theorem cell21_282917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_282917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_282917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_282917 prefixEnd_282917 := by exact prefixLift 282917
  have htrace : WordTrace (prefixWord ++ tailWord_282917) baseStart_282917 baseEnd_282917 := by
    simpa [prefixWord, tailWord_282917, baseEnd_282917] using wordTrace_append hprefix tailTrace_282917
  have hstable : (prefixWord ++ tailWord_282917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282917).length < 2 ^ (prefixWord ++ tailWord_282917).sum := by decide
  have hdescent : baseEnd_282917 < baseStart_282917 := by decide
  rcases family_descends (prefixWord ++ tailWord_282917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283001 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_283001 : Nat := 118140960795 + 283001 * 2 ^ 59
def prefixEnd_283001 : Nat := 4983230072969 + 3 ^ 40 * 283001 * 2
def baseEnd_283001 : Nat := 64584683868067773771559

theorem tailTrace_283001 : CollatzResearch.WordTrace tailWord_283001 prefixEnd_283001 64584683868067773771559 := by
  unfold tailWord_283001
  simp only [CollatzResearch.WordTrace]
  refine ⟨10321894447743184567944857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6881262965162123045296571 10321894447743184567944857)
  ·
    refine ⟨7741420835807388425958643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10321894447743184567944857 7741420835807388425958643)
    ·
      refine ⟨11612131253711082638937965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7741420835807388425958643 11612131253711082638937965)
      ·
        refine ⟨4354549220141655989601737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11612131253711082638937965 4354549220141655989601737)
        ·
          refine ⟨3265911915106241992201303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4354549220141655989601737 3265911915106241992201303)
          ·
            refine ⟨4898867872659362988301955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265911915106241992201303 4898867872659362988301955)
            ·
              refine ⟨7348301808989044482452933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898867872659362988301955 7348301808989044482452933)
              ·
                refine ⟨1377806589185445840459925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7348301808989044482452933 1377806589185445840459925)
                ·
                  refine ⟨64584683868067773771559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1377806589185445840459925 64584683868067773771559)
                  ·
                    rfl

theorem cell21_283001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_283001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283001 prefixEnd_283001 := by exact prefixLift 283001
  have htrace : WordTrace (prefixWord ++ tailWord_283001) baseStart_283001 baseEnd_283001 := by
    simpa [prefixWord, tailWord_283001, baseEnd_283001] using wordTrace_append hprefix tailTrace_283001
  have hstable : (prefixWord ++ tailWord_283001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283001).length < 2 ^ (prefixWord ++ tailWord_283001).sum := by decide
  have hdescent : baseEnd_283001 < baseStart_283001 := by decide
  rcases family_descends (prefixWord ++ tailWord_283001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283010 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_283010 : Nat := 118140960795 + 283010 * 2 ^ 59
def prefixEnd_283010 : Nat := 4983230072969 + 3 ^ 40 * 283010 * 2
def baseEnd_283010 : Nat := 64586737790685758121541

theorem tailTrace_283010 : CollatzResearch.WordTrace tailWord_283010 prefixEnd_283010 64586737790685758121541 := by
  unfold tailWord_283010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580555676177644776255621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6881481803140386070014989 2580555676177644776255621)
  ·
    refine ⟨483854189283308395547929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2580555676177644776255621 483854189283308395547929)
    ·
      refine ⟨362890641962481296660947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483854189283308395547929 362890641962481296660947)
      ·
        refine ⟨544335962943721944991421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362890641962481296660947 544335962943721944991421)
        ·
          refine ⟨204125986103895729371783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544335962943721944991421 204125986103895729371783)
          ·
            refine ⟨306188979155843594057675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204125986103895729371783 306188979155843594057675)
            ·
              refine ⟨459283468733765391086513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306188979155843594057675 459283468733765391086513)
              ·
                refine ⟨344462601550324043314885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459283468733765391086513 344462601550324043314885)
                ·
                  refine ⟨64586737790685758121541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344462601550324043314885 64586737790685758121541)
                  ·
                    rfl

theorem cell21_283010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_283010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283010 prefixEnd_283010 := by exact prefixLift 283010
  have htrace : WordTrace (prefixWord ++ tailWord_283010) baseStart_283010 baseEnd_283010 := by
    simpa [prefixWord, tailWord_283010, baseEnd_283010] using wordTrace_append hprefix tailTrace_283010
  have hstable : (prefixWord ++ tailWord_283010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283010).length < 2 ^ (prefixWord ++ tailWord_283010).sum := by decide
  have hdescent : baseEnd_283010 < baseStart_283010 := by decide
  rcases family_descends (prefixWord ++ tailWord_283010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283080 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_283080 : Nat := 118140960795 + 283080 * 2 ^ 59
def prefixEnd_283080 : Nat := 4983230072969 + 3 ^ 40 * 283080 * 2
def baseEnd_283080 : Nat := 64602712744381191954731

theorem tailTrace_283080 : CollatzResearch.WordTrace tailWord_283080 prefixEnd_283080 64602712744381191954731 := by
  unfold tailWord_283080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162387907228490530035347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6883183876304654040047129 5162387907228490530035347)
  ·
    refine ⟨7743581860842735795053021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162387907228490530035347 7743581860842735795053021)
    ·
      refine ⟨2903843197816025923144883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7743581860842735795053021 2903843197816025923144883)
      ·
        refine ⟨4355764796724038884717325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903843197816025923144883 4355764796724038884717325)
        ·
          refine ⟨1633411798771514581768997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4355764796724038884717325 1633411798771514581768997)
          ·
            refine ⟨306264712269658984081687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1633411798771514581768997 306264712269658984081687)
            ·
              refine ⟨459397068404488476122531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306264712269658984081687 459397068404488476122531)
              ·
                refine ⟨689095602606732714183797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459397068404488476122531 689095602606732714183797)
                ·
                  refine ⟨64602712744381191954731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689095602606732714183797 64602712744381191954731)
                  ·
                    rfl

theorem cell21_283080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_283080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283080 prefixEnd_283080 := by exact prefixLift 283080
  have htrace : WordTrace (prefixWord ++ tailWord_283080) baseStart_283080 baseEnd_283080 := by
    simpa [prefixWord, tailWord_283080, baseEnd_283080] using wordTrace_append hprefix tailTrace_283080
  have hstable : (prefixWord ++ tailWord_283080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283080).length < 2 ^ (prefixWord ++ tailWord_283080).sum := by decide
  have hdescent : baseEnd_283080 < baseStart_283080 := by decide
  rcases family_descends (prefixWord ++ tailWord_283080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283125 : List Nat := [1, 3, 5, 1, 2, 9]
def baseStart_283125 : Nat := 118140960795 + 283125 * 2 ^ 59
def prefixEnd_283125 : Nat := 4983230072969 + 3 ^ 40 * 283125 * 2
def baseEnd_283125 : Nat := 2393073420647078285357

theorem tailTrace_283125 : CollatzResearch.WordTrace tailWord_283125 prefixEnd_283125 2393073420647078285357 := by
  unfold tailWord_283125
  simp only [CollatzResearch.WordTrace]
  refine ⟨10326417099293953745458829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6884278066195969163639219 10326417099293953745458829)
  ·
    refine ⟨3872406412235232654547061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10326417099293953745458829 3872406412235232654547061)
    ·
      refine ⟨363038101147053061363787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3872406412235232654547061 363038101147053061363787)
      ·
        refine ⟨544557151720579592045681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363038101147053061363787 544557151720579592045681)
        ·
          refine ⟨408417863790434694034261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544557151720579592045681 408417863790434694034261)
          ·
            refine ⟨2393073420647078285357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 408417863790434694034261 2393073420647078285357)
            ·
              rfl

theorem cell21_283125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 9].length) (baseStart_283125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283125 prefixEnd_283125 := by exact prefixLift 283125
  have htrace : WordTrace (prefixWord ++ tailWord_283125) baseStart_283125 baseEnd_283125 := by
    simpa [prefixWord, tailWord_283125, baseEnd_283125] using wordTrace_append hprefix tailTrace_283125
  have hstable : (prefixWord ++ tailWord_283125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283125).length < 2 ^ (prefixWord ++ tailWord_283125).sum := by decide
  have hdescent : baseEnd_283125 < baseStart_283125 := by decide
  rcases family_descends (prefixWord ++ tailWord_283125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283156 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_283156 : Nat := 118140960795 + 283156 * 2 ^ 59
def prefixEnd_283156 : Nat := 4983230072969 + 3 ^ 40 * 283156 * 2
def baseEnd_283156 : Nat := 64620056979821948687909

theorem tailTrace_283156 : CollatzResearch.WordTrace tailWord_283156 prefixEnd_283156 64620056979821948687909 := by
  unfold tailWord_283156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163773881090823019918661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6885031841454430693224881 5163773881090823019918661)
  ·
    refine ⟨968207602704529316234749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5163773881090823019918661 968207602704529316234749)
    ·
      refine ⟨363077851014198493588031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 968207602704529316234749 363077851014198493588031)
      ·
        refine ⟨544616776521297740382047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363077851014198493588031 544616776521297740382047)
        ·
          refine ⟨816925164781946610573071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544616776521297740382047 816925164781946610573071)
          ·
            refine ⟨1225387747172919915859607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816925164781946610573071 1225387747172919915859607)
            ·
              refine ⟨1838081620759379873789411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225387747172919915859607 1838081620759379873789411)
              ·
                refine ⟨2757122431139069810684117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838081620759379873789411 2757122431139069810684117)
                ·
                  refine ⟨64620056979821948687909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2757122431139069810684117 64620056979821948687909)
                  ·
                    rfl

theorem cell21_283156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_283156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283156 prefixEnd_283156 := by exact prefixLift 283156
  have htrace : WordTrace (prefixWord ++ tailWord_283156) baseStart_283156 baseEnd_283156 := by
    simpa [prefixWord, tailWord_283156, baseEnd_283156] using wordTrace_append hprefix tailTrace_283156
  have hstable : (prefixWord ++ tailWord_283156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283156).length < 2 ^ (prefixWord ++ tailWord_283156).sum := by decide
  have hdescent : baseEnd_283156 < baseStart_283156 := by decide
  rcases family_descends (prefixWord ++ tailWord_283156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283232 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_283232 : Nat := 118140960795 + 283232 * 2 ^ 59
def prefixEnd_283232 : Nat := 4983230072969 + 3 ^ 40 * 283232 * 2
def baseEnd_283232 : Nat := 64637401215262705421087

theorem tailTrace_283232 : CollatzResearch.WordTrace tailWord_283232 prefixEnd_283232 64637401215262705421087 := by
  unfold tailWord_283232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165159854953155509801975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6886879806604207346402633 5165159854953155509801975)
  ·
    refine ⟨7747739782429733264702963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165159854953155509801975 7747739782429733264702963)
    ·
      refine ⟨11621609673644599897054445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747739782429733264702963 11621609673644599897054445)
      ·
        refine ⟨4358103627616724961395417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11621609673644599897054445 4358103627616724961395417)
        ·
          refine ⟨3268577720712543721046563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4358103627616724961395417 3268577720712543721046563)
          ·
            refine ⟨4902866581068815581569845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268577720712543721046563 4902866581068815581569845)
            ·
              refine ⟨459643741975201460772173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4902866581068815581569845 459643741975201460772173)
              ·
                refine ⟨172366403240700547789565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459643741975201460772173 172366403240700547789565)
                ·
                  refine ⟨64637401215262705421087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172366403240700547789565 64637401215262705421087)
                  ·
                    rfl

theorem cell21_283232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_283232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283232 prefixEnd_283232 := by exact prefixLift 283232
  have htrace : WordTrace (prefixWord ++ tailWord_283232) baseStart_283232 baseEnd_283232 := by
    simpa [prefixWord, tailWord_283232, baseEnd_283232] using wordTrace_append hprefix tailTrace_283232
  have hstable : (prefixWord ++ tailWord_283232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283232).length < 2 ^ (prefixWord ++ tailWord_283232).sum := by decide
  have hdescent : baseEnd_283232 < baseStart_283232 := by decide
  rcases family_descends (prefixWord ++ tailWord_283232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283246 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_283246 : Nat := 118140960795 + 283246 * 2 ^ 59
def prefixEnd_283246 : Nat := 4983230072969 + 3 ^ 40 * 283246 * 2
def baseEnd_283246 : Nat := 64640596206001792187725

theorem tailTrace_283246 : CollatzResearch.WordTrace tailWord_283246 prefixEnd_283246 64640596206001792187725 := by
  unfold tailWord_283246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291353791481948926326699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6887220221237060940409061 1291353791481948926326699)
  ·
    refine ⟨1937030687222923389490049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1291353791481948926326699 1937030687222923389490049)
    ·
      refine ⟨1452773015417192542117537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1937030687222923389490049 1452773015417192542117537)
      ·
        refine ⟨1089579761562894406588153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452773015417192542117537 1089579761562894406588153)
        ·
          refine ⟨817184821172170804941115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089579761562894406588153 817184821172170804941115)
          ·
            refine ⟨1225777231758256207411673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817184821172170804941115 1225777231758256207411673)
            ·
              refine ⟨919332923818692155558755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225777231758256207411673 919332923818692155558755)
              ·
                refine ⟨1378999385728038233338133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919332923818692155558755 1378999385728038233338133)
                ·
                  refine ⟨64640596206001792187725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1378999385728038233338133 64640596206001792187725)
                  ·
                    rfl

theorem cell21_283246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_283246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283246 prefixEnd_283246 := by exact prefixLift 283246
  have htrace : WordTrace (prefixWord ++ tailWord_283246) baseStart_283246 baseEnd_283246 := by
    simpa [prefixWord, tailWord_283246, baseEnd_283246] using wordTrace_append hprefix tailTrace_283246
  have hstable : (prefixWord ++ tailWord_283246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283246).length < 2 ^ (prefixWord ++ tailWord_283246).sum := by decide
  have hdescent : baseEnd_283246 < baseStart_283246 := by decide
  rcases family_descends (prefixWord ++ tailWord_283246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283305 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_283305 : Nat := 118140960795 + 283305 * 2 ^ 59
def prefixEnd_283305 : Nat := 4983230072969 + 3 ^ 40 * 283305 * 2
def baseEnd_283305 : Nat := 64654060809830800704271

theorem tailTrace_283305 : CollatzResearch.WordTrace tailWord_283305 prefixEnd_283305 64654060809830800704271 := by
  unfold tailWord_283305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332982238641844487011369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6888654825761229658007579 10332982238641844487011369)
  ·
    refine ⟨7749736678981383365258527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10332982238641844487011369 7749736678981383365258527)
    ·
      refine ⟨11624605018472075047887791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749736678981383365258527 11624605018472075047887791)
      ·
        refine ⟨17436907527708112571831687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11624605018472075047887791 17436907527708112571831687)
        ·
          refine ⟨26155361291562168857747531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17436907527708112571831687 26155361291562168857747531)
          ·
            refine ⟨39233041937343253286621297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26155361291562168857747531 39233041937343253286621297)
            ·
              refine ⟨29424781453007439964965973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39233041937343253286621297 29424781453007439964965973)
              ·
                refine ⟨344821657652430937089445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 29424781453007439964965973 344821657652430937089445)
                ·
                  refine ⟨64654060809830800704271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344821657652430937089445 64654060809830800704271)
                  ·
                    rfl

theorem cell21_283305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_283305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283305 prefixEnd_283305 := by exact prefixLift 283305
  have htrace : WordTrace (prefixWord ++ tailWord_283305) baseStart_283305 baseEnd_283305 := by
    simpa [prefixWord, tailWord_283305, baseEnd_283305] using wordTrace_append hprefix tailTrace_283305
  have hstable : (prefixWord ++ tailWord_283305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283305).length < 2 ^ (prefixWord ++ tailWord_283305).sum := by decide
  have hdescent : baseEnd_283305 < baseStart_283305 := by decide
  rcases family_descends (prefixWord ++ tailWord_283305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283356 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_283356 : Nat := 118140960795 + 283356 * 2 ^ 59
def prefixEnd_283356 : Nat := 4983230072969 + 3 ^ 40 * 283356 * 2
def baseEnd_283356 : Nat := 64665699704666045354167

theorem tailTrace_283356 : CollatzResearch.WordTrace tailWord_283356 prefixEnd_283356 64665699704666045354167 := by
  unfold tailWord_283356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167421180728540098558961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6889894907638053464745281 5167421180728540098558961)
  ·
    refine ⟨3875565885546405073919221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5167421180728540098558961 3875565885546405073919221)
    ·
      refine ⟨363334301769975475679927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3875565885546405073919221 363334301769975475679927)
      ·
        refine ⟨545001452654963213519891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363334301769975475679927 545001452654963213519891)
        ·
          refine ⟨817502178982444820279837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545001452654963213519891 817502178982444820279837)
          ·
            refine ⟨306563317118416807604939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 817502178982444820279837 306563317118416807604939)
            ·
              refine ⟨459844975677625211407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306563317118416807604939 459844975677625211407409)
              ·
                refine ⟨344883731758218908555557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459844975677625211407409 344883731758218908555557)
                ·
                  refine ⟨64665699704666045354167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344883731758218908555557 64665699704666045354167)
                  ·
                    rfl

theorem cell21_283356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_283356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283356 prefixEnd_283356 := by exact prefixLift 283356
  have htrace : WordTrace (prefixWord ++ tailWord_283356) baseStart_283356 baseEnd_283356 := by
    simpa [prefixWord, tailWord_283356, baseEnd_283356] using wordTrace_append hprefix tailTrace_283356
  have hstable : (prefixWord ++ tailWord_283356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283356).length < 2 ^ (prefixWord ++ tailWord_283356).sum := by decide
  have hdescent : baseEnd_283356 < baseStart_283356 := by decide
  rcases family_descends (prefixWord ++ tailWord_283356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283474 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_283474 : Nat := 118140960795 + 283474 * 2 ^ 59
def prefixEnd_283474 : Nat := 4983230072969 + 3 ^ 40 * 283474 * 2
def baseEnd_283474 : Nat := 64692628912324062387259

theorem tailTrace_283474 : CollatzResearch.WordTrace tailWord_283474 prefixEnd_283474 64692628912324062387259 := by
  unfold tailWord_283474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584786543757396587478369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6892764116686390899942317 2584786543757396587478369)
  ·
    refine ⟨1938589907818047440608777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2584786543757396587478369 1938589907818047440608777)
    ·
      refine ⟨1453942430863535580456583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1938589907818047440608777 1453942430863535580456583)
      ·
        refine ⟨2180913646295303370684875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453942430863535580456583 2180913646295303370684875)
        ·
          refine ⟨3271370469442955056027313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180913646295303370684875 3271370469442955056027313)
          ·
            refine ⟨2453527852082216292020485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271370469442955056027313 2453527852082216292020485)
            ·
              refine ⟨460036472265415554753841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2453527852082216292020485 460036472265415554753841)
              ·
                refine ⟨345027354199061666065381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460036472265415554753841 345027354199061666065381)
                ·
                  refine ⟨64692628912324062387259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345027354199061666065381 64692628912324062387259)
                  ·
                    rfl

theorem cell21_283474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_283474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283474 prefixEnd_283474 := by exact prefixLift 283474
  have htrace : WordTrace (prefixWord ++ tailWord_283474) baseStart_283474 baseEnd_283474 := by
    simpa [prefixWord, tailWord_283474, baseEnd_283474] using wordTrace_append hprefix tailTrace_283474
  have hstable : (prefixWord ++ tailWord_283474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283474).length < 2 ^ (prefixWord ++ tailWord_283474).sum := by decide
  have hdescent : baseEnd_283474 < baseStart_283474 := by decide
  rcases family_descends (prefixWord ++ tailWord_283474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283519 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 3]
def baseStart_283519 : Nat := 118140960795 + 283519 * 2 ^ 59
def prefixEnd_283519 : Nat := 4983230072969 + 3 ^ 40 * 283519 * 2
def baseEnd_283519 : Nat := 64702898525413984137167

theorem tailTrace_283519 : CollatzResearch.WordTrace tailWord_283519 prefixEnd_283519 64702898525413984137167 := by
  unfold tailWord_283519
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340787459866559035301611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6893858306577706023534407 10340787459866559035301611)
  ·
    refine ⟨15511181189799838552952417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10340787459866559035301611 15511181189799838552952417)
    ·
      refine ⟨11633385892349878914714313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15511181189799838552952417 11633385892349878914714313)
      ·
        refine ⟨8725039419262409186035735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11633385892349878914714313 8725039419262409186035735)
        ·
          refine ⟨13087559128893613779053603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8725039419262409186035735 13087559128893613779053603)
          ·
            refine ⟨19631338693340420668580405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13087559128893613779053603 19631338693340420668580405)
            ·
              refine ⟨1840438002500664437679413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19631338693340420668580405 1840438002500664437679413)
              ·
                refine ⟨172541062734437291032445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1840438002500664437679413 172541062734437291032445)
                ·
                  refine ⟨64702898525413984137167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172541062734437291032445 64702898525413984137167)
                  ·
                    rfl

theorem cell21_283519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3].length) (baseStart_283519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283519 prefixEnd_283519 := by exact prefixLift 283519
  have htrace : WordTrace (prefixWord ++ tailWord_283519) baseStart_283519 baseEnd_283519 := by
    simpa [prefixWord, tailWord_283519, baseEnd_283519] using wordTrace_append hprefix tailTrace_283519
  have hstable : (prefixWord ++ tailWord_283519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283519).length < 2 ^ (prefixWord ++ tailWord_283519).sum := by decide
  have hdescent : baseEnd_283519 < baseStart_283519 := by decide
  rcases family_descends (prefixWord ++ tailWord_283519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283522 : List Nat := [3, 4, 2, 2, 1, 1, 8]
def baseStart_283522 : Nat := 118140960795 + 283522 * 2 ^ 59
def prefixEnd_283522 : Nat := 4983230072969 + 3 ^ 40 * 283522 * 2
def baseEnd_283522 : Nat := 7189287018476293954129

theorem tailTrace_283522 : CollatzResearch.WordTrace tailWord_283522 prefixEnd_283522 7189287018476293954129 := by
  unfold tailWord_283522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585224219713922636915205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6893931252570460365107213 2585224219713922636915205)
  ·
    refine ⟨484729541196360494421601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2585224219713922636915205 484729541196360494421601)
    ·
      refine ⟨363547155897270370816201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 484729541196360494421601 363547155897270370816201)
      ·
        refine ⟨272660366922952778112151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363547155897270370816201 272660366922952778112151)
        ·
          refine ⟨408990550384429167168227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272660366922952778112151 408990550384429167168227)
          ·
            refine ⟨613485825576643750752341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408990550384429167168227 613485825576643750752341)
            ·
              refine ⟨7189287018476293954129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 613485825576643750752341 7189287018476293954129)
              ·
                rfl

theorem cell21_283522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 8].length) (baseStart_283522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283522 prefixEnd_283522 := by exact prefixLift 283522
  have htrace : WordTrace (prefixWord ++ tailWord_283522) baseStart_283522 baseEnd_283522 := by
    simpa [prefixWord, tailWord_283522, baseEnd_283522] using wordTrace_append hprefix tailTrace_283522
  have hstable : (prefixWord ++ tailWord_283522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283522).length < 2 ^ (prefixWord ++ tailWord_283522).sum := by decide
  have hdescent : baseEnd_283522 < baseStart_283522 := by decide
  rcases family_descends (prefixWord ++ tailWord_283522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283581 : List Nat := [1, 4, 1, 2, 5, 1, 7]
def baseStart_283581 : Nat := 118140960795 + 283581 * 2 ^ 59
def prefixEnd_283581 : Nat := 4983230072969 + 3 ^ 40 * 283581 * 2
def baseEnd_283581 : Nat := 7190783085568406011523

theorem tailTrace_283581 : CollatzResearch.WordTrace tailWord_283581 prefixEnd_283581 7190783085568406011523 := by
  unfold tailWord_283581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343048785641943624058597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6895365857094629082705731 10343048785641943624058597)
  ·
    refine ⟨1939321647307864429510987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10343048785641943624058597 1939321647307864429510987)
    ·
      refine ⟨2908982470961796644266481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939321647307864429510987 2908982470961796644266481)
      ·
        refine ⟨2181736853221347483199861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2908982470961796644266481 2181736853221347483199861)
        ·
          refine ⟨204537829989501326549987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2181736853221347483199861 204537829989501326549987)
          ·
            refine ⟨306806744984251989824981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204537829989501326549987 306806744984251989824981)
            ·
              refine ⟨7190783085568406011523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 306806744984251989824981 7190783085568406011523)
              ·
                rfl

theorem cell21_283581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 7].length) (baseStart_283581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283581 prefixEnd_283581 := by exact prefixLift 283581
  have htrace : WordTrace (prefixWord ++ tailWord_283581) baseStart_283581 baseEnd_283581 := by
    simpa [prefixWord, tailWord_283581, baseEnd_283581] using wordTrace_append hprefix tailTrace_283581
  have hstable : (prefixWord ++ tailWord_283581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283581).length < 2 ^ (prefixWord ++ tailWord_283581).sum := by decide
  have hdescent : baseEnd_283581 < baseStart_283581 := by decide
  rcases family_descends (prefixWord ++ tailWord_283581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283595 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 5]
def baseStart_283595 : Nat := 118140960795 + 283595 * 2 ^ 59
def prefixEnd_283595 : Nat := 4983230072969 + 3 ^ 40 * 283595 * 2
def baseEnd_283595 : Nat := 64720242760854740870345

theorem tailTrace_283595 : CollatzResearch.WordTrace tailWord_283595 prefixEnd_283595 64720242760854740870345 := by
  unfold tailWord_283595
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343559407591224015068239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6895706271727482676712159 10343559407591224015068239)
  ·
    refine ⟨15515339111386836022602359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10343559407591224015068239 15515339111386836022602359)
    ·
      refine ⟨23273008667080254033903539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15515339111386836022602359 23273008667080254033903539)
      ·
        refine ⟨34909513000620381050855309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23273008667080254033903539 34909513000620381050855309)
        ·
          refine ⟨13091067375232642894070741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34909513000620381050855309 13091067375232642894070741)
          ·
            refine ⟨306821891607015067829783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13091067375232642894070741 306821891607015067829783)
            ·
              refine ⟨460232837410522601744675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306821891607015067829783 460232837410522601744675)
              ·
                refine ⟨690349256115783902617013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460232837410522601744675 690349256115783902617013)
                ·
                  refine ⟨64720242760854740870345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 690349256115783902617013 64720242760854740870345)
                  ·
                    rfl

theorem cell21_283595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_283595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283595 prefixEnd_283595 := by exact prefixLift 283595
  have htrace : WordTrace (prefixWord ++ tailWord_283595) baseStart_283595 baseEnd_283595 := by
    simpa [prefixWord, tailWord_283595, baseEnd_283595] using wordTrace_append hprefix tailTrace_283595
  have hstable : (prefixWord ++ tailWord_283595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283595).length < 2 ^ (prefixWord ++ tailWord_283595).sum := by decide
  have hdescent : baseEnd_283595 < baseStart_283595 := by decide
  rcases family_descends (prefixWord ++ tailWord_283595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283671 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_283671 : Nat := 118140960795 + 283671 * 2 ^ 59
def prefixEnd_283671 : Nat := 4983230072969 + 3 ^ 40 * 283671 * 2
def baseEnd_283671 : Nat := 64737586996295497603523

theorem tailTrace_283671 : CollatzResearch.WordTrace tailWord_283671 prefixEnd_283671 64737586996295497603523 := by
  unfold tailWord_283671
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346331355315888994834867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6897554236877259329889911 10346331355315888994834867)
  ·
    refine ⟨15519497032973833492252301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10346331355315888994834867 15519497032973833492252301)
    ·
      refine ⟨5819811387365187559594613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15519497032973833492252301 5819811387365187559594613)
      ·
        refine ⟨545607317565486333711995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5819811387365187559594613 545607317565486333711995)
        ·
          refine ⟨818410976348229500567993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545607317565486333711995 818410976348229500567993)
          ·
            refine ⟨613808232261172125425995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818410976348229500567993 613808232261172125425995)
            ·
              refine ⟨920712348391758188138993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613808232261172125425995 920712348391758188138993)
              ·
                refine ⟨690534261293818641104245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920712348391758188138993 690534261293818641104245)
                ·
                  refine ⟨64737586996295497603523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 690534261293818641104245 64737586996295497603523)
                  ·
                    rfl

theorem cell21_283671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_283671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283671 prefixEnd_283671 := by exact prefixLift 283671
  have htrace : WordTrace (prefixWord ++ tailWord_283671) baseStart_283671 baseEnd_283671 := by
    simpa [prefixWord, tailWord_283671, baseEnd_283671] using wordTrace_append hprefix tailTrace_283671
  have hstable : (prefixWord ++ tailWord_283671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283671).length < 2 ^ (prefixWord ++ tailWord_283671).sum := by decide
  have hdescent : baseEnd_283671 < baseStart_283671 := by decide
  rcases family_descends (prefixWord ++ tailWord_283671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283702 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_283702 : Nat := 118140960795 + 283702 * 2 ^ 59
def prefixEnd_283702 : Nat := 4983230072969 + 3 ^ 40 * 283702 * 2
def baseEnd_283702 : Nat := 64744661618646332586793

theorem tailTrace_283702 : CollatzResearch.WordTrace tailWord_283702 prefixEnd_283702 64744661618646332586793 := by
  unfold tailWord_283702
  simp only [CollatzResearch.WordTrace]
  refine ⟨646716376137723830575835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6898308012135720859475573 646716376137723830575835)
  ·
    refine ⟨970074564206585745863753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646716376137723830575835 970074564206585745863753)
    ·
      refine ⟨727555923154939309397815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 970074564206585745863753 727555923154939309397815)
      ·
        refine ⟨1091333884732408964096723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727555923154939309397815 1091333884732408964096723)
        ·
          refine ⟨1637000827098613446145085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091333884732408964096723 1637000827098613446145085)
          ·
            refine ⟨613875310161980042304407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1637000827098613446145085 613875310161980042304407)
            ·
              refine ⟨920812965242970063456611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613875310161980042304407 920812965242970063456611)
              ·
                refine ⟨1381219447864455095184917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920812965242970063456611 1381219447864455095184917)
                ·
                  refine ⟨64744661618646332586793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1381219447864455095184917 64744661618646332586793)
                  ·
                    rfl

theorem cell21_283702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_283702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283702 prefixEnd_283702 := by exact prefixLift 283702
  have htrace : WordTrace (prefixWord ++ tailWord_283702) baseStart_283702 baseEnd_283702 := by
    simpa [prefixWord, tailWord_283702, baseEnd_283702] using wordTrace_append hprefix tailTrace_283702
  have hstable : (prefixWord ++ tailWord_283702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283702).length < 2 ^ (prefixWord ++ tailWord_283702).sum := by decide
  have hdescent : baseEnd_283702 < baseStart_283702 := by decide
  rcases family_descends (prefixWord ++ tailWord_283702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283744 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_283744 : Nat := 118140960795 + 283744 * 2 ^ 59
def prefixEnd_283744 : Nat := 4983230072969 + 3 ^ 40 * 283744 * 2
def baseEnd_283744 : Nat := 64754246590863592886707

theorem tailTrace_283744 : CollatzResearch.WordTrace tailWord_283744 prefixEnd_283744 64754246590863592886707 := by
  unfold tailWord_283744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174496942025711231121143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6899329256034281641494857 5174496942025711231121143)
  ·
    refine ⟨7761745413038566846681715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174496942025711231121143 7761745413038566846681715)
    ·
      refine ⟨11642618119557850270022573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761745413038566846681715 11642618119557850270022573)
      ·
        refine ⟨4365981794834193851258465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11642618119557850270022573 4365981794834193851258465)
        ·
          refine ⟨3274486346125645388443849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365981794834193851258465 3274486346125645388443849)
          ·
            refine ⟨2455864759594234041332887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274486346125645388443849 2455864759594234041332887)
            ·
              refine ⟨3683797139391351061999331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455864759594234041332887 3683797139391351061999331)
              ·
                refine ⟨5525695709087026592998997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683797139391351061999331 5525695709087026592998997)
                ·
                  refine ⟨64754246590863592886707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5525695709087026592998997 64754246590863592886707)
                  ·
                    rfl

theorem cell21_283744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_283744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283744 prefixEnd_283744 := by exact prefixLift 283744
  have htrace : WordTrace (prefixWord ++ tailWord_283744) baseStart_283744 baseEnd_283744 := by
    simpa [prefixWord, tailWord_283744, baseEnd_283744] using wordTrace_append hprefix tailTrace_283744
  have hstable : (prefixWord ++ tailWord_283744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283744).length < 2 ^ (prefixWord ++ tailWord_283744).sum := by decide
  have hdescent : baseEnd_283744 < baseStart_283744 := by decide
  rcases family_descends (prefixWord ++ tailWord_283744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283837 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_283837 : Nat := 118140960795 + 283837 * 2 ^ 59
def prefixEnd_283837 : Nat := 4983230072969 + 3 ^ 40 * 283837 * 2
def baseEnd_283837 : Nat := 64775470457916097836517

theorem tailTrace_283837 : CollatzResearch.WordTrace tailWord_283837 prefixEnd_283837 64775470457916097836517 := by
  unfold tailWord_283837
  simp only [CollatzResearch.WordTrace]
  refine ⟨10352385872714499345377765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6901590581809666230251843 10352385872714499345377765)
  ·
    refine ⟨1941072351133968627258331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10352385872714499345377765 1941072351133968627258331)
    ·
      refine ⟨2911608526700952940887497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941072351133968627258331 2911608526700952940887497)
      ·
        refine ⟨2183706395025714705665623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2911608526700952940887497 2183706395025714705665623)
        ·
          refine ⟨3275559592538572058498435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183706395025714705665623 3275559592538572058498435)
          ·
            refine ⟨4913339388807858087747653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275559592538572058498435 4913339388807858087747653)
            ·
              refine ⟨921251135401473391452685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4913339388807858087747653 921251135401473391452685)
              ·
                refine ⟨345469175775552521794757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 921251135401473391452685 345469175775552521794757)
                ·
                  refine ⟨64775470457916097836517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345469175775552521794757 64775470457916097836517)
                  ·
                    rfl

theorem cell21_283837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_283837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283837 prefixEnd_283837 := by exact prefixLift 283837
  have htrace : WordTrace (prefixWord ++ tailWord_283837) baseStart_283837 baseEnd_283837 := by
    simpa [prefixWord, tailWord_283837, baseEnd_283837] using wordTrace_append hprefix tailTrace_283837
  have hstable : (prefixWord ++ tailWord_283837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283837).length < 2 ^ (prefixWord ++ tailWord_283837).sum := by decide
  have hdescent : baseEnd_283837 < baseStart_283837 := by decide
  rcases family_descends (prefixWord ++ tailWord_283837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283865 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_283865 : Nat := 118140960795 + 283865 * 2 ^ 59
def prefixEnd_283865 : Nat := 4983230072969 + 3 ^ 40 * 283865 * 2
def baseEnd_283865 : Nat := 64781860439394271369793

theorem tailTrace_283865 : CollatzResearch.WordTrace tailWord_283865 prefixEnd_283865 64781860439394271369793 := by
  unfold tailWord_283865
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353407116613060127397049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6902271411075373418264699 10353407116613060127397049)
  ·
    refine ⟨7765055337459795095547787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10353407116613060127397049 7765055337459795095547787)
    ·
      refine ⟨11647583006189692643321681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7765055337459795095547787 11647583006189692643321681)
      ·
        refine ⟨8735687254642269482491261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11647583006189692643321681 8735687254642269482491261)
        ·
          refine ⟨3275882720490851055934223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735687254642269482491261 3275882720490851055934223)
          ·
            refine ⟨4913824080736276583901335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275882720490851055934223 4913824080736276583901335)
            ·
              refine ⟨7370736121104414875852003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913824080736276583901335 7370736121104414875852003)
              ·
                refine ⟨11056104181656622313778005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370736121104414875852003 11056104181656622313778005)
                ·
                  refine ⟨64781860439394271369793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11056104181656622313778005 64781860439394271369793)
                  ·
                    rfl

theorem cell21_283865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_283865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283865 prefixEnd_283865 := by exact prefixLift 283865
  have htrace : WordTrace (prefixWord ++ tailWord_283865) baseStart_283865 baseEnd_283865 := by
    simpa [prefixWord, tailWord_283865, baseEnd_283865] using wordTrace_append hprefix tailTrace_283865
  have hstable : (prefixWord ++ tailWord_283865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283865).length < 2 ^ (prefixWord ++ tailWord_283865).sum := by decide
  have hdescent : baseEnd_283865 < baseStart_283865 := by decide
  rcases family_descends (prefixWord ++ tailWord_283865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283882 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_283882 : Nat := 118140960795 + 283882 * 2 ^ 59
def prefixEnd_283882 : Nat := 4983230072969 + 3 ^ 40 * 283882 * 2
def baseEnd_283882 : Nat := 64785740071006019586425

theorem tailTrace_283882 : CollatzResearch.WordTrace tailWord_283882 prefixEnd_283882 64785740071006019586425 := by
  unfold tailWord_283882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588506789387868007691475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6902684771700981353843933 2588506789387868007691475)
  ·
    refine ⟨3882760184081802011537213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588506789387868007691475 3882760184081802011537213)
    ·
      refine ⟨1456035069030675754326455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3882760184081802011537213 1456035069030675754326455)
      ·
        refine ⟨2184052603546013631489683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456035069030675754326455 2184052603546013631489683)
        ·
          refine ⟨3276078905319020447234525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184052603546013631489683 3276078905319020447234525)
          ·
            refine ⟨1228529589494632667712947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3276078905319020447234525 1228529589494632667712947)
            ·
              refine ⟨1842794384241949001569421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228529589494632667712947 1842794384241949001569421)
              ·
                refine ⟨691047894090730875588533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842794384241949001569421 691047894090730875588533)
                ·
                  refine ⟨64785740071006019586425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 691047894090730875588533 64785740071006019586425)
                  ·
                    rfl

theorem cell21_283882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_283882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283882 prefixEnd_283882 := by exact prefixLift 283882
  have htrace : WordTrace (prefixWord ++ tailWord_283882) baseStart_283882 baseEnd_283882 := by
    simpa [prefixWord, tailWord_283882, baseEnd_283882] using wordTrace_append hprefix tailTrace_283882
  have hstable : (prefixWord ++ tailWord_283882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283882).length < 2 ^ (prefixWord ++ tailWord_283882).sum := by decide
  have hdescent : baseEnd_283882 < baseStart_283882 := by decide
  rcases family_descends (prefixWord ++ tailWord_283882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283916 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_283916 : Nat := 118140960795 + 283916 * 2 ^ 59
def prefixEnd_283916 : Nat := 4983230072969 + 3 ^ 40 * 283916 * 2
def baseEnd_283916 : Nat := 64793499334229516019689

theorem tailTrace_283916 : CollatzResearch.WordTrace tailWord_283916 prefixEnd_283916 64793499334229516019689 := by
  unfold tailWord_283916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177633619714147918751801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6903511492952197225002401 5177633619714147918751801)
  ·
    refine ⟨3883225214785610939063851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5177633619714147918751801 3883225214785610939063851)
    ·
      refine ⟨5824837822178416408595777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883225214785610939063851 5824837822178416408595777)
      ·
        refine ⟨4368628366633812306446833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824837822178416408595777 4368628366633812306446833)
        ·
          refine ⟨3276471274975359229835125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368628366633812306446833 3276471274975359229835125)
          ·
            refine ⟨307169182028939927797043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3276471274975359229835125 307169182028939927797043)
            ·
              refine ⟨460753773043409891695565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307169182028939927797043 460753773043409891695565)
              ·
                refine ⟨172782664891278709385837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 460753773043409891695565 172782664891278709385837)
                ·
                  refine ⟨64793499334229516019689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172782664891278709385837 64793499334229516019689)
                  ·
                    rfl

theorem cell21_283916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_283916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283916 prefixEnd_283916 := by exact prefixLift 283916
  have htrace : WordTrace (prefixWord ++ tailWord_283916) baseStart_283916 baseEnd_283916 := by
    simpa [prefixWord, tailWord_283916, baseEnd_283916] using wordTrace_append hprefix tailTrace_283916
  have hstable : (prefixWord ++ tailWord_283916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283916).length < 2 ^ (prefixWord ++ tailWord_283916).sum := by decide
  have hdescent : baseEnd_283916 < baseStart_283916 := by decide
  rcases family_descends (prefixWord ++ tailWord_283916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283933 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 3]
def baseStart_283933 : Nat := 118140960795 + 283933 * 2 ^ 59
def prefixEnd_283933 : Nat := 4983230072969 + 3 ^ 40 * 283933 * 2
def baseEnd_283933 : Nat := 64797378965841264236321

theorem tailTrace_283933 : CollatzResearch.WordTrace tailWord_283933 prefixEnd_283933 64797378965841264236321 := by
  unfold tailWord_283933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355887280366707740872453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6903924853577805160581635 10355887280366707740872453)
  ·
    refine ⟨1941728865068757701413585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10355887280366707740872453 1941728865068757701413585)
    ·
      refine ⟨1456296648801568276060189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1941728865068757701413585 1456296648801568276060189)
      ·
        refine ⟨546111243300588103522571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1456296648801568276060189 546111243300588103522571)
        ·
          refine ⟨819166864950882155283857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546111243300588103522571 819166864950882155283857)
          ·
            refine ⟨614375148713161616462893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819166864950882155283857 614375148713161616462893)
            ·
              refine ⟨230390680767435606173585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614375148713161616462893 230390680767435606173585)
              ·
                refine ⟨172793010575576704630189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230390680767435606173585 172793010575576704630189)
                ·
                  refine ⟨64797378965841264236321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172793010575576704630189 64797378965841264236321)
                  ·
                    rfl

theorem cell21_283933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_283933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283933 prefixEnd_283933 := by exact prefixLift 283933
  have htrace : WordTrace (prefixWord ++ tailWord_283933) baseStart_283933 baseEnd_283933 := by
    simpa [prefixWord, tailWord_283933, baseEnd_283933] using wordTrace_append hprefix tailTrace_283933
  have hstable : (prefixWord ++ tailWord_283933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283933).length < 2 ^ (prefixWord ++ tailWord_283933).sum := by decide
  have hdescent : baseEnd_283933 < baseStart_283933 := by decide
  rcases family_descends (prefixWord ++ tailWord_283933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283944 : List Nat := [2, 1, 5, 1, 2, 2, 2, 6]
def baseStart_283944 : Nat := 118140960795 + 283944 * 2 ^ 59
def prefixEnd_283944 : Nat := 4983230072969 + 3 ^ 40 * 283944 * 2
def baseEnd_283944 : Nat := 21599963105235896517655

theorem tailTrace_283944 : CollatzResearch.WordTrace tailWord_283944 prefixEnd_283944 21599963105235896517655 := by
  unfold tailWord_283944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178144241663428309761443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6904192322217904413015257 5178144241663428309761443)
  ·
    refine ⟨7767216362495142464642165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178144241663428309761443 7767216362495142464642165)
    ·
      refine ⟨728176533983919606060203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7767216362495142464642165 728176533983919606060203)
      ·
        refine ⟨1092264800975879409090305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728176533983919606060203 1092264800975879409090305)
        ·
          refine ⟨819198600731909556817729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092264800975879409090305 819198600731909556817729)
          ·
            refine ⟨614398950548932167613297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819198600731909556817729 614398950548932167613297)
            ·
              refine ⟨460799212911699125709973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614398950548932167613297 460799212911699125709973)
              ·
                refine ⟨21599963105235896517655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 460799212911699125709973 21599963105235896517655)
                ·
                  rfl

theorem cell21_283944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_283944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283944 prefixEnd_283944 := by exact prefixLift 283944
  have htrace : WordTrace (prefixWord ++ tailWord_283944) baseStart_283944 baseEnd_283944 := by
    simpa [prefixWord, tailWord_283944, baseEnd_283944] using wordTrace_append hprefix tailTrace_283944
  have hstable : (prefixWord ++ tailWord_283944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283944).length < 2 ^ (prefixWord ++ tailWord_283944).sum := by decide
  have hdescent : baseEnd_283944 < baseStart_283944 := by decide
  rcases family_descends (prefixWord ++ tailWord_283944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283989 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_283989 : Nat := 118140960795 + 283989 * 2 ^ 59
def prefixEnd_283989 : Nat := 4983230072969 + 3 ^ 40 * 283989 * 2
def baseEnd_283989 : Nat := 64810158928797611302873

theorem tailTrace_283989 : CollatzResearch.WordTrace tailWord_283989 prefixEnd_283989 64810158928797611302873 := by
  unfold tailWord_283989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357929768163829304911021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6905286512109219536607347 10357929768163829304911021)
  ·
    refine ⟨3884223663061435989341633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10357929768163829304911021 3884223663061435989341633)
    ·
      refine ⟨2913167747296076992006225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3884223663061435989341633 2913167747296076992006225)
      ·
        refine ⟨2184875810472057744004669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913167747296076992006225 2184875810472057744004669)
        ·
          refine ⟨819328428927021654001751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2184875810472057744004669 819328428927021654001751)
          ·
            refine ⟨1228992643390532481002627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819328428927021654001751 1228992643390532481002627)
            ·
              refine ⟨1843488965085798721503941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228992643390532481002627 1843488965085798721503941)
              ·
                refine ⟨345654180953587260281989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1843488965085798721503941 345654180953587260281989)
                ·
                  refine ⟨64810158928797611302873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345654180953587260281989 64810158928797611302873)
                  ·
                    rfl

theorem cell21_283989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_283989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_283989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_283989 prefixEnd_283989 := by exact prefixLift 283989
  have htrace : WordTrace (prefixWord ++ tailWord_283989) baseStart_283989 baseEnd_283989 := by
    simpa [prefixWord, tailWord_283989, baseEnd_283989] using wordTrace_append hprefix tailTrace_283989
  have hstable : (prefixWord ++ tailWord_283989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283989).length < 2 ^ (prefixWord ++ tailWord_283989).sum := by decide
  have hdescent : baseEnd_283989 < baseStart_283989 := by decide
  rcases family_descends (prefixWord ++ tailWord_283989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284003 : List Nat := [1, 1, 1, 5, 2, 2, 3, 6]
def baseStart_284003 : Nat := 118140960795 + 284003 * 2 ^ 59
def prefixEnd_284003 : Nat := 4983230072969 + 3 ^ 40 * 284003 * 2
def baseEnd_284003 : Nat := 21604451306512232689837

theorem tailTrace_284003 : CollatzResearch.WordTrace tailWord_284003 prefixEnd_284003 21604451306512232689837 := by
  unfold tailWord_284003
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358440390113109695920663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6905626926742073130613775 10358440390113109695920663)
  ·
    refine ⟨15537660585169664543880995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10358440390113109695920663 15537660585169664543880995)
    ·
      refine ⟨23306490877754496815821493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15537660585169664543880995 23306490877754496815821493)
      ·
        refine ⟨2184983519789484076483265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23306490877754496815821493 2184983519789484076483265)
        ·
          refine ⟨1638737639842113057362449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184983519789484076483265 1638737639842113057362449)
          ·
            refine ⟨1229053229881584793021837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1638737639842113057362449 1229053229881584793021837)
            ·
              refine ⟨460894961205594297383189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1229053229881584793021837 460894961205594297383189)
              ·
                refine ⟨21604451306512232689837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 460894961205594297383189 21604451306512232689837)
                ·
                  rfl

theorem cell21_284003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_284003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284003 prefixEnd_284003 := by exact prefixLift 284003
  have htrace : WordTrace (prefixWord ++ tailWord_284003) baseStart_284003 baseEnd_284003 := by
    simpa [prefixWord, tailWord_284003, baseEnd_284003] using wordTrace_append hprefix tailTrace_284003
  have hstable : (prefixWord ++ tailWord_284003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284003).length < 2 ^ (prefixWord ++ tailWord_284003).sum := by decide
  have hdescent : baseEnd_284003 < baseStart_284003 := by decide
  rcases family_descends (prefixWord ++ tailWord_284003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284017 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_284017 : Nat := 118140960795 + 284017 * 2 ^ 59
def prefixEnd_284017 : Nat := 4983230072969 + 3 ^ 40 * 284017 * 2
def baseEnd_284017 : Nat := 64816548910275784836149

theorem tailTrace_284017 : CollatzResearch.WordTrace tailWord_284017 prefixEnd_284017 64816548910275784836149 := by
  unfold tailWord_284017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358951012062390086930305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6905967341374926724620203 10358951012062390086930305)
  ·
    refine ⟨7769213259046792565197729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10358951012062390086930305 7769213259046792565197729)
    ·
      refine ⟨5826909944285094423898297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7769213259046792565197729 5826909944285094423898297)
      ·
        refine ⟨4370182458213820817923723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5826909944285094423898297 4370182458213820817923723)
        ·
          refine ⟨6555273687320731226885585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370182458213820817923723 6555273687320731226885585)
          ·
            refine ⟨4916455265490548420164189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555273687320731226885585 4916455265490548420164189)
            ·
              refine ⟨1843670724558955657561571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4916455265490548420164189 1843670724558955657561571)
              ·
                refine ⟨2765506086838433486342357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843670724558955657561571 2765506086838433486342357)
                ·
                  refine ⟨64816548910275784836149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2765506086838433486342357 64816548910275784836149)
                  ·
                    rfl

theorem cell21_284017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_284017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284017 prefixEnd_284017 := by exact prefixLift 284017
  have htrace : WordTrace (prefixWord ++ tailWord_284017) baseStart_284017 baseEnd_284017 := by
    simpa [prefixWord, tailWord_284017, baseEnd_284017] using wordTrace_append hprefix tailTrace_284017
  have hstable : (prefixWord ++ tailWord_284017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284017).length < 2 ^ (prefixWord ++ tailWord_284017).sum := by decide
  have hdescent : baseEnd_284017 < baseStart_284017 := by decide
  rcases family_descends (prefixWord ++ tailWord_284017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284110 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_284110 : Nat := 118140960795 + 284110 * 2 ^ 59
def prefixEnd_284110 : Nat := 4983230072969 + 3 ^ 40 * 284110 * 2
def baseEnd_284110 : Nat := 64837772777328289785959

theorem tailTrace_284110 : CollatzResearch.WordTrace tailWord_284110 prefixEnd_284110 64837772777328289785959 := by
  unfold tailWord_284110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295292875090683371258223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6908228667150311313377189 1295292875090683371258223)
  ·
    refine ⟨1942939312636025056887335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1295292875090683371258223 1942939312636025056887335)
    ·
      refine ⟨2914408968954037585331003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942939312636025056887335 2914408968954037585331003)
      ·
        refine ⟨4371613453431056377996505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914408968954037585331003 4371613453431056377996505)
        ·
          refine ⟨3278710090073292283497379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4371613453431056377996505 3278710090073292283497379)
          ·
            refine ⟨4918065135109938425246069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278710090073292283497379 4918065135109938425246069)
            ·
              refine ⟨461068606416556727366819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4918065135109938425246069 461068606416556727366819)
              ·
                refine ⟨691602909624835091050229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461068606416556727366819 691602909624835091050229)
                ·
                  refine ⟨64837772777328289785959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 691602909624835091050229 64837772777328289785959)
                  ·
                    rfl

theorem cell21_284110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_284110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284110 prefixEnd_284110 := by exact prefixLift 284110
  have htrace : WordTrace (prefixWord ++ tailWord_284110) baseStart_284110 baseEnd_284110 := by
    simpa [prefixWord, tailWord_284110, baseEnd_284110] using wordTrace_append hprefix tailTrace_284110
  have hstable : (prefixWord ++ tailWord_284110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284110).length < 2 ^ (prefixWord ++ tailWord_284110).sum := by decide
  have hdescent : baseEnd_284110 < baseStart_284110 := by decide
  rcases family_descends (prefixWord ++ tailWord_284110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284116 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_284116 : Nat := 118140960795 + 284116 * 2 ^ 59
def prefixEnd_284116 : Nat := 4983230072969 + 3 ^ 40 * 284116 * 2
def baseEnd_284116 : Nat := 64839142059073612685947

theorem tailTrace_284116 : CollatzResearch.WordTrace tailWord_284116 prefixEnd_284116 64839142059073612685947 := by
  unfold tailWord_284116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181280919351864997392101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6908374559135819996522801 5181280919351864997392101)
  ·
    refine ⟨971490172378474687011019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5181280919351864997392101 971490172378474687011019)
    ·
      refine ⟨1457235258567712030516529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971490172378474687011019 1457235258567712030516529)
      ·
        refine ⟨1092926443925784022887397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1457235258567712030516529 1092926443925784022887397)
        ·
          refine ⟨204923708236084504291387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1092926443925784022887397 204923708236084504291387)
          ·
            refine ⟨307385562354126756437081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204923708236084504291387 307385562354126756437081)
            ·
              refine ⟨230539171765595067327811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307385562354126756437081 230539171765595067327811)
              ·
                refine ⟨345808757648392600991717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230539171765595067327811 345808757648392600991717)
                ·
                  refine ⟨64839142059073612685947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345808757648392600991717 64839142059073612685947)
                  ·
                    rfl

theorem cell21_284116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_284116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284116 prefixEnd_284116 := by exact prefixLift 284116
  have htrace : WordTrace (prefixWord ++ tailWord_284116) baseStart_284116 baseEnd_284116 := by
    simpa [prefixWord, tailWord_284116, baseEnd_284116] using wordTrace_append hprefix tailTrace_284116
  have hstable : (prefixWord ++ tailWord_284116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284116).length < 2 ^ (prefixWord ++ tailWord_284116).sum := by decide
  have hdescent : baseEnd_284116 < baseStart_284116 := by decide
  rcases family_descends (prefixWord ++ tailWord_284116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284161 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 3]
def baseStart_284161 : Nat := 118140960795 + 284161 * 2 ^ 59
def prefixEnd_284161 : Nat := 4983230072969 + 3 ^ 40 * 284161 * 2
def baseEnd_284161 : Nat := 64849411672163534435855

theorem tailTrace_284161 : CollatzResearch.WordTrace tailWord_284161 prefixEnd_284161 64849411672163534435855 := by
  unfold tailWord_284161
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364203123540702680172337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6909468749027135120114891 10364203123540702680172337)
  ·
    refine ⟨7773152342655527010129253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10364203123540702680172337 7773152342655527010129253)
    ·
      refine ⟨1457466064247911314399235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7773152342655527010129253 1457466064247911314399235)
      ·
        refine ⟨2186199096371866971598853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457466064247911314399235 2186199096371866971598853)
        ·
          refine ⟨409912330569725057174785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2186199096371866971598853 409912330569725057174785)
          ·
            refine ⟨307434247927293792881089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409912330569725057174785 307434247927293792881089)
            ·
              refine ⟨230575685945470344660817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307434247927293792881089 230575685945470344660817)
              ·
                refine ⟨172931764459102758495613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230575685945470344660817 172931764459102758495613)
                ·
                  refine ⟨64849411672163534435855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172931764459102758495613 64849411672163534435855)
                  ·
                    rfl

theorem cell21_284161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_284161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284161 prefixEnd_284161 := by exact prefixLift 284161
  have htrace : WordTrace (prefixWord ++ tailWord_284161) baseStart_284161 baseEnd_284161 := by
    simpa [prefixWord, tailWord_284161, baseEnd_284161] using wordTrace_append hprefix tailTrace_284161
  have hstable : (prefixWord ++ tailWord_284161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284161).length < 2 ^ (prefixWord ++ tailWord_284161).sum := by decide
  have hdescent : baseEnd_284161 < baseStart_284161 := by decide
  rcases family_descends (prefixWord ++ tailWord_284161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284169 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_284169 : Nat := 118140960795 + 284169 * 2 ^ 59
def prefixEnd_284169 : Nat := 4983230072969 + 3 ^ 40 * 284169 * 2
def baseEnd_284169 : Nat := 64851237381157298302505

theorem tailTrace_284169 : CollatzResearch.WordTrace tailWord_284169 prefixEnd_284169 64851237381157298302505 := by
  unfold tailWord_284169
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364494907511720046463561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6909663271674480030975707 10364494907511720046463561)
  ·
    refine ⟨7773371180633790034847671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10364494907511720046463561 7773371180633790034847671)
    ·
      refine ⟨11660056770950685052271507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7773371180633790034847671 11660056770950685052271507)
      ·
        refine ⟨17490085156426027578407261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660056770950685052271507 17490085156426027578407261)
        ·
          refine ⟨6558781933659760341902723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17490085156426027578407261 6558781933659760341902723)
          ·
            refine ⟨9838172900489640512854085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558781933659760341902723 9838172900489640512854085)
            ·
              refine ⟨1844657418841807596160141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9838172900489640512854085 1844657418841807596160141)
              ·
                refine ⟨691746532065677848560053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1844657418841807596160141 691746532065677848560053)
                ·
                  refine ⟨64851237381157298302505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 691746532065677848560053 64851237381157298302505)
                  ·
                    rfl

theorem cell21_284169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_284169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284169 prefixEnd_284169 := by exact prefixLift 284169
  have htrace : WordTrace (prefixWord ++ tailWord_284169) baseStart_284169 baseEnd_284169 := by
    simpa [prefixWord, tailWord_284169, baseEnd_284169] using wordTrace_append hprefix tailTrace_284169
  have hstable : (prefixWord ++ tailWord_284169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284169).length < 2 ^ (prefixWord ++ tailWord_284169).sum := by decide
  have hdescent : baseEnd_284169 < baseStart_284169 := by decide
  rcases family_descends (prefixWord ++ tailWord_284169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284172 : List Nat := [2, 2, 1, 2, 5, 2, 1, 6]
def baseStart_284172 : Nat := 118140960795 + 284172 * 2 ^ 59
def prefixEnd_284172 : Nat := 4983230072969 + 3 ^ 40 * 284172 * 2
def baseEnd_284172 : Nat := 21617307340676653250833

theorem tailTrace_284172 : CollatzResearch.WordTrace tailWord_284172 prefixEnd_284172 21617307340676653250833 := by
  unfold tailWord_284172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5182302163250425779411385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6909736217667234372548513 5182302163250425779411385)
  ·
    refine ⟨3886726622437819334558539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5182302163250425779411385 3886726622437819334558539)
    ·
      refine ⟨5830089933656729001837809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886726622437819334558539 5830089933656729001837809)
      ·
        refine ⟨4372567450242546751378357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5830089933656729001837809 4372567450242546751378357)
        ·
          refine ⟨409928198460238757941721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4372567450242546751378357 409928198460238757941721)
          ·
            refine ⟨307446148845179068456291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409928198460238757941721 307446148845179068456291)
            ·
              refine ⟨461169223267768602684437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307446148845179068456291 461169223267768602684437)
              ·
                refine ⟨21617307340676653250833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 461169223267768602684437 21617307340676653250833)
                ·
                  rfl

theorem cell21_284172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_284172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284172 prefixEnd_284172 := by exact prefixLift 284172
  have htrace : WordTrace (prefixWord ++ tailWord_284172) baseStart_284172 baseEnd_284172 := by
    simpa [prefixWord, tailWord_284172, baseEnd_284172] using wordTrace_append hprefix tailTrace_284172
  have hstable : (prefixWord ++ tailWord_284172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284172).length < 2 ^ (prefixWord ++ tailWord_284172).sum := by decide
  have hdescent : baseEnd_284172 < baseStart_284172 := by decide
  rcases family_descends (prefixWord ++ tailWord_284172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284217 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_284217 : Nat := 118140960795 + 284217 * 2 ^ 59
def prefixEnd_284217 : Nat := 4983230072969 + 3 ^ 40 * 284217 * 2
def baseEnd_284217 : Nat := 64862191635119881502407

theorem tailTrace_284217 : CollatzResearch.WordTrace tailWord_284217 prefixEnd_284217 64862191635119881502407 := by
  unfold tailWord_284217
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366245611337824244210905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6910830407558549496140603 10366245611337824244210905)
  ·
    refine ⟨7774684208503368183158179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366245611337824244210905 7774684208503368183158179)
    ·
      refine ⟨11662026312755052274737269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774684208503368183158179 11662026312755052274737269)
      ·
        refine ⟨1093314966820786150756619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11662026312755052274737269 1093314966820786150756619)
        ·
          refine ⟨1639972450231179226134929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093314966820786150756619 1639972450231179226134929)
          ·
            refine ⟨1229979337673384419601197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639972450231179226134929 1229979337673384419601197)
            ·
              refine ⟨461242251627519157350449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1229979337673384419601197 461242251627519157350449)
              ·
                refine ⟨345931688720639368012837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461242251627519157350449 345931688720639368012837)
                ·
                  refine ⟨64862191635119881502407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345931688720639368012837 64862191635119881502407)
                  ·
                    rfl

theorem cell21_284217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_284217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284217 prefixEnd_284217 := by exact prefixLift 284217
  have htrace : WordTrace (prefixWord ++ tailWord_284217) baseStart_284217 baseEnd_284217 := by
    simpa [prefixWord, tailWord_284217, baseEnd_284217] using wordTrace_append hprefix tailTrace_284217
  have hstable : (prefixWord ++ tailWord_284217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284217).length < 2 ^ (prefixWord ++ tailWord_284217).sum := by decide
  have hdescent : baseEnd_284217 < baseStart_284217 := by decide
  rcases family_descends (prefixWord ++ tailWord_284217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284341 : List Nat := [1, 3, 3, 3, 3, 1, 1, 6]
def baseStart_284341 : Nat := 118140960795 + 284341 * 2 ^ 59
def prefixEnd_284341 : Nat := 4983230072969 + 3 ^ 40 * 284341 * 2
def baseEnd_284341 : Nat := 21630163374841073811829

theorem tailTrace_284341 : CollatzResearch.WordTrace tailWord_284341 prefixEnd_284341 21630163374841073811829 := by
  unfold tailWord_284341
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370768262888593421724877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6913845508592395614483251 10370768262888593421724877)
  ·
    refine ⟨3889038098583222533146829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10370768262888593421724877 3889038098583222533146829)
    ·
      refine ⟨1458389286968708449930061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3889038098583222533146829 1458389286968708449930061)
      ·
        refine ⟨546895982613265668723773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1458389286968708449930061 546895982613265668723773)
        ·
          refine ⟨205085993479974625771415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 546895982613265668723773 205085993479974625771415)
          ·
            refine ⟨307628990219961938657123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205085993479974625771415 307628990219961938657123)
            ·
              refine ⟨461443485329942907985685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307628990219961938657123 461443485329942907985685)
              ·
                refine ⟨21630163374841073811829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 461443485329942907985685 21630163374841073811829)
                ·
                  rfl

theorem cell21_284341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 6].length) (baseStart_284341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284341 prefixEnd_284341 := by exact prefixLift 284341
  have htrace : WordTrace (prefixWord ++ tailWord_284341) baseStart_284341 baseEnd_284341 := by
    simpa [prefixWord, tailWord_284341, baseEnd_284341] using wordTrace_append hprefix tailTrace_284341
  have hstable : (prefixWord ++ tailWord_284341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284341).length < 2 ^ (prefixWord ++ tailWord_284341).sum := by decide
  have hdescent : baseEnd_284341 < baseStart_284341 := by decide
  rcases family_descends (prefixWord ++ tailWord_284341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284352 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_284352 : Nat := 118140960795 + 284352 * 2 ^ 59
def prefixEnd_284352 : Nat := 4983230072969 + 3 ^ 40 * 284352 * 2
def baseEnd_284352 : Nat := 64893000474389646752131

theorem tailTrace_284352 : CollatzResearch.WordTrace tailWord_284352 prefixEnd_284352 64893000474389646752131 := by
  unfold tailWord_284352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185584732924371150187655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6914112977232494866916873 5185584732924371150187655)
  ·
    refine ⟨7778377099386556725281483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5185584732924371150187655 7778377099386556725281483)
    ·
      refine ⟨11667565649079835087922225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7778377099386556725281483 11667565649079835087922225)
      ·
        refine ⟨8750674236809876315941669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11667565649079835087922225 8750674236809876315941669)
        ·
          refine ⟨1640751419401851809239063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8750674236809876315941669 1640751419401851809239063)
          ·
            refine ⟨2461127129102777713858595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640751419401851809239063 2461127129102777713858595)
            ·
              refine ⟨3691690693654166570787893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461127129102777713858595 3691690693654166570787893)
              ·
                refine ⟨346096002530078116011365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3691690693654166570787893 346096002530078116011365)
                ·
                  refine ⟨64893000474389646752131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346096002530078116011365 64893000474389646752131)
                  ·
                    rfl

theorem cell21_284352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_284352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284352 prefixEnd_284352 := by exact prefixLift 284352
  have htrace : WordTrace (prefixWord ++ tailWord_284352) baseStart_284352 baseEnd_284352 := by
    simpa [prefixWord, tailWord_284352, baseEnd_284352] using wordTrace_append hprefix tailTrace_284352
  have hstable : (prefixWord ++ tailWord_284352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284352).length < 2 ^ (prefixWord ++ tailWord_284352).sum := by decide
  have hdescent : baseEnd_284352 < baseStart_284352 := by decide
  rcases family_descends (prefixWord ++ tailWord_284352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284358 : List Nat := [6, 1, 2, 1, 1, 2, 3, 5]
def baseStart_284358 : Nat := 118140960795 + 284358 * 2 ^ 59
def prefixEnd_284358 : Nat := 4983230072969 + 3 ^ 40 * 284358 * 2
def baseEnd_284358 : Nat := 21631456585378323217373

theorem tailTrace_284358 : CollatzResearch.WordTrace tailWord_284358 prefixEnd_284358 21631456585378323217373 := by
  unfold tailWord_284358
  simp only [CollatzResearch.WordTrace]
  refine ⟨324105884494593916409179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6914258869218003550062485 324105884494593916409179)
  ·
    refine ⟨486158826741890874613769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 324105884494593916409179 486158826741890874613769)
    ·
      refine ⟨364619120056418155960327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486158826741890874613769 364619120056418155960327)
      ·
        refine ⟨546928680084627233940491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364619120056418155960327 546928680084627233940491)
        ·
          refine ⟨820393020126940850910737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546928680084627233940491 820393020126940850910737)
          ·
            refine ⟨615294765095205638183053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820393020126940850910737 615294765095205638183053)
            ·
              refine ⟨230735536910702114318645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 615294765095205638183053 230735536910702114318645)
              ·
                refine ⟨21631456585378323217373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 230735536910702114318645 21631456585378323217373)
                ·
                  rfl

theorem cell21_284358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_284358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284358 prefixEnd_284358 := by exact prefixLift 284358
  have htrace : WordTrace (prefixWord ++ tailWord_284358) baseStart_284358 baseEnd_284358 := by
    simpa [prefixWord, tailWord_284358, baseEnd_284358] using wordTrace_append hprefix tailTrace_284358
  have hstable : (prefixWord ++ tailWord_284358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284358).length < 2 ^ (prefixWord ++ tailWord_284358).sum := by decide
  have hdescent : baseEnd_284358 < baseStart_284358 := by decide
  rcases family_descends (prefixWord ++ tailWord_284358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284372 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_284372 : Nat := 118140960795 + 284372 * 2 ^ 59
def prefixEnd_284372 : Nat := 4983230072969 + 3 ^ 40 * 284372 * 2
def baseEnd_284372 : Nat := 64897564746874056418757

theorem tailTrace_284372 : CollatzResearch.WordTrace tailWord_284372 prefixEnd_284372 64897564746874056418757 := by
  unfold tailWord_284372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185949462888142858051685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6914599283850857144068913 5185949462888142858051685)
  ·
    refine ⟨972365524291526785884691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5185949462888142858051685 972365524291526785884691)
    ·
      refine ⟨1458548286437290178827037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972365524291526785884691 1458548286437290178827037)
      ·
        refine ⟨546955607413983817060139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1458548286437290178827037 546955607413983817060139)
        ·
          refine ⟨820433411120975725590209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546955607413983817060139 820433411120975725590209)
          ·
            refine ⟨615325058340731794192657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820433411120975725590209 615325058340731794192657)
            ·
              refine ⟨461493793755548845644493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615325058340731794192657 461493793755548845644493)
              ·
                refine ⟨173060172658330817116685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461493793755548845644493 173060172658330817116685)
                ·
                  refine ⟨64897564746874056418757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173060172658330817116685 64897564746874056418757)
                  ·
                    rfl

theorem cell21_284372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_284372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284372 prefixEnd_284372 := by exact prefixLift 284372
  have htrace : WordTrace (prefixWord ++ tailWord_284372) baseStart_284372 baseEnd_284372 := by
    simpa [prefixWord, tailWord_284372, baseEnd_284372] using wordTrace_append hprefix tailTrace_284372
  have hstable : (prefixWord ++ tailWord_284372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284372).length < 2 ^ (prefixWord ++ tailWord_284372).sum := by decide
  have hdescent : baseEnd_284372 < baseStart_284372 := by decide
  rcases family_descends (prefixWord ++ tailWord_284372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284442 : List Nat := [3, 1, 1, 3, 2, 2, 9]
def baseStart_284442 : Nat := 118140960795 + 284442 * 2 ^ 59
def prefixEnd_284442 : Nat := 4983230072969 + 3 ^ 40 * 284442 * 2
def baseEnd_284442 : Nat := 7212615522285498916883

theorem tailTrace_284442 : CollatzResearch.WordTrace tailWord_284442 prefixEnd_284442 7212615522285498916883 := by
  unfold tailWord_284442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593613008880671917787895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6916301357015125114101053 2593613008880671917787895)
  ·
    refine ⟨3890419513321007876681843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2593613008880671917787895 3890419513321007876681843)
    ·
      refine ⟨5835629269981511815022765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890419513321007876681843 5835629269981511815022765)
      ·
        refine ⟨2188360976243066930633537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5835629269981511815022765 2188360976243066930633537)
        ·
          refine ⟨1641270732182300197975153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188360976243066930633537 1641270732182300197975153)
          ·
            refine ⟨1230953049136725148481365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641270732182300197975153 1230953049136725148481365)
            ·
              refine ⟨7212615522285498916883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1230953049136725148481365 7212615522285498916883)
              ·
                rfl

theorem cell21_284442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 9].length) (baseStart_284442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284442 prefixEnd_284442 := by exact prefixLift 284442
  have htrace : WordTrace (prefixWord ++ tailWord_284442) baseStart_284442 baseEnd_284442 := by
    simpa [prefixWord, tailWord_284442, baseEnd_284442] using wordTrace_append hprefix tailTrace_284442
  have hstable : (prefixWord ++ tailWord_284442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284442).length < 2 ^ (prefixWord ++ tailWord_284442).sum := by decide
  have hdescent : baseEnd_284442 < baseStart_284442 := by decide
  rcases family_descends (prefixWord ++ tailWord_284442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284462 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_284462 : Nat := 118140960795 + 284462 * 2 ^ 59
def prefixEnd_284462 : Nat := 4983230072969 + 3 ^ 40 * 284462 * 2
def baseEnd_284462 : Nat := 64918103973053899918573

theorem tailTrace_284462 : CollatzResearch.WordTrace tailWord_284462 prefixEnd_284462 64918103973053899918573 := by
  unfold tailWord_284462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296897686931278885859955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6916787663633487391253093 1296897686931278885859955)
  ·
    refine ⟨1945346530396918328789933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296897686931278885859955 1945346530396918328789933)
    ·
      refine ⟨729504948898844373296225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1945346530396918328789933 729504948898844373296225)
      ·
        refine ⟨547128711674133279972169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 729504948898844373296225 547128711674133279972169)
        ·
          refine ⟨410346533755599959979127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547128711674133279972169 410346533755599959979127)
          ·
            refine ⟨615519800633399939968691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410346533755599959979127 615519800633399939968691)
            ·
              refine ⟨923279700950099909953037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615519800633399939968691 923279700950099909953037)
              ·
                refine ⟨346229887856287466232389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 923279700950099909953037 346229887856287466232389)
                ·
                  refine ⟨64918103973053899918573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346229887856287466232389 64918103973053899918573)
                  ·
                    rfl

theorem cell21_284462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_284462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284462 prefixEnd_284462 := by exact prefixLift 284462
  have htrace : WordTrace (prefixWord ++ tailWord_284462) baseStart_284462 baseEnd_284462 := by
    simpa [prefixWord, tailWord_284462, baseEnd_284462] using wordTrace_append hprefix tailTrace_284462
  have hstable : (prefixWord ++ tailWord_284462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284462).length < 2 ^ (prefixWord ++ tailWord_284462).sum := by decide
  have hdescent : baseEnd_284462 < baseStart_284462 := by decide
  rcases family_descends (prefixWord ++ tailWord_284462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284487 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_284487 : Nat := 118140960795 + 284487 * 2 ^ 59
def prefixEnd_284487 : Nat := 4983230072969 + 3 ^ 40 * 284487 * 2
def baseEnd_284487 : Nat := 64923809313659412001855

theorem tailTrace_284487 : CollatzResearch.WordTrace tailWord_284487 prefixEnd_284487 64923809313659412001855 := by
  unfold tailWord_284487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376093320359660356539715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6917395546906440237693143 10376093320359660356539715)
  ·
    refine ⟨15564139980539490534809573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10376093320359660356539715 15564139980539490534809573)
    ·
      refine ⟨2918276246351154475276795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15564139980539490534809573 2918276246351154475276795)
      ·
        refine ⟨4377414369526731712915193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918276246351154475276795 4377414369526731712915193)
        ·
          refine ⟨3283060777145048784686395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4377414369526731712915193 3283060777145048784686395)
          ·
            refine ⟨4924591165717573177029593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283060777145048784686395 4924591165717573177029593)
            ·
              refine ⟨3693443374288179882772195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924591165717573177029593 3693443374288179882772195)
              ·
                refine ⟨5540165061432269824158293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693443374288179882772195 5540165061432269824158293)
                ·
                  refine ⟨64923809313659412001855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5540165061432269824158293 64923809313659412001855)
                  ·
                    rfl

theorem cell21_284487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_284487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284487 prefixEnd_284487 := by exact prefixLift 284487
  have htrace : WordTrace (prefixWord ++ tailWord_284487) baseStart_284487 baseEnd_284487 := by
    simpa [prefixWord, tailWord_284487, baseEnd_284487] using wordTrace_append hprefix tailTrace_284487
  have hstable : (prefixWord ++ tailWord_284487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284487).length < 2 ^ (prefixWord ++ tailWord_284487).sum := by decide
  have hdescent : baseEnd_284487 < baseStart_284487 := by decide
  rcases family_descends (prefixWord ++ tailWord_284487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284490 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_284490 : Nat := 118140960795 + 284490 * 2 ^ 59
def prefixEnd_284490 : Nat := 4983230072969 + 3 ^ 40 * 284490 * 2
def baseEnd_284490 : Nat := 64924493954532073451849

theorem tailTrace_284490 : CollatzResearch.WordTrace tailWord_284490 prefixEnd_284490 64924493954532073451849 := by
  unfold tailWord_284490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594050684837197967224731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6917468492899194579265949 2594050684837197967224731)
  ·
    refine ⟨3891076027255796950837097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2594050684837197967224731 3891076027255796950837097)
    ·
      refine ⟨2918307020441847713127823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3891076027255796950837097 2918307020441847713127823)
      ·
        refine ⟨4377460530662771569691735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918307020441847713127823 4377460530662771569691735)
        ·
          refine ⟨6566190795994157354537603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377460530662771569691735 6566190795994157354537603)
          ·
            refine ⟨9849286193991236031806405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566190795994157354537603 9849286193991236031806405)
            ·
              refine ⟨1846741161373356755963701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9849286193991236031806405 1846741161373356755963701)
              ·
                refine ⟨173131983878752195871597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1846741161373356755963701 173131983878752195871597)
                ·
                  refine ⟨64924493954532073451849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173131983878752195871597 64924493954532073451849)
                  ·
                    rfl

theorem cell21_284490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_284490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284490 prefixEnd_284490 := by exact prefixLift 284490
  have htrace : WordTrace (prefixWord ++ tailWord_284490) baseStart_284490 baseEnd_284490 := by
    simpa [prefixWord, tailWord_284490, baseEnd_284490] using wordTrace_append hprefix tailTrace_284490
  have hstable : (prefixWord ++ tailWord_284490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284490).length < 2 ^ (prefixWord ++ tailWord_284490).sum := by decide
  have hdescent : baseEnd_284490 < baseStart_284490 := by decide
  rcases family_descends (prefixWord ++ tailWord_284490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284676 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_284676 : Nat := 118140960795 + 284676 * 2 ^ 59
def prefixEnd_284676 : Nat := 4983230072969 + 3 ^ 40 * 284676 * 2
def baseEnd_284676 : Nat := 64966941688637083351469

theorem tailTrace_284676 : CollatzResearch.WordTrace tailWord_284676 prefixEnd_284676 64966941688637083351469 := by
  unfold tailWord_284676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5191493358337472817584941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6921991144449963756779921 5191493358337472817584941)
  ·
    refine ⟨1946810009376552306594353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5191493358337472817584941 1946810009376552306594353)
    ·
      refine ⟨1460107507032414229945765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946810009376552306594353 1460107507032414229945765)
      ·
        refine ⟨273770157568577668114831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1460107507032414229945765 273770157568577668114831)
        ·
          refine ⟨410655236352866502172247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273770157568577668114831 410655236352866502172247)
          ·
            refine ⟨615982854529299753258371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410655236352866502172247 615982854529299753258371)
            ·
              refine ⟨923974281793949629887557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615982854529299753258371 923974281793949629887557)
              ·
                refine ⟨173245177836365555603917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 923974281793949629887557 173245177836365555603917)
                ·
                  refine ⟨64966941688637083351469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173245177836365555603917 64966941688637083351469)
                  ·
                    rfl

theorem cell21_284676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_284676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284676 prefixEnd_284676 := by exact prefixLift 284676
  have htrace : WordTrace (prefixWord ++ tailWord_284676) baseStart_284676 baseEnd_284676 := by
    simpa [prefixWord, tailWord_284676, baseEnd_284676] using wordTrace_append hprefix tailTrace_284676
  have hstable : (prefixWord ++ tailWord_284676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284676).length < 2 ^ (prefixWord ++ tailWord_284676).sum := by decide
  have hdescent : baseEnd_284676 < baseStart_284676 := by decide
  rcases family_descends (prefixWord ++ tailWord_284676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284701 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_284701 : Nat := 118140960795 + 284701 * 2 ^ 59
def prefixEnd_284701 : Nat := 4983230072969 + 3 ^ 40 * 284701 * 2
def baseEnd_284701 : Nat := 64972647029242595434751

theorem tailTrace_284701 : CollatzResearch.WordTrace tailWord_284701 prefixEnd_284701 64972647029242595434751 := by
  unfold tailWord_284701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383898541584374904829957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6922599027722916603219971 10383898541584374904829957)
  ·
    refine ⟨1946980976547070294655617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10383898541584374904829957 1946980976547070294655617)
    ·
      refine ⟨1460235732410302720991713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946980976547070294655617 1460235732410302720991713)
      ·
        refine ⟨1095176799307727040743785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460235732410302720991713 1095176799307727040743785)
        ·
          refine ⟨821382599480795280557839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095176799307727040743785 821382599480795280557839)
          ·
            refine ⟨1232073899221192920836759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821382599480795280557839 1232073899221192920836759)
            ·
              refine ⟨1848110848831789381255139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232073899221192920836759 1848110848831789381255139)
              ·
                refine ⟨2772166273247684071882709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848110848831789381255139 2772166273247684071882709)
                ·
                  refine ⟨64972647029242595434751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2772166273247684071882709 64972647029242595434751)
                  ·
                    rfl

theorem cell21_284701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_284701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284701 prefixEnd_284701 := by exact prefixLift 284701
  have htrace : WordTrace (prefixWord ++ tailWord_284701) baseStart_284701 baseEnd_284701 := by
    simpa [prefixWord, tailWord_284701, baseEnd_284701] using wordTrace_append hprefix tailTrace_284701
  have hstable : (prefixWord ++ tailWord_284701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284701).length < 2 ^ (prefixWord ++ tailWord_284701).sum := by decide
  have hdescent : baseEnd_284701 < baseStart_284701 := by decide
  rcases family_descends (prefixWord ++ tailWord_284701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284791 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_284791 : Nat := 118140960795 + 284791 * 2 ^ 59
def prefixEnd_284791 : Nat := 4983230072969 + 3 ^ 40 * 284791 * 2
def baseEnd_284791 : Nat := 64993186255422438934567

theorem tailTrace_284791 : CollatzResearch.WordTrace tailWord_284791 prefixEnd_284791 64993186255422438934567 := by
  unfold tailWord_284791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387181111258320275606227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6924787407505546850404151 10387181111258320275606227)
  ·
    refine ⟨15580771666887480413409341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10387181111258320275606227 15580771666887480413409341)
    ·
      refine ⟨5842789375082805155028503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15580771666887480413409341 5842789375082805155028503)
      ·
        refine ⟨8764184062624207732542755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5842789375082805155028503 8764184062624207732542755)
        ·
          refine ⟨13146276093936311598814133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8764184062624207732542755 13146276093936311598814133)
          ·
            refine ⟨1232463383806529212388825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13146276093936311598814133 1232463383806529212388825)
            ·
              refine ⟨924347537854896909291619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232463383806529212388825 924347537854896909291619)
              ·
                refine ⟨1386521306782345363937429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924347537854896909291619 1386521306782345363937429)
                ·
                  refine ⟨64993186255422438934567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1386521306782345363937429 64993186255422438934567)
                  ·
                    rfl

theorem cell21_284791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_284791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284791 prefixEnd_284791 := by exact prefixLift 284791
  have htrace : WordTrace (prefixWord ++ tailWord_284791) baseStart_284791 baseEnd_284791 := by
    simpa [prefixWord, tailWord_284791, baseEnd_284791] using wordTrace_append hprefix tailTrace_284791
  have hstable : (prefixWord ++ tailWord_284791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284791).length < 2 ^ (prefixWord ++ tailWord_284791).sum := by decide
  have hdescent : baseEnd_284791 < baseStart_284791 := by decide
  rcases family_descends (prefixWord ++ tailWord_284791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284839 : List Nat := [1, 1, 6, 2, 3, 8]
def baseStart_284839 : Nat := 118140960795 + 284839 * 2 ^ 59
def prefixEnd_284839 : Nat := 4983230072969 + 3 ^ 40 * 284839 * 2
def baseEnd_284839 : Nat := 2407560759606852671647

theorem tailTrace_284839 : CollatzResearch.WordTrace tailWord_284839 prefixEnd_284839 2407560759606852671647 := by
  unfold tailWord_284839
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388931815084424473353571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6925954543389616315569047 10388931815084424473353571)
  ·
    refine ⟨15583397722626636710030357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10388931815084424473353571 15583397722626636710030357)
    ·
      refine ⟨730471768248123595782673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15583397722626636710030357 730471768248123595782673)
      ·
        refine ⟨547853826186092696837005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 730471768248123595782673 547853826186092696837005)
        ·
          refine ⟨205445184819784761313877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 547853826186092696837005 205445184819784761313877)
          ·
            refine ⟨2407560759606852671647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 205445184819784761313877 2407560759606852671647)
            ·
              rfl

theorem cell21_284839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 8].length) (baseStart_284839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284839 prefixEnd_284839 := by exact prefixLift 284839
  have htrace : WordTrace (prefixWord ++ tailWord_284839) baseStart_284839 baseEnd_284839 := by
    simpa [prefixWord, tailWord_284839, baseEnd_284839] using wordTrace_append hprefix tailTrace_284839
  have hstable : (prefixWord ++ tailWord_284839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284839).length < 2 ^ (prefixWord ++ tailWord_284839).sum := by decide
  have hdescent : baseEnd_284839 < baseStart_284839 := by decide
  rcases family_descends (prefixWord ++ tailWord_284839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284842 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_284842 : Nat := 118140960795 + 284842 * 2 ^ 59
def prefixEnd_284842 : Nat := 4983230072969 + 3 ^ 40 * 284842 * 2
def baseEnd_284842 : Nat := 65004825150257683584463

theorem tailTrace_284842 : CollatzResearch.WordTrace tailWord_284842 prefixEnd_284842 65004825150257683584463 := by
  unfold tailWord_284842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597260308518388996428195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6926027489382370657141853 2597260308518388996428195)
  ·
    refine ⟨3895890462777583494642293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597260308518388996428195 3895890462777583494642293)
    ·
      refine ⟨365239730885398452622715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3895890462777583494642293 365239730885398452622715)
      ·
        refine ⟨547859596328097678934073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365239730885398452622715 547859596328097678934073)
        ·
          refine ⟨410894697246073259200555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547859596328097678934073 410894697246073259200555)
          ·
            refine ⟨616342045869109888800833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410894697246073259200555 616342045869109888800833)
            ·
              refine ⟨462256534401832416600625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616342045869109888800833 462256534401832416600625)
              ·
                refine ⟨346692400801374312450469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462256534401832416600625 346692400801374312450469)
                ·
                  refine ⟨65004825150257683584463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346692400801374312450469 65004825150257683584463)
                  ·
                    rfl

theorem cell21_284842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_284842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284842 prefixEnd_284842 := by exact prefixLift 284842
  have htrace : WordTrace (prefixWord ++ tailWord_284842) baseStart_284842 baseEnd_284842 := by
    simpa [prefixWord, tailWord_284842, baseEnd_284842] using wordTrace_append hprefix tailTrace_284842
  have hstable : (prefixWord ++ tailWord_284842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284842).length < 2 ^ (prefixWord ++ tailWord_284842).sum := by decide
  have hdescent : baseEnd_284842 < baseStart_284842 := by decide
  rcases family_descends (prefixWord ++ tailWord_284842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284881 : List Nat := [1, 2, 2, 1, 2, 2, 2, 9]
def baseStart_284881 : Nat := 118140960795 + 284881 * 2 ^ 59
def prefixEnd_284881 : Nat := 4983230072969 + 3 ^ 40 * 284881 * 2
def baseEnd_284881 : Nat := 21671241827200760811461

theorem tailTrace_284881 : CollatzResearch.WordTrace tailWord_284881 prefixEnd_284881 21671241827200760811461 := by
  unfold tailWord_284881
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390463680932265646382497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6926975787288177097588331 10390463680932265646382497)
  ·
    refine ⟨7792847760699199234786873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10390463680932265646382497 7792847760699199234786873)
    ·
      refine ⟨5844635820524399426090155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7792847760699199234786873 5844635820524399426090155)
      ·
        refine ⟨8766953730786599139135233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5844635820524399426090155 8766953730786599139135233)
        ·
          refine ⟨6575215298089949354351425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8766953730786599139135233 6575215298089949354351425)
          ·
            refine ⟨4931411473567462015763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6575215298089949354351425 4931411473567462015763569)
            ·
              refine ⟨3698558605175596511822677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931411473567462015763569 3698558605175596511822677)
              ·
                refine ⟨21671241827200760811461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3698558605175596511822677 21671241827200760811461)
                ·
                  rfl

theorem cell21_284881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_284881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284881 prefixEnd_284881 := by exact prefixLift 284881
  have htrace : WordTrace (prefixWord ++ tailWord_284881) baseStart_284881 baseEnd_284881 := by
    simpa [prefixWord, tailWord_284881, baseEnd_284881] using wordTrace_append hprefix tailTrace_284881
  have hstable : (prefixWord ++ tailWord_284881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284881).length < 2 ^ (prefixWord ++ tailWord_284881).sum := by decide
  have hdescent : baseEnd_284881 < baseStart_284881 := by decide
  rcases family_descends (prefixWord ++ tailWord_284881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284901 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 4]
def baseStart_284901 : Nat := 118140960795 + 284901 * 2 ^ 59
def prefixEnd_284901 : Nat := 4983230072969 + 3 ^ 40 * 284901 * 2
def baseEnd_284901 : Nat := 65018289754086692101009

theorem tailTrace_284901 : CollatzResearch.WordTrace tailWord_284901 prefixEnd_284901 65018289754086692101009 := by
  unfold tailWord_284901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391193140859809062110557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6927462093906539374740371 10391193140859809062110557)
  ·
    refine ⟨3896697427822428398291459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10391193140859809062110557 3896697427822428398291459)
    ·
      refine ⟨5845046141733642597437189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896697427822428398291459 5845046141733642597437189)
      ·
        refine ⟨1095946151575057987019473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5845046141733642597437189 1095946151575057987019473)
        ·
          refine ⟨821959613681293490264605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095946151575057987019473 821959613681293490264605)
          ·
            refine ⟨308234855130485058849227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 821959613681293490264605 308234855130485058849227)
            ·
              refine ⟨462352282695727588273841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308234855130485058849227 462352282695727588273841)
              ·
                refine ⟨346764212021795691205381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462352282695727588273841 346764212021795691205381)
                ·
                  refine ⟨65018289754086692101009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346764212021795691205381 65018289754086692101009)
                  ·
                    rfl

theorem cell21_284901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_284901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284901 prefixEnd_284901 := by exact prefixLift 284901
  have htrace : WordTrace (prefixWord ++ tailWord_284901) baseStart_284901 baseEnd_284901 := by
    simpa [prefixWord, tailWord_284901, baseEnd_284901] using wordTrace_append hprefix tailTrace_284901
  have hstable : (prefixWord ++ tailWord_284901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284901).length < 2 ^ (prefixWord ++ tailWord_284901).sum := by decide
  have hdescent : baseEnd_284901 < baseStart_284901 := by decide
  rcases family_descends (prefixWord ++ tailWord_284901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284932 : List Nat := [2, 3, 2, 2, 3, 2, 2, 5]
def baseStart_284932 : Nat := 118140960795 + 284932 * 2 ^ 59
def prefixEnd_284932 : Nat := 4983230072969 + 3 ^ 40 * 284932 * 2
def baseEnd_284932 : Nat := 21675121458812509028093

theorem tailTrace_284932 : CollatzResearch.WordTrace tailWord_284932 prefixEnd_284932 21675121458812509028093 := by
  unfold tailWord_284932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196161901873750678244525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6928215869165000904326033 5196161901873750678244525)
  ·
    refine ⟨1948560713202656504341697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5196161901873750678244525 1948560713202656504341697)
    ·
      refine ⟨1461420534901992378256273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1948560713202656504341697 1461420534901992378256273)
      ·
        refine ⟨1096065401176494283692205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1461420534901992378256273 1096065401176494283692205)
        ·
          refine ⟨411024525441185356384577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1096065401176494283692205 411024525441185356384577)
          ·
            refine ⟨308268394080889017288433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411024525441185356384577 308268394080889017288433)
            ·
              refine ⟨231201295560666762966325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308268394080889017288433 231201295560666762966325)
              ·
                refine ⟨21675121458812509028093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231201295560666762966325 21675121458812509028093)
                ·
                  rfl

theorem cell21_284932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_284932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284932 prefixEnd_284932 := by exact prefixLift 284932
  have htrace : WordTrace (prefixWord ++ tailWord_284932) baseStart_284932 baseEnd_284932 := by
    simpa [prefixWord, tailWord_284932, baseEnd_284932] using wordTrace_append hprefix tailTrace_284932
  have hstable : (prefixWord ++ tailWord_284932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284932).length < 2 ^ (prefixWord ++ tailWord_284932).sum := by decide
  have hdescent : baseEnd_284932 < baseStart_284932 := by decide
  rcases family_descends (prefixWord ++ tailWord_284932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284988 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_284988 : Nat := 118140960795 + 284988 * 2 ^ 59
def prefixEnd_284988 : Nat := 4983230072969 + 3 ^ 40 * 284988 * 2
def baseEnd_284988 : Nat := 65038144339393874150831

theorem tailTrace_284988 : CollatzResearch.WordTrace tailWord_284988 prefixEnd_284988 65038144339393874150831 := by
  unfold tailWord_284988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197183145772311460263809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6929577527696415280351745 5197183145772311460263809)
  ·
    refine ⟨3897887359329233595197857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5197183145772311460263809 3897887359329233595197857)
    ·
      refine ⟨2923415519496925196398393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3897887359329233595197857 2923415519496925196398393)
      ·
        refine ⟨2192561639622693897298795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923415519496925196398393 2192561639622693897298795)
        ·
          refine ⟨3288842459434040845948193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192561639622693897298795 3288842459434040845948193)
          ·
            refine ⟨2466631844575530634461145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288842459434040845948193 2466631844575530634461145)
            ·
              refine ⟨1849973883431647975845859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2466631844575530634461145 1849973883431647975845859)
              ·
                refine ⟨2774960825147471963768789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849973883431647975845859 2774960825147471963768789)
                ·
                  refine ⟨65038144339393874150831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2774960825147471963768789 65038144339393874150831)
                  ·
                    rfl

theorem cell21_284988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_284988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_284988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_284988 prefixEnd_284988 := by exact prefixLift 284988
  have htrace : WordTrace (prefixWord ++ tailWord_284988) baseStart_284988 baseEnd_284988 := by
    simpa [prefixWord, tailWord_284988, baseEnd_284988] using wordTrace_append hprefix tailTrace_284988
  have hstable : (prefixWord ++ tailWord_284988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284988).length < 2 ^ (prefixWord ++ tailWord_284988).sum := by decide
  have hdescent : baseEnd_284988 < baseStart_284988 := by decide
  rcases family_descends (prefixWord ++ tailWord_284988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285064 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_285064 : Nat := 118140960795 + 285064 * 2 ^ 59
def prefixEnd_285064 : Nat := 4983230072969 + 3 ^ 40 * 285064 * 2
def baseEnd_285064 : Nat := 65055488574834630884009

theorem tailTrace_285064 : CollatzResearch.WordTrace tailWord_285064 prefixEnd_285064 65055488574834630884009 := by
  unfold tailWord_285064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198569119634643950147123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6931425492846191933529497 5198569119634643950147123)
  ·
    refine ⟨7797853679451965925220685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5198569119634643950147123 7797853679451965925220685)
    ·
      refine ⟨2924195129794487221957757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7797853679451965925220685 2924195129794487221957757)
      ·
        refine ⟨1096573173672932708234159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2924195129794487221957757 1096573173672932708234159)
        ·
          refine ⟨1644859760509399062351239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096573173672932708234159 1644859760509399062351239)
          ·
            refine ⟨2467289640764098593526859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644859760509399062351239 2467289640764098593526859)
            ·
              refine ⟨3700934461146147890290289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467289640764098593526859 3700934461146147890290289)
              ·
                refine ⟨2775700845859610917717717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700934461146147890290289 2775700845859610917717717)
                ·
                  refine ⟨65055488574834630884009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2775700845859610917717717 65055488574834630884009)
                  ·
                    rfl

theorem cell21_285064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_285064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285064 prefixEnd_285064 := by exact prefixLift 285064
  have htrace : WordTrace (prefixWord ++ tailWord_285064) baseStart_285064 baseEnd_285064 := by
    simpa [prefixWord, tailWord_285064, baseEnd_285064] using wordTrace_append hprefix tailTrace_285064
  have hstable : (prefixWord ++ tailWord_285064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285064).length < 2 ^ (prefixWord ++ tailWord_285064).sum := by decide
  have hdescent : baseEnd_285064 < baseStart_285064 := by decide
  rcases family_descends (prefixWord ++ tailWord_285064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285081 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 3]
def baseStart_285081 : Nat := 118140960795 + 285081 * 2 ^ 59
def prefixEnd_285081 : Nat := 4983230072969 + 3 ^ 40 * 285081 * 2
def baseEnd_285081 : Nat := 65059368206446379100641

theorem tailTrace_285081 : CollatzResearch.WordTrace tailWord_285081 prefixEnd_285081 65059368206446379100641 := by
  unfold tailWord_285081
  simp only [CollatzResearch.WordTrace]
  refine ⟨10397758280207699803663097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6931838853471799869108731 10397758280207699803663097)
  ·
    refine ⟨7798318710155774852747323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10397758280207699803663097 7798318710155774852747323)
    ·
      refine ⟨11697478065233662279120985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798318710155774852747323 11697478065233662279120985)
      ·
        refine ⟨8773108548925246709340739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697478065233662279120985 8773108548925246709340739)
        ·
          refine ⟨13159662823387870064011109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8773108548925246709340739 13159662823387870064011109)
          ·
            refine ⟨2467436779385225637002083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13159662823387870064011109 2467436779385225637002083)
            ·
              refine ⟨3701155169077838455503125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467436779385225637002083 3701155169077838455503125)
              ·
                refine ⟨173491648550523677601709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3701155169077838455503125 173491648550523677601709)
                ·
                  refine ⟨65059368206446379100641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173491648550523677601709 65059368206446379100641)
                  ·
                    rfl

theorem cell21_285081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_285081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285081 prefixEnd_285081 := by exact prefixLift 285081
  have htrace : WordTrace (prefixWord ++ tailWord_285081) baseStart_285081 baseEnd_285081 := by
    simpa [prefixWord, tailWord_285081, baseEnd_285081] using wordTrace_append hprefix tailTrace_285081
  have hstable : (prefixWord ++ tailWord_285081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285081).length < 2 ^ (prefixWord ++ tailWord_285081).sum := by decide
  have hdescent : baseEnd_285081 < baseStart_285081 := by decide
  rcases family_descends (prefixWord ++ tailWord_285081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285101 : List Nat := [1, 5, 2, 2, 3, 1, 2, 5]
def baseStart_285101 : Nat := 118140960795 + 285101 * 2 ^ 59
def prefixEnd_285101 : Nat := 4983230072969 + 3 ^ 40 * 285101 * 2
def baseEnd_285101 : Nat := 21687977492976929589089

theorem tailTrace_285101 : CollatzResearch.WordTrace tailWord_285101 prefixEnd_285101 21687977492976929589089 := by
  unfold tailWord_285101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398487740135243219391157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6932325160090162146260771 10398487740135243219391157)
  ·
    refine ⟨974858225637679051817921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10398487740135243219391157 974858225637679051817921)
    ·
      refine ⟨731143669228259288863441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 974858225637679051817921 731143669228259288863441)
      ·
        refine ⟨548357751921194466647581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731143669228259288863441 548357751921194466647581)
        ·
          refine ⟨205634156970447924992843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 548357751921194466647581 205634156970447924992843)
          ·
            refine ⟨308451235455671887489265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205634156970447924992843 308451235455671887489265)
            ·
              refine ⟨231338426591753915616949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308451235455671887489265 231338426591753915616949)
              ·
                refine ⟨21687977492976929589089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231338426591753915616949 21687977492976929589089)
                ·
                  rfl

theorem cell21_285101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 5].length) (baseStart_285101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285101 prefixEnd_285101 := by exact prefixLift 285101
  have htrace : WordTrace (prefixWord ++ tailWord_285101) baseStart_285101 baseEnd_285101 := by
    simpa [prefixWord, tailWord_285101, baseEnd_285101] using wordTrace_append hprefix tailTrace_285101
  have hstable : (prefixWord ++ tailWord_285101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285101).length < 2 ^ (prefixWord ++ tailWord_285101).sum := by decide
  have hdescent : baseEnd_285101 < baseStart_285101 := by decide
  rcases family_descends (prefixWord ++ tailWord_285101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285174 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_285174 : Nat := 118140960795 + 285174 * 2 ^ 59
def prefixEnd_285174 : Nat := 4983230072969 + 3 ^ 40 * 285174 * 2
def baseEnd_285174 : Nat := 65080592073498884050451

theorem tailTrace_285174 : CollatzResearch.WordTrace tailWord_285174 prefixEnd_285174 65080592073498884050451 := by
  unfold tailWord_285174
  simp only [CollatzResearch.WordTrace]
  refine ⟨650071891804423542924911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6934100179247184457865717 650071891804423542924911)
  ·
    refine ⟨975107837706635314387367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 650071891804423542924911 975107837706635314387367)
    ·
      refine ⟨1462661756559952971581051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975107837706635314387367 1462661756559952971581051)
      ·
        refine ⟨2193992634839929457371577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462661756559952971581051 2193992634839929457371577)
        ·
          refine ⟨1645494476129947093028683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193992634839929457371577 1645494476129947093028683)
          ·
            refine ⟨2468241714194920639543025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645494476129947093028683 2468241714194920639543025)
            ·
              refine ⟨1851181285646190479657269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468241714194920639543025 1851181285646190479657269)
              ·
                refine ⟨173548245529330357467869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1851181285646190479657269 173548245529330357467869)
                ·
                  refine ⟨65080592073498884050451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173548245529330357467869 65080592073498884050451)
                  ·
                    rfl

theorem cell21_285174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_285174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285174 prefixEnd_285174 := by exact prefixLift 285174
  have htrace : WordTrace (prefixWord ++ tailWord_285174) baseStart_285174 baseEnd_285174 := by
    simpa [prefixWord, tailWord_285174, baseEnd_285174] using wordTrace_append hprefix tailTrace_285174
  have hstable : (prefixWord ++ tailWord_285174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285174).length < 2 ^ (prefixWord ++ tailWord_285174).sum := by decide
  have hdescent : baseEnd_285174 < baseStart_285174 := by decide
  rcases family_descends (prefixWord ++ tailWord_285174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285185 : List Nat := [1, 2, 4, 1, 3, 10]
def baseStart_285185 : Nat := 118140960795 + 285185 * 2 ^ 59
def prefixEnd_285185 : Nat := 4983230072969 + 3 ^ 40 * 285185 * 2
def baseEnd_285185 : Nat := 2410485274939455902485

theorem tailTrace_285185 : CollatzResearch.WordTrace tailWord_285185 prefixEnd_285185 2410485274939455902485 := by
  unfold tailWord_285185
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401551471830925565449009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6934367647887283710299339 10401551471830925565449009)
  ·
    refine ⟨7801163603873194174086757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10401551471830925565449009 7801163603873194174086757)
    ·
      refine ⟨1462718175726223907641267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7801163603873194174086757 1462718175726223907641267)
      ·
        refine ⟨2194077263589335861461901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462718175726223907641267 2194077263589335861461901)
        ·
          refine ⟨822778973846000948048213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2194077263589335861461901 822778973846000948048213)
          ·
            refine ⟨2410485274939455902485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 822778973846000948048213 2410485274939455902485)
            ·
              rfl

theorem cell21_285185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 10].length) (baseStart_285185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285185 prefixEnd_285185 := by exact prefixLift 285185
  have htrace : WordTrace (prefixWord ++ tailWord_285185) baseStart_285185 baseEnd_285185 := by
    simpa [prefixWord, tailWord_285185, baseEnd_285185] using wordTrace_append hprefix tailTrace_285185
  have hstable : (prefixWord ++ tailWord_285185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285185).length < 2 ^ (prefixWord ++ tailWord_285185).sum := by decide
  have hdescent : baseEnd_285185 < baseStart_285185 := by decide
  rcases family_descends (prefixWord ++ tailWord_285185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285188 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_285188 : Nat := 118140960795 + 285188 * 2 ^ 59
def prefixEnd_285188 : Nat := 4983230072969 + 3 ^ 40 * 285188 * 2
def baseEnd_285188 : Nat := 65083787064237970817089

theorem tailTrace_285188 : CollatzResearch.WordTrace tailWord_285188 prefixEnd_285188 65083787064237970817089 := by
  unfold tailWord_285188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200830445410028538904109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6934440593880038051872145 5200830445410028538904109)
  ·
    refine ⟨1950311417028760702089041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5200830445410028538904109 1950311417028760702089041)
    ·
      refine ⟨1462733562771570526566781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1950311417028760702089041 1462733562771570526566781)
      ·
        refine ⟨548525086039338947462543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1462733562771570526566781 548525086039338947462543)
        ·
          refine ⟨822787629059008421193815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548525086039338947462543 822787629059008421193815)
          ·
            refine ⟨1234181443588512631790723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822787629059008421193815 1234181443588512631790723)
            ·
              refine ⟨1851272165382768947686085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234181443588512631790723 1851272165382768947686085)
              ·
                refine ⟨347113531009269177691141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1851272165382768947686085 347113531009269177691141)
                ·
                  refine ⟨65083787064237970817089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 347113531009269177691141 65083787064237970817089)
                  ·
                    rfl

theorem cell21_285188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_285188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285188 prefixEnd_285188 := by exact prefixLift 285188
  have htrace : WordTrace (prefixWord ++ tailWord_285188) baseStart_285188 baseEnd_285188 := by
    simpa [prefixWord, tailWord_285188, baseEnd_285188] using wordTrace_append hprefix tailTrace_285188
  have hstable : (prefixWord ++ tailWord_285188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285188).length < 2 ^ (prefixWord ++ tailWord_285188).sum := by decide
  have hdescent : baseEnd_285188 < baseStart_285188 := by decide
  rcases family_descends (prefixWord ++ tailWord_285188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285233 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 3]
def baseStart_285233 : Nat := 118140960795 + 285233 * 2 ^ 59
def prefixEnd_285233 : Nat := 4983230072969 + 3 ^ 40 * 285233 * 2
def baseEnd_285233 : Nat := 65094056677327892566997

theorem tailTrace_285233 : CollatzResearch.WordTrace tailWord_285233 prefixEnd_285233 65094056677327892566997 := by
  unfold tailWord_285233
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403302175657029763196353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6935534783771353175464235 10403302175657029763196353)
  ·
    refine ⟨7802476631742772322397265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10403302175657029763196353 7802476631742772322397265)
    ·
      refine ⟨5851857473807079241797949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7802476631742772322397265 5851857473807079241797949)
      ·
        refine ⟨2194446552677654715674231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5851857473807079241797949 2194446552677654715674231)
        ·
          refine ⟨3291669829016482073511347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194446552677654715674231 3291669829016482073511347)
          ·
            refine ⟨4937504743524723110267021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291669829016482073511347 4937504743524723110267021)
            ·
              refine ⟨1851564278821771166350133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4937504743524723110267021 1851564278821771166350133)
              ·
                refine ⟨173584151139541046845325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1851564278821771166350133 173584151139541046845325)
                ·
                  refine ⟨65094056677327892566997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173584151139541046845325 65094056677327892566997)
                  ·
                    rfl

theorem cell21_285233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_285233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285233 prefixEnd_285233 := by exact prefixLift 285233
  have htrace : WordTrace (prefixWord ++ tailWord_285233) baseStart_285233 baseEnd_285233 := by
    simpa [prefixWord, tailWord_285233, baseEnd_285233] using wordTrace_append hprefix tailTrace_285233
  have hstable : (prefixWord ++ tailWord_285233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285233).length < 2 ^ (prefixWord ++ tailWord_285233).sum := by decide
  have hdescent : baseEnd_285233 < baseStart_285233 := by decide
  rcases family_descends (prefixWord ++ tailWord_285233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285354 : List Nat := [3, 1, 5, 2, 10]
def baseStart_285354 : Nat := 118140960795 + 285354 * 2 ^ 59
def prefixEnd_285354 : Nat := 4983230072969 + 3 ^ 40 * 285354 * 2
def baseEnd_285354 : Nat := 803971241059982358643

theorem tailTrace_285354 : CollatzResearch.WordTrace tailWord_285354 prefixEnd_285354 803971241059982358643 := by
  unfold tailWord_285354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601928852054666857087779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6938476938812444952234077 2601928852054666857087779)
  ·
    refine ⟨3902893278082000285631669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2601928852054666857087779 3902893278082000285631669)
    ·
      refine ⟨365896244820187526777969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3902893278082000285631669 365896244820187526777969)
      ·
        refine ⟨274422183615140645083477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365896244820187526777969 274422183615140645083477)
        ·
          refine ⟨803971241059982358643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 274422183615140645083477 803971241059982358643)
          ·
            rfl

theorem cell21_285354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 10].length) (baseStart_285354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285354 prefixEnd_285354 := by exact prefixLift 285354
  have htrace : WordTrace (prefixWord ++ tailWord_285354) baseStart_285354 baseEnd_285354 := by
    simpa [prefixWord, tailWord_285354, baseEnd_285354] using wordTrace_append hprefix tailTrace_285354
  have hstable : (prefixWord ++ tailWord_285354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285354).length < 2 ^ (prefixWord ++ tailWord_285354).sum := by decide
  have hdescent : baseEnd_285354 < baseStart_285354 := by decide
  rcases family_descends (prefixWord ++ tailWord_285354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285413 : List Nat := [1, 3, 1, 4, 1, 3, 8]
def baseStart_285413 : Nat := 118140960795 + 285413 * 2 ^ 59
def prefixEnd_285413 : Nat := 4983230072969 + 3 ^ 40 * 285413 * 2
def baseEnd_285413 : Nat := 7237237236631953285181

theorem tailTrace_285413 : CollatzResearch.WordTrace tailWord_285413 prefixEnd_285413 7237237236631953285181 := by
  unfold tailWord_285413
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409867315004920504748893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6939911543336613669832595 10409867315004920504748893)
  ·
    refine ⟨3903700243126845189280835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10409867315004920504748893 3903700243126845189280835)
    ·
      refine ⟨5855550364690267783921253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903700243126845189280835 5855550364690267783921253)
      ·
        refine ⟨1097915693379425209485235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5855550364690267783921253 1097915693379425209485235)
        ·
          refine ⟨1646873540069137814227853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097915693379425209485235 1646873540069137814227853)
          ·
            refine ⟨617577577525926680335445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1646873540069137814227853 617577577525926680335445)
            ·
              refine ⟨7237237236631953285181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 617577577525926680335445 7237237236631953285181)
              ·
                rfl

theorem cell21_285413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 8].length) (baseStart_285413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285413 prefixEnd_285413 := by exact prefixLift 285413
  have htrace : WordTrace (prefixWord ++ tailWord_285413) baseStart_285413 baseEnd_285413 := by
    simpa [prefixWord, tailWord_285413, baseEnd_285413] using wordTrace_append hprefix tailTrace_285413
  have hstable : (prefixWord ++ tailWord_285413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285413).length < 2 ^ (prefixWord ++ tailWord_285413).sum := by decide
  have hdescent : baseEnd_285413 < baseStart_285413 := by decide
  rcases family_descends (prefixWord ++ tailWord_285413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285444 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_285444 : Nat := 118140960795 + 285444 * 2 ^ 59
def prefixEnd_285444 : Nat := 4983230072969 + 3 ^ 40 * 285444 * 2
def baseEnd_285444 : Nat := 65142209752038414549899

theorem tailTrace_285444 : CollatzResearch.WordTrace tailWord_285444 prefixEnd_285444 65142209752038414549899 := by
  unfold tailWord_285444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205498988946306399563693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6940665318595075199418257 5205498988946306399563693)
  ·
    refine ⟨1952062120854864899836385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5205498988946306399563693 1952062120854864899836385)
    ·
      refine ⟨1464046590641148674877289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1952062120854864899836385 1464046590641148674877289)
      ·
        refine ⟨1098034942980861506157967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1464046590641148674877289 1098034942980861506157967)
        ·
          refine ⟨1647052414471292259236951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098034942980861506157967 1647052414471292259236951)
          ·
            refine ⟨2470578621706938388855427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647052414471292259236951 2470578621706938388855427)
            ·
              refine ⟨3705867932560407583283141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470578621706938388855427 3705867932560407583283141)
              ·
                refine ⟨694850237355076421865589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3705867932560407583283141 694850237355076421865589)
                ·
                  refine ⟨65142209752038414549899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694850237355076421865589 65142209752038414549899)
                  ·
                    rfl

theorem cell21_285444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_285444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285444 prefixEnd_285444 := by exact prefixLift 285444
  have htrace : WordTrace (prefixWord ++ tailWord_285444) baseStart_285444 baseEnd_285444 := by
    simpa [prefixWord, tailWord_285444, baseEnd_285444] using wordTrace_append hprefix tailTrace_285444
  have hstable : (prefixWord ++ tailWord_285444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285444).length < 2 ^ (prefixWord ++ tailWord_285444).sum := by decide
  have hdescent : baseEnd_285444 < baseStart_285444 := by decide
  rcases family_descends (prefixWord ++ tailWord_285444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285447 : List Nat := [1, 1, 4, 4, 1, 3, 2, 5]
def baseStart_285447 : Nat := 118140960795 + 285447 * 2 ^ 59
def prefixEnd_285447 : Nat := 4983230072969 + 3 ^ 40 * 285447 * 2
def baseEnd_285447 : Nat := 21714298130970358666631

theorem tailTrace_285447 : CollatzResearch.WordTrace tailWord_285447 prefixEnd_285447 21714298130970358666631 := by
  unfold tailWord_285447
  simp only [CollatzResearch.WordTrace]
  refine ⟨10411107396881744311486595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6940738264587829540991063 10411107396881744311486595)
  ·
    refine ⟨15616661095322616467229893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10411107396881744311486595 15616661095322616467229893)
    ·
      refine ⟨2928123955372990587605605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15616661095322616467229893 2928123955372990587605605)
      ·
        refine ⟨549023241632435735176051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2928123955372990587605605 549023241632435735176051)
        ·
          refine ⟨823534862448653602764077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549023241632435735176051 823534862448653602764077)
          ·
            refine ⟨308825573418245101036529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 823534862448653602764077 308825573418245101036529)
            ·
              refine ⟨231619180063683825777397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308825573418245101036529 231619180063683825777397)
              ·
                refine ⟨21714298130970358666631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231619180063683825777397 21714298130970358666631)
                ·
                  rfl

theorem cell21_285447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 5].length) (baseStart_285447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285447 prefixEnd_285447 := by exact prefixLift 285447
  have htrace : WordTrace (prefixWord ++ tailWord_285447) baseStart_285447 baseEnd_285447 := by
    simpa [prefixWord, tailWord_285447, baseEnd_285447] using wordTrace_append hprefix tailTrace_285447
  have hstable : (prefixWord ++ tailWord_285447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285447).length < 2 ^ (prefixWord ++ tailWord_285447).sum := by decide
  have hdescent : baseEnd_285447 < baseStart_285447 := by decide
  rcases family_descends (prefixWord ++ tailWord_285447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285489 : List Nat := [1, 2, 2, 3, 2, 1, 4, 6]
def baseStart_285489 : Nat := 118140960795 + 285489 * 2 ^ 59
def prefixEnd_285489 : Nat := 4983230072969 + 3 ^ 40 * 285489 * 2
def baseEnd_285489 : Nat := 21717493121709445433269

theorem tailTrace_285489 : CollatzResearch.WordTrace tailWord_285489 prefixEnd_285489 21717493121709445433269 := by
  unfold tailWord_285489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10412639262729585484515521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6941759508486390323010347 10412639262729585484515521)
  ·
    refine ⟨7809479447047189113386641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10412639262729585484515521 7809479447047189113386641)
    ·
      refine ⟨5857109585285391835039981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7809479447047189113386641 5857109585285391835039981)
      ·
        refine ⟨2196416094482021938139993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5857109585285391835039981 2196416094482021938139993)
        ·
          refine ⟨1647312070861516453604995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196416094482021938139993 1647312070861516453604995)
          ·
            refine ⟨2470968106292274680407493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647312070861516453604995 2470968106292274680407493)
            ·
              refine ⟨463306519929801502576405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2470968106292274680407493 463306519929801502576405)
              ·
                refine ⟨21717493121709445433269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 463306519929801502576405 21717493121709445433269)
                ·
                  rfl

theorem cell21_285489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_285489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285489 prefixEnd_285489 := by exact prefixLift 285489
  have htrace : WordTrace (prefixWord ++ tailWord_285489) baseStart_285489 baseEnd_285489 := by
    simpa [prefixWord, tailWord_285489, baseEnd_285489] using wordTrace_append hprefix tailTrace_285489
  have hstable : (prefixWord ++ tailWord_285489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285489).length < 2 ^ (prefixWord ++ tailWord_285489).sum := by decide
  have hdescent : baseEnd_285489 < baseStart_285489 := by decide
  rcases family_descends (prefixWord ++ tailWord_285489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285622 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_285622 : Nat := 118140960795 + 285622 * 2 ^ 59
def prefixEnd_285622 : Nat := 4983230072969 + 3 ^ 40 * 285622 * 2
def baseEnd_285622 : Nat := 65182831777149660582869

theorem tailTrace_285622 : CollatzResearch.WordTrace tailWord_285622 prefixEnd_285622 65182831777149660582869 := by
  unfold tailWord_285622
  simp only [CollatzResearch.WordTrace]
  refine ⟨651093135702984324944195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6944993447498499466071413 651093135702984324944195)
  ·
    refine ⟨976639703554476487416293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651093135702984324944195 976639703554476487416293)
    ·
      refine ⟨183119944416464341390555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 976639703554476487416293 183119944416464341390555)
      ·
        refine ⟨274679916624696512085833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183119944416464341390555 274679916624696512085833)
        ·
          refine ⟨206009937468522384064375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274679916624696512085833 206009937468522384064375)
          ·
            refine ⟨309014906202783576096563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206009937468522384064375 309014906202783576096563)
            ·
              refine ⟨463522359304175364144845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309014906202783576096563 463522359304175364144845)
              ·
                refine ⟨173820884739065761554317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463522359304175364144845 173820884739065761554317)
                ·
                  refine ⟨65182831777149660582869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173820884739065761554317 65182831777149660582869)
                  ·
                    rfl

theorem cell21_285622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_285622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285622 prefixEnd_285622 := by exact prefixLift 285622
  have htrace : WordTrace (prefixWord ++ tailWord_285622) baseStart_285622 baseEnd_285622 := by
    simpa [prefixWord, tailWord_285622, baseEnd_285622] using wordTrace_append hprefix tailTrace_285622
  have hstable : (prefixWord ++ tailWord_285622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285622).length < 2 ^ (prefixWord ++ tailWord_285622).sum := by decide
  have hdescent : baseEnd_285622 < baseStart_285622 := by decide
  rcases family_descends (prefixWord ++ tailWord_285622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285655 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_285655 : Nat := 118140960795 + 285655 * 2 ^ 59
def prefixEnd_285655 : Nat := 4983230072969 + 3 ^ 40 * 285655 * 2
def baseEnd_285655 : Nat := 65190362826748936532801

theorem tailTrace_285655 : CollatzResearch.WordTrace tailWord_285655 prefixEnd_285655 65190362826748936532801 := by
  unfold tailWord_285655
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418693780128195835058419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6945795853418797223372279 10418693780128195835058419)
  ·
    refine ⟨15628040670192293752587629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10418693780128195835058419 15628040670192293752587629)
    ·
      refine ⟨5860515251322110157220361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15628040670192293752587629 5860515251322110157220361)
      ·
        refine ⟨4395386438491582617915271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5860515251322110157220361 4395386438491582617915271)
        ·
          refine ⟨6593079657737373926872907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4395386438491582617915271 6593079657737373926872907)
          ·
            refine ⟨9889619486606060890309361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593079657737373926872907 9889619486606060890309361)
            ·
              refine ⟨7417214614954545667732021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9889619486606060890309361 7417214614954545667732021)
              ·
                refine ⟨695363870151988656349877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7417214614954545667732021 695363870151988656349877)
                ·
                  refine ⟨65190362826748936532801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695363870151988656349877 65190362826748936532801)
                  ·
                    rfl

theorem cell21_285655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_285655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285655 prefixEnd_285655 := by exact prefixLift 285655
  have htrace : WordTrace (prefixWord ++ tailWord_285655) baseStart_285655 baseEnd_285655 := by
    simpa [prefixWord, tailWord_285655, baseEnd_285655] using wordTrace_append hprefix tailTrace_285655
  have hstable : (prefixWord ++ tailWord_285655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285655).length < 2 ^ (prefixWord ++ tailWord_285655).sum := by decide
  have hdescent : baseEnd_285655 < baseStart_285655 := by decide
  rcases family_descends (prefixWord ++ tailWord_285655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285661 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 4]
def baseStart_285661 : Nat := 118140960795 + 285661 * 2 ^ 59
def prefixEnd_285661 : Nat := 4983230072969 + 3 ^ 40 * 285661 * 2
def baseEnd_285661 : Nat := 65191732108494259432789

theorem tailTrace_285661 : CollatzResearch.WordTrace tailWord_285661 prefixEnd_285661 65191732108494259432789 := by
  unfold tailWord_285661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418912618106458859776837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6945941745404305906517891 10418912618106458859776837)
  ·
    refine ⟨1953546115894961036208157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10418912618106458859776837 1953546115894961036208157)
    ·
      refine ⟨732579793460610388578059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1953546115894961036208157 732579793460610388578059)
      ·
        refine ⟨1098869690190915582867089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732579793460610388578059 1098869690190915582867089)
        ·
          refine ⟨824152267643186687150317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1098869690190915582867089 824152267643186687150317)
          ·
            refine ⟨309057100366195007681369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 824152267643186687150317 309057100366195007681369)
            ·
              refine ⟨231792825274646255761027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309057100366195007681369 231792825274646255761027)
              ·
                refine ⟨347689237911969383641541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231792825274646255761027 347689237911969383641541)
                ·
                  refine ⟨65191732108494259432789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 347689237911969383641541 65191732108494259432789)
                  ·
                    rfl

theorem cell21_285661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_285661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285661 prefixEnd_285661 := by exact prefixLift 285661
  have htrace : WordTrace (prefixWord ++ tailWord_285661) baseStart_285661 baseEnd_285661 := by
    simpa [prefixWord, tailWord_285661, baseEnd_285661] using wordTrace_append hprefix tailTrace_285661
  have hstable : (prefixWord ++ tailWord_285661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285661).length < 2 ^ (prefixWord ++ tailWord_285661).sum := by decide
  have hdescent : baseEnd_285661 < baseStart_285661 := by decide
  rcases family_descends (prefixWord ++ tailWord_285661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285700 : List Nat := [2, 3, 2, 14]
def baseStart_285700 : Nat := 118140960795 + 285700 * 2 ^ 59
def prefixEnd_285700 : Nat := 4983230072969 + 3 ^ 40 * 285700 * 2
def baseEnd_285700 : Nat := 268315359834727811863

theorem tailTrace_285700 : CollatzResearch.WordTrace tailWord_285700 prefixEnd_285700 268315359834727811863 := by
  unfold tailWord_285700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5210167532482584260223277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6946890043310112346964369 5210167532482584260223277)
  ·
    refine ⟨1953812824680969097583729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5210167532482584260223277 1953812824680969097583729)
    ·
      refine ⟨1465359618510726823187797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1953812824680969097583729 1465359618510726823187797)
      ·
        refine ⟨268315359834727811863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1465359618510726823187797 268315359834727811863)
        ·
          rfl

theorem cell21_285700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 14].length) (baseStart_285700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285700 prefixEnd_285700 := by exact prefixLift 285700
  have htrace : WordTrace (prefixWord ++ tailWord_285700) baseStart_285700 baseEnd_285700 := by
    simpa [prefixWord, tailWord_285700, baseEnd_285700] using wordTrace_append hprefix tailTrace_285700
  have hstable : (prefixWord ++ tailWord_285700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285700).length < 2 ^ (prefixWord ++ tailWord_285700).sum := by decide
  have hdescent : baseEnd_285700 < baseStart_285700 := by decide
  rcases family_descends (prefixWord ++ tailWord_285700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285703 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_285703 : Nat := 118140960795 + 285703 * 2 ^ 59
def prefixEnd_285703 : Nat := 4983230072969 + 3 ^ 40 * 285703 * 2
def baseEnd_285703 : Nat := 65201317080711519732703

theorem tailTrace_285703 : CollatzResearch.WordTrace tailWord_285703 prefixEnd_285703 65201317080711519732703 := by
  unfold tailWord_285703
  simp only [CollatzResearch.WordTrace]
  refine ⟨10420444483954300032805763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6946962989302866688537175 10420444483954300032805763)
  ·
    refine ⟨15630666725931450049208645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10420444483954300032805763 15630666725931450049208645)
    ·
      refine ⟨2930750011112146884226621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15630666725931450049208645 2930750011112146884226621)
      ·
        refine ⟨1099031254167055081584983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2930750011112146884226621 1099031254167055081584983)
        ·
          refine ⟨1648546881250582622377475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099031254167055081584983 1648546881250582622377475)
          ·
            refine ⟨2472820321875873933566213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648546881250582622377475 2472820321875873933566213)
            ·
              refine ⟨463653810351726362543665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2472820321875873933566213 463653810351726362543665)
              ·
                refine ⟨347740357763794771907749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463653810351726362543665 347740357763794771907749)
                ·
                  refine ⟨65201317080711519732703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 347740357763794771907749 65201317080711519732703)
                  ·
                    rfl

theorem cell21_285703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_285703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285703 prefixEnd_285703 := by exact prefixLift 285703
  have htrace : WordTrace (prefixWord ++ tailWord_285703) baseStart_285703 baseEnd_285703 := by
    simpa [prefixWord, tailWord_285703, baseEnd_285703] using wordTrace_append hprefix tailTrace_285703
  have hstable : (prefixWord ++ tailWord_285703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285703).length < 2 ^ (prefixWord ++ tailWord_285703).sum := by decide
  have hdescent : baseEnd_285703 < baseStart_285703 := by decide
  rcases family_descends (prefixWord ++ tailWord_285703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285706 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_285706 : Nat := 118140960795 + 285706 * 2 ^ 59
def prefixEnd_285706 : Nat := 4983230072969 + 3 ^ 40 * 285706 * 2
def baseEnd_285706 : Nat := 65202001721584181182697

theorem tailTrace_285706 : CollatzResearch.WordTrace tailWord_285706 prefixEnd_285706 65202001721584181182697 := by
  unfold tailWord_285706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605138475735857886291243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6947035935295621030109981 2605138475735857886291243)
  ·
    refine ⟨3907707713603786829436865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2605138475735857886291243 3907707713603786829436865)
    ·
      refine ⟨2930780785202840122077649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3907707713603786829436865 2930780785202840122077649)
      ·
        refine ⟨2198085588902130091558237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2930780785202840122077649 2198085588902130091558237)
        ·
          refine ⟨824282095838298784334339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2198085588902130091558237 824282095838298784334339)
          ·
            refine ⟨1236423143757448176501509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824282095838298784334339 1236423143757448176501509)
            ·
              refine ⟨231829339454521533094033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1236423143757448176501509 231829339454521533094033)
              ·
                refine ⟨173872004590891149820525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231829339454521533094033 173872004590891149820525)
                ·
                  refine ⟨65202001721584181182697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173872004590891149820525 65202001721584181182697)
                  ·
                    rfl

theorem cell21_285706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_285706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285706 prefixEnd_285706 := by exact prefixLift 285706
  have htrace : WordTrace (prefixWord ++ tailWord_285706) baseStart_285706 baseEnd_285706 := by
    simpa [prefixWord, tailWord_285706, baseEnd_285706] using wordTrace_append hprefix tailTrace_285706
  have hstable : (prefixWord ++ tailWord_285706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285706).length < 2 ^ (prefixWord ++ tailWord_285706).sum := by decide
  have hdescent : baseEnd_285706 < baseStart_285706 := by decide
  rcases family_descends (prefixWord ++ tailWord_285706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285717 : List Nat := [1, 3, 2, 1, 4, 1, 3, 6]
def baseStart_285717 : Nat := 118140960795 + 285717 * 2 ^ 59
def prefixEnd_285717 : Nat := 4983230072969 + 3 ^ 40 * 285717 * 2
def baseEnd_285717 : Nat := 21734837357150202166447

theorem tailTrace_285717 : CollatzResearch.WordTrace tailWord_285717 prefixEnd_285717 21734837357150202166447 := by
  unfold tailWord_285717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10420955105903580423815405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6947303403935720282543603 10420955105903580423815405)
  ·
    refine ⟨3907858164713842658930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10420955105903580423815405 3907858164713842658930777)
    ·
      refine ⟨2930893623535381994198083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3907858164713842658930777 2930893623535381994198083)
      ·
        refine ⟨4396340435303072991297125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930893623535381994198083 4396340435303072991297125)
        ·
          refine ⟨824313831619326185868211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4396340435303072991297125 824313831619326185868211)
          ·
            refine ⟨1236470747428989278802317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824313831619326185868211 1236470747428989278802317)
            ·
              refine ⟨463676530285870979550869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236470747428989278802317 463676530285870979550869)
              ·
                refine ⟨21734837357150202166447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 463676530285870979550869 21734837357150202166447)
                ·
                  rfl

theorem cell21_285717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_285717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285717 prefixEnd_285717 := by exact prefixLift 285717
  have htrace : WordTrace (prefixWord ++ tailWord_285717) baseStart_285717 baseEnd_285717 := by
    simpa [prefixWord, tailWord_285717, baseEnd_285717] using wordTrace_append hprefix tailTrace_285717
  have hstable : (prefixWord ++ tailWord_285717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285717).length < 2 ^ (prefixWord ++ tailWord_285717).sum := by decide
  have hdescent : baseEnd_285717 < baseStart_285717 := by decide
  rcases family_descends (prefixWord ++ tailWord_285717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285731 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_285731 : Nat := 118140960795 + 285731 * 2 ^ 59
def prefixEnd_285731 : Nat := 4983230072969 + 3 ^ 40 * 285731 * 2
def baseEnd_285731 : Nat := 65207707062189693265979

theorem tailTrace_285731 : CollatzResearch.WordTrace tailWord_285731 prefixEnd_285731 65207707062189693265979 := by
  unfold tailWord_285731
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421465727852860814825047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6947643818568573876550031 10421465727852860814825047)
  ·
    refine ⟨15632198591779291222237571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10421465727852860814825047 15632198591779291222237571)
    ·
      refine ⟨23448297887668936833356357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15632198591779291222237571 23448297887668936833356357)
      ·
        refine ⟨4396555853937925656254317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23448297887668936833356357 4396555853937925656254317)
        ·
          refine ⟨1648708445226722121095369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4396555853937925656254317 1648708445226722121095369)
          ·
            refine ⟨1236531333920041590821527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648708445226722121095369 1236531333920041590821527)
            ·
              refine ⟨1854797000880062386232291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236531333920041590821527 1854797000880062386232291)
              ·
                refine ⟨2782195501320093579348437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854797000880062386232291 2782195501320093579348437)
                ·
                  refine ⟨65207707062189693265979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2782195501320093579348437 65207707062189693265979)
                  ·
                    rfl

theorem cell21_285731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_285731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285731 prefixEnd_285731 := by exact prefixLift 285731
  have htrace : WordTrace (prefixWord ++ tailWord_285731) baseStart_285731 baseEnd_285731 := by
    simpa [prefixWord, tailWord_285731, baseEnd_285731] using wordTrace_append hprefix tailTrace_285731
  have hstable : (prefixWord ++ tailWord_285731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285731).length < 2 ^ (prefixWord ++ tailWord_285731).sum := by decide
  have hdescent : baseEnd_285731 < baseStart_285731 := by decide
  rcases family_descends (prefixWord ++ tailWord_285731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285793 : List Nat := [1, 2, 3, 1, 1, 2, 6, 5]
def baseStart_285793 : Nat := 118140960795 + 285793 * 2 ^ 59
def prefixEnd_285793 : Nat := 4983230072969 + 3 ^ 40 * 285793 * 2
def baseEnd_285793 : Nat := 21740618768963787744173

theorem tailTrace_285793 : CollatzResearch.WordTrace tailWord_285793 prefixEnd_285793 21740618768963787744173 := by
  unfold tailWord_285793
  simp only [CollatzResearch.WordTrace]
  refine ⟨10423727053628245403582033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6949151369085496935721355 10423727053628245403582033)
  ·
    refine ⟨7817795290221184052686525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10423727053628245403582033 7817795290221184052686525)
    ·
      refine ⟨2931673233832944019757447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7817795290221184052686525 2931673233832944019757447)
      ·
        refine ⟨4397509850749416029636171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931673233832944019757447 4397509850749416029636171)
        ·
          refine ⟨6596264776124124044454257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397509850749416029636171 6596264776124124044454257)
          ·
            refine ⟨4947198582093093033340693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6596264776124124044454257 4947198582093093033340693)
            ·
              refine ⟨231899933535613735937845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4947198582093093033340693 231899933535613735937845)
              ·
                refine ⟨21740618768963787744173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231899933535613735937845 21740618768963787744173)
                ·
                  rfl

theorem cell21_285793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 5].length) (baseStart_285793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285793 prefixEnd_285793 := by exact prefixLift 285793
  have htrace : WordTrace (prefixWord ++ tailWord_285793) baseStart_285793 baseEnd_285793 := by
    simpa [prefixWord, tailWord_285793, baseEnd_285793] using wordTrace_append hprefix tailTrace_285793
  have hstable : (prefixWord ++ tailWord_285793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285793).length < 2 ^ (prefixWord ++ tailWord_285793).sum := by decide
  have hdescent : baseEnd_285793 < baseStart_285793 := by decide
  rcases family_descends (prefixWord ++ tailWord_285793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285824 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_285824 : Nat := 118140960795 + 285824 * 2 ^ 59
def prefixEnd_285824 : Nat := 4983230072969 + 3 ^ 40 * 285824 * 2
def baseEnd_285824 : Nat := 65228930929242198215789

theorem tailTrace_285824 : CollatzResearch.WordTrace tailWord_285824 prefixEnd_285824 65228930929242198215789 := by
  unfold tailWord_285824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212428858257968848980263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6949905144343958465307017 5212428858257968848980263)
  ·
    refine ⟨7818643287386953273470395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212428858257968848980263 7818643287386953273470395)
    ·
      refine ⟨11727964931080429910205593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818643287386953273470395 11727964931080429910205593)
      ·
        refine ⟨8795973698310322432654195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11727964931080429910205593 8795973698310322432654195)
        ·
          refine ⟨13193960547465483648981293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8795973698310322432654195 13193960547465483648981293)
          ·
            refine ⟨4947735205299556368367985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13193960547465483648981293 4947735205299556368367985)
            ·
              refine ⟨3710801403974667276275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947735205299556368367985 3710801403974667276275989)
              ·
                refine ⟨173943815811312528575437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3710801403974667276275989 173943815811312528575437)
                ·
                  refine ⟨65228930929242198215789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173943815811312528575437 65228930929242198215789)
                  ·
                    rfl

theorem cell21_285824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_285824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285824 prefixEnd_285824 := by exact prefixLift 285824
  have htrace : WordTrace (prefixWord ++ tailWord_285824) baseStart_285824 baseEnd_285824 := by
    simpa [prefixWord, tailWord_285824, baseEnd_285824] using wordTrace_append hprefix tailTrace_285824
  have hstable : (prefixWord ++ tailWord_285824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285824).length < 2 ^ (prefixWord ++ tailWord_285824).sum := by decide
  have hdescent : baseEnd_285824 < baseStart_285824 := by decide
  rcases family_descends (prefixWord ++ tailWord_285824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285869 : List Nat := [1, 5, 2, 1, 3, 9]
def baseStart_285869 : Nat := 118140960795 + 285869 * 2 ^ 59
def prefixEnd_285869 : Nat := 4983230072969 + 3 ^ 40 * 285869 * 2
def baseEnd_285869 : Nat := 2416266686753041480211

theorem tailTrace_285869 : CollatzResearch.WordTrace tailWord_285869 prefixEnd_285869 2416266686753041480211 := by
  unfold tailWord_285869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10426499001352910383348661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6950999334235273588899107 10426499001352910383348661)
  ·
    refine ⟨977484281376835348438937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10426499001352910383348661 977484281376835348438937)
    ·
      refine ⟨733113211032626511329203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 977484281376835348438937 733113211032626511329203)
      ·
        refine ⟨1099669816548939766993805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733113211032626511329203 1099669816548939766993805)
        ·
          refine ⟨412376181205852412622677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1099669816548939766993805 412376181205852412622677)
          ·
            refine ⟨2416266686753041480211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 412376181205852412622677 2416266686753041480211)
            ·
              rfl

theorem cell21_285869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 9].length) (baseStart_285869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285869 prefixEnd_285869 := by exact prefixLift 285869
  have htrace : WordTrace (prefixWord ++ tailWord_285869) baseStart_285869 baseEnd_285869 := by
    simpa [prefixWord, tailWord_285869, baseEnd_285869] using wordTrace_append hprefix tailTrace_285869
  have hstable : (prefixWord ++ tailWord_285869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285869).length < 2 ^ (prefixWord ++ tailWord_285869).sum := by decide
  have hdescent : baseEnd_285869 < baseStart_285869 := by decide
  rcases family_descends (prefixWord ++ tailWord_285869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285886 : List Nat := [4, 2, 1, 1, 3, 3, 1, 6]
def baseStart_285886 : Nat := 118140960795 + 285886 * 2 ^ 59
def prefixEnd_285886 : Nat := 4983230072969 + 3 ^ 40 * 285886 * 2
def baseEnd_285886 : Nat := 21747693391314622727443

theorem tailTrace_285886 : CollatzResearch.WordTrace tailWord_285886 prefixEnd_285886 21747693391314622727443 := by
  unfold tailWord_285886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303389880286415285839689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6951412694860881524478341 1303389880286415285839689)
  ·
    refine ⟨977542410214811464379767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1303389880286415285839689 977542410214811464379767)
    ·
      refine ⟨1466313615322217196569651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977542410214811464379767 1466313615322217196569651)
      ·
        refine ⟨2199470422983325794854477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466313615322217196569651 2199470422983325794854477)
        ·
          refine ⟨824801408618747173070429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2199470422983325794854477 824801408618747173070429)
          ·
            refine ⟨309300528232030189901411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 824801408618747173070429 309300528232030189901411)
            ·
              refine ⟨463950792348045284852117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309300528232030189901411 463950792348045284852117)
              ·
                refine ⟨21747693391314622727443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 463950792348045284852117 21747693391314622727443)
                ·
                  rfl

theorem cell21_285886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_285886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285886 prefixEnd_285886 := by exact prefixLift 285886
  have htrace : WordTrace (prefixWord ++ tailWord_285886) baseStart_285886 baseEnd_285886 := by
    simpa [prefixWord, tailWord_285886, baseEnd_285886] using wordTrace_append hprefix tailTrace_285886
  have hstable : (prefixWord ++ tailWord_285886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285886).length < 2 ^ (prefixWord ++ tailWord_285886).sum := by decide
  have hdescent : baseEnd_285886 < baseStart_285886 := by decide
  rcases family_descends (prefixWord ++ tailWord_285886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285928 : List Nat := [2, 1, 4, 1, 2, 1, 10]
def baseStart_285928 : Nat := 118140960795 + 285928 * 2 ^ 59
def prefixEnd_285928 : Nat := 4983230072969 + 3 ^ 40 * 285928 * 2
def baseEnd_285928 : Nat := 7250296127351236498027

theorem tailTrace_285928 : CollatzResearch.WordTrace tailWord_285928 prefixEnd_285928 7250296127351236498027 := by
  unfold tailWord_285928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214325454069581729873219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6952433938759442306497625 5214325454069581729873219)
  ·
    refine ⟨7821488181104372594809829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5214325454069581729873219 7821488181104372594809829)
    ·
      refine ⟨1466529033957069861526843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7821488181104372594809829 1466529033957069861526843)
      ·
        refine ⟨2199793550935604792290265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466529033957069861526843 2199793550935604792290265)
        ·
          refine ⟨1649845163201703594217699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2199793550935604792290265 1649845163201703594217699)
          ·
            refine ⟨2474767744802555391326549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649845163201703594217699 2474767744802555391326549)
            ·
              refine ⟨7250296127351236498027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2474767744802555391326549 7250296127351236498027)
              ·
                rfl

theorem cell21_285928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 10].length) (baseStart_285928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285928 prefixEnd_285928 := by exact prefixLift 285928
  have htrace : WordTrace (prefixWord ++ tailWord_285928) baseStart_285928 baseEnd_285928 := by
    simpa [prefixWord, tailWord_285928, baseEnd_285928] using wordTrace_append hprefix tailTrace_285928
  have hstable : (prefixWord ++ tailWord_285928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285928).length < 2 ^ (prefixWord ++ tailWord_285928).sum := by decide
  have hdescent : baseEnd_285928 < baseStart_285928 := by decide
  rcases family_descends (prefixWord ++ tailWord_285928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285931 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 4]
def baseStart_285931 : Nat := 118140960795 + 285931 * 2 ^ 59
def prefixEnd_285931 : Nat := 4983230072969 + 3 ^ 40 * 285931 * 2
def baseEnd_285931 : Nat := 65253349787033789932237

theorem tailTrace_285931 : CollatzResearch.WordTrace tailWord_285931 prefixEnd_285931 65253349787033789932237 := by
  unfold tailWord_285931
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428760327128294972105647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6952506884752196648070431 10428760327128294972105647)
  ·
    refine ⟨15643140490692442458158471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10428760327128294972105647 15643140490692442458158471)
    ·
      refine ⟨23464710736038663687237707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15643140490692442458158471 23464710736038663687237707)
      ·
        refine ⟨35197066104057995530856561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23464710736038663687237707 35197066104057995530856561)
        ·
          refine ⟨26397799578043496648142421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35197066104057995530856561 26397799578043496648142421)
          ·
            refine ⟨309349213805197226345419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 26397799578043496648142421 309349213805197226345419)
            ·
              refine ⟨464023820707795839518129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309349213805197226345419 464023820707795839518129)
              ·
                refine ⟨348017865530846879638597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464023820707795839518129 348017865530846879638597)
                ·
                  refine ⟨65253349787033789932237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348017865530846879638597 65253349787033789932237)
                  ·
                    rfl

theorem cell21_285931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_285931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285931 prefixEnd_285931 := by exact prefixLift 285931
  have htrace : WordTrace (prefixWord ++ tailWord_285931) baseStart_285931 baseEnd_285931 := by
    simpa [prefixWord, tailWord_285931, baseEnd_285931] using wordTrace_append hprefix tailTrace_285931
  have hstable : (prefixWord ++ tailWord_285931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285931).length < 2 ^ (prefixWord ++ tailWord_285931).sum := by decide
  have hdescent : baseEnd_285931 < baseStart_285931 := by decide
  rcases family_descends (prefixWord ++ tailWord_285931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285948 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_285948 : Nat := 118140960795 + 285948 * 2 ^ 59
def prefixEnd_285948 : Nat := 4983230072969 + 3 ^ 40 * 285948 * 2
def baseEnd_285948 : Nat := 65257229418645538148869

theorem tailTrace_285948 : CollatzResearch.WordTrace tailWord_285948 prefixEnd_285948 65257229418645538148869 := by
  unfold tailWord_285948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214690184033353437737249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6952920245377804583649665 5214690184033353437737249)
  ·
    refine ⟨3911017638025015078302937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5214690184033353437737249 3911017638025015078302937)
    ·
      refine ⟨2933263228518761308727203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3911017638025015078302937 2933263228518761308727203)
      ·
        refine ⟨4399894842778141963090805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933263228518761308727203 4399894842778141963090805)
        ·
          refine ⟨412490141510450809039763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4399894842778141963090805 412490141510450809039763)
          ·
            refine ⟨618735212265676213559645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412490141510450809039763 618735212265676213559645)
            ·
              refine ⟨232025704599628580084867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 618735212265676213559645 232025704599628580084867)
              ·
                refine ⟨348038556899442870127301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232025704599628580084867 348038556899442870127301)
                ·
                  refine ⟨65257229418645538148869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348038556899442870127301 65257229418645538148869)
                  ·
                    rfl

theorem cell21_285948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_285948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_285948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_285948 prefixEnd_285948 := by exact prefixLift 285948
  have htrace : WordTrace (prefixWord ++ tailWord_285948) baseStart_285948 baseEnd_285948 := by
    simpa [prefixWord, tailWord_285948, baseEnd_285948] using wordTrace_append hprefix tailTrace_285948
  have hstable : (prefixWord ++ tailWord_285948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285948).length < 2 ^ (prefixWord ++ tailWord_285948).sum := by decide
  have hdescent : baseEnd_285948 < baseStart_285948 := by decide
  rcases family_descends (prefixWord ++ tailWord_285948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286049 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_286049 : Nat := 118140960795 + 286049 * 2 ^ 59
def prefixEnd_286049 : Nat := 4983230072969 + 3 ^ 40 * 286049 * 2
def baseEnd_286049 : Nat := 65280278994691806965329

theorem tailTrace_286049 : CollatzResearch.WordTrace tailWord_286049 prefixEnd_286049 65280278994691806965329 := by
  unfold tailWord_286049
  simp only [CollatzResearch.WordTrace]
  refine ⟨10433064140700801124901201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6955376093800534083267467 10433064140700801124901201)
  ·
    refine ⟨7824798105525600843675901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10433064140700801124901201 7824798105525600843675901)
    ·
      refine ⟨2934299289572100316378463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7824798105525600843675901 2934299289572100316378463)
      ·
        refine ⟨4401448934358150474567695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934299289572100316378463 4401448934358150474567695)
        ·
          refine ⟨6602173401537225711851543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401448934358150474567695 6602173401537225711851543)
          ·
            refine ⟨9903260102305838567777315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6602173401537225711851543 9903260102305838567777315)
            ·
              refine ⟨14854890153458757851665973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9903260102305838567777315 14854890153458757851665973)
              ·
                refine ⟨1392645951886758548593685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14854890153458757851665973 1392645951886758548593685)
                ·
                  refine ⟨65280278994691806965329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1392645951886758548593685 65280278994691806965329)
                  ·
                    rfl

theorem cell21_286049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_286049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286049 prefixEnd_286049 := by exact prefixLift 286049
  have htrace : WordTrace (prefixWord ++ tailWord_286049) baseStart_286049 baseEnd_286049 := by
    simpa [prefixWord, tailWord_286049, baseEnd_286049] using wordTrace_append hprefix tailTrace_286049
  have hstable : (prefixWord ++ tailWord_286049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286049).length < 2 ^ (prefixWord ++ tailWord_286049).sum := by decide
  have hdescent : baseEnd_286049 < baseStart_286049 := by decide
  rcases family_descends (prefixWord ++ tailWord_286049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286066 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_286066 : Nat := 118140960795 + 286066 * 2 ^ 59
def prefixEnd_286066 : Nat := 4983230072969 + 3 ^ 40 * 286066 * 2
def baseEnd_286066 : Nat := 65284158626303555181961

theorem tailTrace_286066 : CollatzResearch.WordTrace tailWord_286066 prefixEnd_286066 65284158626303555181961 := by
  unfold tailWord_286066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608421045409803257067513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6955789454426142018846701 2608421045409803257067513)
  ·
    refine ⟨1956315784057352442800635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2608421045409803257067513 1956315784057352442800635)
    ·
      refine ⟨2934473676086028664200953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1956315784057352442800635 2934473676086028664200953)
      ·
        refine ⟨2200855257064521498150715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2934473676086028664200953 2200855257064521498150715)
        ·
          refine ⟨3301282885596782247226073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200855257064521498150715 3301282885596782247226073)
          ·
            refine ⟨2475962164197586685419555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3301282885596782247226073 2475962164197586685419555)
            ·
              refine ⟨3713943246296380028129333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475962164197586685419555 3713943246296380028129333)
              ·
                refine ⟨348182179340285627637125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3713943246296380028129333 348182179340285627637125)
                ·
                  refine ⟨65284158626303555181961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348182179340285627637125 65284158626303555181961)
                  ·
                    rfl

theorem cell21_286066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_286066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286066 prefixEnd_286066 := by exact prefixLift 286066
  have htrace : WordTrace (prefixWord ++ tailWord_286066) baseStart_286066 baseEnd_286066 := by
    simpa [prefixWord, tailWord_286066, baseEnd_286066] using wordTrace_append hprefix tailTrace_286066
  have hstable : (prefixWord ++ tailWord_286066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286066).length < 2 ^ (prefixWord ++ tailWord_286066).sum := by decide
  have hdescent : baseEnd_286066 < baseStart_286066 := by decide
  rcases family_descends (prefixWord ++ tailWord_286066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286100 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_286100 : Nat := 118140960795 + 286100 * 2 ^ 59
def prefixEnd_286100 : Nat := 4983230072969 + 3 ^ 40 * 286100 * 2
def baseEnd_286100 : Nat := 65291917889527051615225

theorem tailTrace_286100 : CollatzResearch.WordTrace tailWord_286100 prefixEnd_286100 65291917889527051615225 := by
  unfold tailWord_286100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217462131758018417503877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6956616175677357890005169 5217462131758018417503877)
  ·
    refine ⟨978274149704628453281977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5217462131758018417503877 978274149704628453281977)
    ·
      refine ⟨733705612278471339961483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 978274149704628453281977 733705612278471339961483)
      ·
        refine ⟨1100558418417707009942225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733705612278471339961483 1100558418417707009942225)
        ·
          refine ⟨825418813813280257456669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100558418417707009942225 825418813813280257456669)
          ·
            refine ⟨309532055179980096546251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 825418813813280257456669 309532055179980096546251)
            ·
              refine ⟨464298082769970144819377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309532055179980096546251 464298082769970144819377)
              ·
                refine ⟨348223562077477608614533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464298082769970144819377 348223562077477608614533)
                ·
                  refine ⟨65291917889527051615225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348223562077477608614533 65291917889527051615225)
                  ·
                    rfl

theorem cell21_286100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_286100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286100 prefixEnd_286100 := by exact prefixLift 286100
  have htrace : WordTrace (prefixWord ++ tailWord_286100) baseStart_286100 baseEnd_286100 := by
    simpa [prefixWord, tailWord_286100, baseEnd_286100] using wordTrace_append hprefix tailTrace_286100
  have hstable : (prefixWord ++ tailWord_286100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286100).length < 2 ^ (prefixWord ++ tailWord_286100).sum := by decide
  have hdescent : baseEnd_286100 < baseStart_286100 := by decide
  rcases family_descends (prefixWord ++ tailWord_286100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286111 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_286111 : Nat := 118140960795 + 286111 * 2 ^ 59
def prefixEnd_286111 : Nat := 4983230072969 + 3 ^ 40 * 286111 * 2
def baseEnd_286111 : Nat := 65294428239393476931869

theorem tailTrace_286111 : CollatzResearch.WordTrace tailWord_286111 prefixEnd_286111 65294428239393476931869 := by
  unfold tailWord_286111
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435325466476185713658187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6956883644317457142438791 10435325466476185713658187)
  ·
    refine ⟨15652988199714278570487281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10435325466476185713658187 15652988199714278570487281)
    ·
      refine ⟨11739741149785708927865461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15652988199714278570487281 11739741149785708927865461)
      ·
        refine ⟨1100600732792410211987387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11739741149785708927865461 1100600732792410211987387)
        ·
          refine ⟨1650901099188615317981081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100600732792410211987387 1650901099188615317981081)
          ·
            refine ⟨1238175824391461488485811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1650901099188615317981081 1238175824391461488485811)
            ·
              refine ⟨1857263736587192232728717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238175824391461488485811 1857263736587192232728717)
              ·
                refine ⟨696473901220197087273269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1857263736587192232728717 696473901220197087273269)
                ·
                  refine ⟨65294428239393476931869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 696473901220197087273269 65294428239393476931869)
                  ·
                    rfl

theorem cell21_286111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_286111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286111 prefixEnd_286111 := by exact prefixLift 286111
  have htrace : WordTrace (prefixWord ++ tailWord_286111) baseStart_286111 baseEnd_286111 := by
    simpa [prefixWord, tailWord_286111, baseEnd_286111] using wordTrace_append hprefix tailTrace_286111
  have hstable : (prefixWord ++ tailWord_286111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286111).length < 2 ^ (prefixWord ++ tailWord_286111).sum := by decide
  have hdescent : baseEnd_286111 < baseStart_286111 := by decide
  rcases family_descends (prefixWord ++ tailWord_286111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286156 : List Nat := [2, 2, 1, 4, 2, 1, 9]
def baseStart_286156 : Nat := 118140960795 + 286156 * 2 ^ 59
def prefixEnd_286156 : Nat := 4983230072969 + 3 ^ 40 * 286156 * 2
def baseEnd_286156 : Nat := 7256077539164822075753

theorem tailTrace_286156 : CollatzResearch.WordTrace tailWord_286156 prefixEnd_286156 7256077539164822075753 := by
  unfold tailWord_286156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218483375656579199523161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6957977834208772266030881 5218483375656579199523161)
  ·
    refine ⟨3913862531742434399642371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5218483375656579199523161 3913862531742434399642371)
    ·
      refine ⟨5870793797613651599463557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3913862531742434399642371 5870793797613651599463557)
      ·
        refine ⟨1100773837052559674899417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5870793797613651599463557 1100773837052559674899417)
        ·
          refine ⟨825580377789419756174563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100773837052559674899417 825580377789419756174563)
          ·
            refine ⟨1238370566684129634261845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825580377789419756174563 1238370566684129634261845)
            ·
              refine ⟨7256077539164822075753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1238370566684129634261845 7256077539164822075753)
              ·
                rfl

theorem cell21_286156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 9].length) (baseStart_286156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286156 prefixEnd_286156 := by exact prefixLift 286156
  have htrace : WordTrace (prefixWord ++ tailWord_286156) baseStart_286156 baseEnd_286156 := by
    simpa [prefixWord, tailWord_286156, baseEnd_286156] using wordTrace_append hprefix tailTrace_286156
  have hstable : (prefixWord ++ tailWord_286156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286156).length < 2 ^ (prefixWord ++ tailWord_286156).sum := by decide
  have hdescent : baseEnd_286156 < baseStart_286156 := by decide
  rcases family_descends (prefixWord ++ tailWord_286156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286173 : List Nat := [1, 4, 3, 1, 1, 3, 2, 6]
def baseStart_286173 : Nat := 118140960795 + 286173 * 2 ^ 59
def prefixEnd_286173 : Nat := 4983230072969 + 3 ^ 40 * 286173 * 2
def baseEnd_286173 : Nat := 21769525828031715632803

theorem tailTrace_286173 : CollatzResearch.WordTrace tailWord_286173 prefixEnd_286173 21769525828031715632803 := by
  unfold tailWord_286173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10437586792251570302415173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6958391194834380201610115 10437586792251570302415173)
  ·
    refine ⟨1957047523547169431702845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10437586792251570302415173 1957047523547169431702845)
    ·
      refine ⟨733892821330188536888567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1957047523547169431702845 733892821330188536888567)
      ·
        refine ⟨1100839231995282805332851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733892821330188536888567 1100839231995282805332851)
        ·
          refine ⟨1651258847992924207999277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100839231995282805332851 1651258847992924207999277)
          ·
            refine ⟨619222067997346577999729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1651258847992924207999277 619222067997346577999729)
            ·
              refine ⟨464416550998009933499797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619222067997346577999729 464416550998009933499797)
              ·
                refine ⟨21769525828031715632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 464416550998009933499797 21769525828031715632803)
                ·
                  rfl

theorem cell21_286173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_286173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286173 prefixEnd_286173 := by exact prefixLift 286173
  have htrace : WordTrace (prefixWord ++ tailWord_286173) baseStart_286173 baseEnd_286173 := by
    simpa [prefixWord, tailWord_286173, baseEnd_286173] using wordTrace_append hprefix tailTrace_286173
  have hstable : (prefixWord ++ tailWord_286173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286173).length < 2 ^ (prefixWord ++ tailWord_286173).sum := by decide
  have hdescent : baseEnd_286173 < baseStart_286173 := by decide
  rcases family_descends (prefixWord ++ tailWord_286173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286218 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_286218 : Nat := 118140960795 + 286218 * 2 ^ 59
def prefixEnd_286218 : Nat := 4983230072969 + 3 ^ 40 * 286218 * 2
def baseEnd_286218 : Nat := 65318847097185068648317

theorem tailTrace_286218 : CollatzResearch.WordTrace tailWord_286218 prefixEnd_286218 65318847097185068648317 := by
  unfold tailWord_286218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609807019272135746950827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6959485384725695325202205 2609807019272135746950827)
  ·
    refine ⟨3914710528908203620426241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2609807019272135746950827 3914710528908203620426241)
    ·
      refine ⟨2936032896681152715319681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3914710528908203620426241 2936032896681152715319681)
      ·
        refine ⟨2202024672510864536489761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2936032896681152715319681 2202024672510864536489761)
        ·
          refine ⟨1651518504383148402367321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2202024672510864536489761 1651518504383148402367321)
          ·
            refine ⟨1238638878287361301775491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651518504383148402367321 1238638878287361301775491)
            ·
              refine ⟨1857958317431041952663237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238638878287361301775491 1857958317431041952663237)
              ·
                refine ⟨348367184518320366124357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1857958317431041952663237 348367184518320366124357)
                ·
                  refine ⟨65318847097185068648317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348367184518320366124357 65318847097185068648317)
                  ·
                    rfl

theorem cell21_286218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_286218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286218 prefixEnd_286218 := by exact prefixLift 286218
  have htrace : WordTrace (prefixWord ++ tailWord_286218) baseStart_286218 baseEnd_286218 := by
    simpa [prefixWord, tailWord_286218, baseEnd_286218] using wordTrace_append hprefix tailTrace_286218
  have hstable : (prefixWord ++ tailWord_286218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286218).length < 2 ^ (prefixWord ++ tailWord_286218).sum := by decide
  have hdescent : baseEnd_286218 < baseStart_286218 := by decide
  rcases family_descends (prefixWord ++ tailWord_286218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286277 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_286277 : Nat := 118140960795 + 286277 * 2 ^ 59
def prefixEnd_286277 : Nat := 4983230072969 + 3 ^ 40 * 286277 * 2
def baseEnd_286277 : Nat := 65332311701014077164863

theorem tailTrace_286277 : CollatzResearch.WordTrace tailWord_286277 prefixEnd_286277 65332311701014077164863 := by
  unfold tailWord_286277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441379983874796064201085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6960919989249864042800723 10441379983874796064201085)
  ·
    refine ⟨3915517493953048524075407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10441379983874796064201085 3915517493953048524075407)
    ·
      refine ⟨5873276240929572786113111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3915517493953048524075407 5873276240929572786113111)
      ·
        refine ⟨8809914361394359179169667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873276240929572786113111 8809914361394359179169667)
        ·
          refine ⟨13214871542091538768754501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8809914361394359179169667 13214871542091538768754501)
          ·
            refine ⟨2477788414142163519141469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13214871542091538768754501 2477788414142163519141469)
            ·
              refine ⟨929170655303311319678051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2477788414142163519141469 929170655303311319678051)
              ·
                refine ⟨1393755982954966979517077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929170655303311319678051 1393755982954966979517077)
                ·
                  refine ⟨65332311701014077164863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1393755982954966979517077 65332311701014077164863)
                  ·
                    rfl

theorem cell21_286277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_286277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286277 prefixEnd_286277 := by exact prefixLift 286277
  have htrace : WordTrace (prefixWord ++ tailWord_286277) baseStart_286277 baseEnd_286277 := by
    simpa [prefixWord, tailWord_286277, baseEnd_286277] using wordTrace_append hprefix tailTrace_286277
  have hstable : (prefixWord ++ tailWord_286277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286277).length < 2 ^ (prefixWord ++ tailWord_286277).sum := by decide
  have hdescent : baseEnd_286277 < baseStart_286277 := by decide
  rcases family_descends (prefixWord ++ tailWord_286277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286308 : List Nat := [2, 3, 1, 1, 2, 4, 1, 7]
def baseStart_286308 : Nat := 118140960795 + 286308 * 2 ^ 59
def prefixEnd_286308 : Nat := 4983230072969 + 3 ^ 40 * 286308 * 2
def baseEnd_286308 : Nat := 21779795441121637382711

theorem tailTrace_286308 : CollatzResearch.WordTrace tailWord_286308 prefixEnd_286308 21779795441121637382711 := by
  unfold tailWord_286308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221255323381244179289789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6961673764508325572386385 5221255323381244179289789)
  ·
    refine ⟨1957970746267966567233671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5221255323381244179289789 1957970746267966567233671)
    ·
      refine ⟨2936956119401949850850507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957970746267966567233671 2936956119401949850850507)
      ·
        refine ⟨4405434179102924776275761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936956119401949850850507 4405434179102924776275761)
        ·
          refine ⟨3304075634327193582206821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4405434179102924776275761 3304075634327193582206821)
          ·
            refine ⟨619514181436348796663779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3304075634327193582206821 619514181436348796663779)
            ·
              refine ⟨929271272154523194995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619514181436348796663779 929271272154523194995669)
              ·
                refine ⟨21779795441121637382711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 929271272154523194995669 21779795441121637382711)
                ·
                  rfl

theorem cell21_286308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_286308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286308 prefixEnd_286308 := by exact prefixLift 286308
  have htrace : WordTrace (prefixWord ++ tailWord_286308) baseStart_286308 baseEnd_286308 := by
    simpa [prefixWord, tailWord_286308, baseEnd_286308] using wordTrace_append hprefix tailTrace_286308
  have hstable : (prefixWord ++ tailWord_286308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286308).length < 2 ^ (prefixWord ++ tailWord_286308).sum := by decide
  have hdescent : baseEnd_286308 < baseStart_286308 := by decide
  rcases family_descends (prefixWord ++ tailWord_286308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286325 : List Nat := [1, 3, 4, 2, 1, 3, 7]
def baseStart_286325 : Nat := 118140960795 + 286325 * 2 ^ 59
def prefixEnd_286325 : Nat := 4983230072969 + 3 ^ 40 * 286325 * 2
def baseEnd_286325 : Nat := 7260362883886295596085

theorem tailTrace_286325 : CollatzResearch.WordTrace tailWord_286325 prefixEnd_286325 7260362883886295596085 := by
  unfold tailWord_286325
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443130687700900261948429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6962087125133933507965619 10443130687700900261948429)
  ·
    refine ⟨3916174007887837598230661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10443130687700900261948429 3916174007887837598230661)
    ·
      refine ⟨734282626478969549668249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3916174007887837598230661 734282626478969549668249)
      ·
        refine ⟨550711969859227162251187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 734282626478969549668249 550711969859227162251187)
        ·
          refine ⟨826067954788840743376781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550711969859227162251187 826067954788840743376781)
          ·
            refine ⟨309775483045815278766293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 826067954788840743376781 309775483045815278766293)
            ·
              refine ⟨7260362883886295596085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 309775483045815278766293 7260362883886295596085)
              ·
                rfl

theorem cell21_286325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 7].length) (baseStart_286325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286325 prefixEnd_286325 := by exact prefixLift 286325
  have htrace : WordTrace (prefixWord ++ tailWord_286325) baseStart_286325 baseEnd_286325 := by
    simpa [prefixWord, tailWord_286325, baseEnd_286325] using wordTrace_append hprefix tailTrace_286325
  have hstable : (prefixWord ++ tailWord_286325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286325).length < 2 ^ (prefixWord ++ tailWord_286325).sum := by decide
  have hdescent : baseEnd_286325 < baseStart_286325 := by decide
  rcases family_descends (prefixWord ++ tailWord_286325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286390 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_286390 : Nat := 118140960795 + 286390 * 2 ^ 59
def prefixEnd_286390 : Nat := 4983230072969 + 3 ^ 40 * 286390 * 2
def baseEnd_286390 : Nat := 65358099840550991781299

theorem tailTrace_286390 : CollatzResearch.WordTrace tailWord_286390 prefixEnd_286390 65358099840550991781299 := by
  unfold tailWord_286390
  simp only [CollatzResearch.WordTrace]
  refine ⟨652843839529088522691539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6963667621643610908709749 652843839529088522691539)
  ·
    refine ⟨979265759293632784037309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652843839529088522691539 979265759293632784037309)
    ·
      refine ⟨367224659735112294013991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 979265759293632784037309 367224659735112294013991)
      ·
        refine ⟨550836989602668441020987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367224659735112294013991 550836989602668441020987)
        ·
          refine ⟨826255484404002661531481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550836989602668441020987 826255484404002661531481)
          ·
            refine ⟨619691613303001996148611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826255484404002661531481 619691613303001996148611)
            ·
              refine ⟨929537419954502994222917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619691613303001996148611 929537419954502994222917)
              ·
                refine ⟨174288266241469311416797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 929537419954502994222917 174288266241469311416797)
                ·
                  refine ⟨65358099840550991781299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174288266241469311416797 65358099840550991781299)
                  ·
                    rfl

theorem cell21_286390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_286390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286390 prefixEnd_286390 := by exact prefixLift 286390
  have htrace : WordTrace (prefixWord ++ tailWord_286390) baseStart_286390 baseEnd_286390 := by
    simpa [prefixWord, tailWord_286390, baseEnd_286390] using wordTrace_append hprefix tailTrace_286390
  have hstable : (prefixWord ++ tailWord_286390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286390).length < 2 ^ (prefixWord ++ tailWord_286390).sum := by decide
  have hdescent : baseEnd_286390 < baseStart_286390 := by decide
  rcases family_descends (prefixWord ++ tailWord_286390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286522 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_286522 : Nat := 118140960795 + 286522 * 2 ^ 59
def prefixEnd_286522 : Nat := 4983230072969 + 3 ^ 40 * 286522 * 2
def baseEnd_286522 : Nat := 65388224038948095581029

theorem tailTrace_286522 : CollatzResearch.WordTrace tailWord_286522 prefixEnd_286522 65388224038948095581029 := by
  unfold tailWord_286522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612578966996800726717455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6966877245324801937913213 2612578966996800726717455)
  ·
    refine ⟨3918868450495201090076183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2612578966996800726717455 3918868450495201090076183)
    ·
      refine ⟨5878302675742801635114275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3918868450495201090076183 5878302675742801635114275)
      ·
        refine ⟨8817454013614202452671413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5878302675742801635114275 8817454013614202452671413)
        ·
          refine ⟨826636313776331479937945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8817454013614202452671413 826636313776331479937945)
          ·
            refine ⟨619977235332248609953459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826636313776331479937945 619977235332248609953459)
            ·
              refine ⟨929965852998372914930189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619977235332248609953459 929965852998372914930189)
              ·
                refine ⟨348737194874389843098821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929965852998372914930189 348737194874389843098821)
                ·
                  refine ⟨65388224038948095581029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348737194874389843098821 65388224038948095581029)
                  ·
                    rfl

theorem cell21_286522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_286522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286522 prefixEnd_286522 := by exact prefixLift 286522
  have htrace : WordTrace (prefixWord ++ tailWord_286522) baseStart_286522 baseEnd_286522 := by
    simpa [prefixWord, tailWord_286522, baseEnd_286522] using wordTrace_append hprefix tailTrace_286522
  have hstable : (prefixWord ++ tailWord_286522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286522).length < 2 ^ (prefixWord ++ tailWord_286522).sum := by decide
  have hdescent : baseEnd_286522 < baseStart_286522 := by decide
  rcases family_descends (prefixWord ++ tailWord_286522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286570 : List Nat := [3, 1, 3, 4, 1, 2, 1, 6]
def baseStart_286570 : Nat := 118140960795 + 286570 * 2 ^ 59
def prefixEnd_286570 : Nat := 4983230072969 + 3 ^ 40 * 286570 * 2
def baseEnd_286570 : Nat := 21799726097636892926977

theorem tailTrace_286570 : CollatzResearch.WordTrace tailWord_286570 prefixEnd_286570 21799726097636892926977 := by
  unfold tailWord_286570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613016642953326776154291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6968044381208871403078109 2613016642953326776154291)
  ·
    refine ⟨3919524964429990164231437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613016642953326776154291 3919524964429990164231437)
    ·
      refine ⟨1469821861661246311586789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3919524964429990164231437 1469821861661246311586789)
      ·
        refine ⟨275591599061483683422523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1469821861661246311586789 275591599061483683422523)
        ·
          refine ⟨413387398592225525133785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275591599061483683422523 413387398592225525133785)
          ·
            refine ⟨310040548944169143850339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413387398592225525133785 310040548944169143850339)
            ·
              refine ⟨465060823416253715775509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310040548944169143850339 465060823416253715775509)
              ·
                refine ⟨21799726097636892926977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 465060823416253715775509 21799726097636892926977)
                ·
                  rfl

theorem cell21_286570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_286570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286570 prefixEnd_286570 := by exact prefixLift 286570
  have htrace : WordTrace (prefixWord ++ tailWord_286570) baseStart_286570 baseEnd_286570 := by
    simpa [prefixWord, tailWord_286570, baseEnd_286570] using wordTrace_append hprefix tailTrace_286570
  have hstable : (prefixWord ++ tailWord_286570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286570).length < 2 ^ (prefixWord ++ tailWord_286570).sum := by decide
  have hdescent : baseEnd_286570 < baseStart_286570 := by decide
  rcases family_descends (prefixWord ++ tailWord_286570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286612 : List Nat := [2, 4, 2, 1, 1, 3, 8]
def baseStart_286612 : Nat := 118140960795 + 286612 * 2 ^ 59
def prefixEnd_286612 : Nat := 4983230072969 + 3 ^ 40 * 286612 * 2
def baseEnd_286612 : Nat := 7267640362791993231205

theorem tailTrace_286612 : CollatzResearch.WordTrace tailWord_286612 prefixEnd_286612 7267640362791993231205 := by
  unfold tailWord_286612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226799218830574138823045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6969065625107432185097393 5226799218830574138823045)
  ·
    refine ⟨980024853530732651029321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5226799218830574138823045 980024853530732651029321)
    ·
      refine ⟨735018640148049488271991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 980024853530732651029321 735018640148049488271991)
      ·
        refine ⟨1102527960222074232407987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735018640148049488271991 1102527960222074232407987)
        ·
          refine ⟨1653791940333111348611981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102527960222074232407987 1653791940333111348611981)
          ·
            refine ⟨620171977624916755729493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1653791940333111348611981 620171977624916755729493)
            ·
              refine ⟨7267640362791993231205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 620171977624916755729493 7267640362791993231205)
              ·
                rfl

theorem cell21_286612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 8].length) (baseStart_286612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286612 prefixEnd_286612 := by exact prefixLift 286612
  have htrace : WordTrace (prefixWord ++ tailWord_286612) baseStart_286612 baseEnd_286612 := by
    simpa [prefixWord, tailWord_286612, baseEnd_286612] using wordTrace_append hprefix tailTrace_286612
  have hstable : (prefixWord ++ tailWord_286612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286612).length < 2 ^ (prefixWord ++ tailWord_286612).sum := by decide
  have hdescent : baseEnd_286612 < baseStart_286612 := by decide
  rcases family_descends (prefixWord ++ tailWord_286612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286677 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 3]
def baseStart_286677 : Nat := 118140960795 + 286677 * 2 ^ 59
def prefixEnd_286677 : Nat := 4983230072969 + 3 ^ 40 * 286677 * 2
def baseEnd_286677 : Nat := 65423597150702270497379

theorem tailTrace_286677 : CollatzResearch.WordTrace tailWord_286677 prefixEnd_286677 65423597150702270497379 := by
  unfold tailWord_286677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10455969182425664378762285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6970646121617109585841523 10455969182425664378762285)
  ·
    refine ⟨3920988443409624142035857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10455969182425664378762285 3920988443409624142035857)
    ·
      refine ⟨2940741332557218106526893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3920988443409624142035857 2940741332557218106526893)
      ·
        refine ⟨1102777999708956789947585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2940741332557218106526893 1102777999708956789947585)
        ·
          refine ⟨827083499781717592460689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102777999708956789947585 827083499781717592460689)
          ·
            refine ⟨620312624836288194345517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827083499781717592460689 620312624836288194345517)
            ·
              refine ⟨232617234313608072879569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620312624836288194345517 232617234313608072879569)
              ·
                refine ⟨174462925735206054659677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232617234313608072879569 174462925735206054659677)
                ·
                  refine ⟨65423597150702270497379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174462925735206054659677 65423597150702270497379)
                  ·
                    rfl

theorem cell21_286677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_286677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286677 prefixEnd_286677 := by exact prefixLift 286677
  have htrace : WordTrace (prefixWord ++ tailWord_286677) baseStart_286677 baseEnd_286677 := by
    simpa [prefixWord, tailWord_286677, baseEnd_286677] using wordTrace_append hprefix tailTrace_286677
  have hstable : (prefixWord ++ tailWord_286677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286677).length < 2 ^ (prefixWord ++ tailWord_286677).sum := by decide
  have hdescent : baseEnd_286677 < baseStart_286677 := by decide
  rcases family_descends (prefixWord ++ tailWord_286677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286691 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 4]
def baseStart_286691 : Nat := 118140960795 + 286691 * 2 ^ 59
def prefixEnd_286691 : Nat := 4983230072969 + 3 ^ 40 * 286691 * 2
def baseEnd_286691 : Nat := 65426792141441357264017

theorem tailTrace_286691 : CollatzResearch.WordTrace tailWord_286691 prefixEnd_286691 65426792141441357264017 := by
  unfold tailWord_286691
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456479804374944769771927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6970986536249963179847951 10456479804374944769771927)
  ·
    refine ⟨15684719706562417154657891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10456479804374944769771927 15684719706562417154657891)
    ·
      refine ⟨23527079559843625731986837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15684719706562417154657891 23527079559843625731986837)
      ·
        refine ⟨1102831854367669956186883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23527079559843625731986837 1102831854367669956186883)
        ·
          refine ⟨1654247781551504934280325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102831854367669956186883 1654247781551504934280325)
          ·
            refine ⟨310171459040907175177561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1654247781551504934280325 310171459040907175177561)
            ·
              refine ⟨232628594280680381383171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310171459040907175177561 232628594280680381383171)
              ·
                refine ⟨348942891421020572074757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232628594280680381383171 348942891421020572074757)
                ·
                  refine ⟨65426792141441357264017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348942891421020572074757 65426792141441357264017)
                  ·
                    rfl

theorem cell21_286691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4].length) (baseStart_286691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286691 prefixEnd_286691 := by exact prefixLift 286691
  have htrace : WordTrace (prefixWord ++ tailWord_286691) baseStart_286691 baseEnd_286691 := by
    simpa [prefixWord, tailWord_286691, baseEnd_286691] using wordTrace_append hprefix tailTrace_286691
  have hstable : (prefixWord ++ tailWord_286691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286691).length < 2 ^ (prefixWord ++ tailWord_286691).sum := by decide
  have hdescent : baseEnd_286691 < baseStart_286691 := by decide
  rcases family_descends (prefixWord ++ tailWord_286691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286823 : List Nat := [1, 1, 5, 1, 1, 2, 3, 7]
def baseStart_286823 : Nat := 118140960795 + 286823 * 2 ^ 59
def prefixEnd_286823 : Nat := 4983230072969 + 3 ^ 40 * 286823 * 2
def baseEnd_286823 : Nat := 21818972113279487021249

theorem tailTrace_286823 : CollatzResearch.WordTrace tailWord_286823 prefixEnd_286823 21818972113279487021249 := by
  unfold tailWord_286823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461294239896731313577123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6974196159931154209051415 10461294239896731313577123)
  ·
    refine ⟨15691941359845096970365685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10461294239896731313577123 15691941359845096970365685)
    ·
      refine ⟨1471119502485477840971783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15691941359845096970365685 1471119502485477840971783)
      ·
        refine ⟨2206679253728216761457675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471119502485477840971783 2206679253728216761457675)
        ·
          refine ⟨3310018880592325142186513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206679253728216761457675 3310018880592325142186513)
          ·
            refine ⟨2482514160444243856639885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3310018880592325142186513 2482514160444243856639885)
            ·
              refine ⟨930942810166591446239957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2482514160444243856639885 930942810166591446239957)
              ·
                refine ⟨21818972113279487021249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 930942810166591446239957 21818972113279487021249)
                ·
                  rfl

theorem cell21_286823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_286823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286823 prefixEnd_286823 := by exact prefixLift 286823
  have htrace : WordTrace (prefixWord ++ tailWord_286823) baseStart_286823 baseEnd_286823 := by
    simpa [prefixWord, tailWord_286823, baseEnd_286823] using wordTrace_append hprefix tailTrace_286823
  have hstable : (prefixWord ++ tailWord_286823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286823).length < 2 ^ (prefixWord ++ tailWord_286823).sum := by decide
  have hdescent : baseEnd_286823 < baseStart_286823 := by decide
  rcases family_descends (prefixWord ++ tailWord_286823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286916 : List Nat := [2, 3, 3, 1, 2, 1, 3, 6]
def baseStart_286916 : Nat := 118140960795 + 286916 * 2 ^ 59
def prefixEnd_286916 : Nat := 4983230072969 + 3 ^ 40 * 286916 * 2
def baseEnd_286916 : Nat := 21826046735630322004519

theorem tailTrace_286916 : CollatzResearch.WordTrace tailWord_286916 prefixEnd_286916 21826046735630322004519 := by
  unfold tailWord_286916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232343114279904098356301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6976457485706538797808401 5232343114279904098356301)
  ·
    refine ⟨1962128667854964036883613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5232343114279904098356301 1962128667854964036883613)
    ·
      refine ⟨735798250445611513831355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1962128667854964036883613 735798250445611513831355)
      ·
        refine ⟨1103697375668417270747033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735798250445611513831355 1103697375668417270747033)
        ·
          refine ⟨827773031751312953060275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103697375668417270747033 827773031751312953060275)
          ·
            refine ⟨1241659547626969429590413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827773031751312953060275 1241659547626969429590413)
            ·
              refine ⟨465622330360113536096405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241659547626969429590413 465622330360113536096405)
              ·
                refine ⟨21826046735630322004519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 465622330360113536096405 21826046735630322004519)
                ·
                  rfl

theorem cell21_286916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_286916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286916 prefixEnd_286916 := by exact prefixLift 286916
  have htrace : WordTrace (prefixWord ++ tailWord_286916) baseStart_286916 baseEnd_286916 := by
    simpa [prefixWord, tailWord_286916, baseEnd_286916] using wordTrace_append hprefix tailTrace_286916
  have hstable : (prefixWord ++ tailWord_286916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286916).length < 2 ^ (prefixWord ++ tailWord_286916).sum := by decide
  have hdescent : baseEnd_286916 < baseStart_286916 := by decide
  rcases family_descends (prefixWord ++ tailWord_286916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286930 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_286930 : Nat := 118140960795 + 286930 * 2 ^ 59
def prefixEnd_286930 : Nat := 4983230072969 + 3 ^ 40 * 286930 * 2
def baseEnd_286930 : Nat := 65481335197630052780195

theorem tailTrace_286930 : CollatzResearch.WordTrace tailWord_286930 prefixEnd_286930 65481335197630052780195 := by
  unfold tailWord_286930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616299212627272146930561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6976797900339392391814829 2616299212627272146930561)
  ·
    refine ⟨1962224409470454110197921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2616299212627272146930561 1962224409470454110197921)
    ·
      refine ⟨1471668307102840582648441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1962224409470454110197921 1471668307102840582648441)
      ·
        refine ⟨1103751230327130436986331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1471668307102840582648441 1103751230327130436986331)
        ·
          refine ⟨1655626845490695655479497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103751230327130436986331 1655626845490695655479497)
          ·
            refine ⟨1241720134118021741609623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655626845490695655479497 1241720134118021741609623)
            ·
              refine ⟨1862580201177032612414435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241720134118021741609623 1862580201177032612414435)
              ·
                refine ⟨2793870301765548918621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862580201177032612414435 2793870301765548918621653)
                ·
                  refine ⟨65481335197630052780195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2793870301765548918621653 65481335197630052780195)
                  ·
                    rfl

theorem cell21_286930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_286930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286930 prefixEnd_286930 := by exact prefixLift 286930
  have htrace : WordTrace (prefixWord ++ tailWord_286930) baseStart_286930 baseEnd_286930 := by
    simpa [prefixWord, tailWord_286930, baseEnd_286930] using wordTrace_append hprefix tailTrace_286930
  have hstable : (prefixWord ++ tailWord_286930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286930).length < 2 ^ (prefixWord ++ tailWord_286930).sum := by decide
  have hdescent : baseEnd_286930 < baseStart_286930 := by decide
  rcases family_descends (prefixWord ++ tailWord_286930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286933 : List Nat := [1, 3, 2, 4, 2, 1, 3, 5]
def baseStart_286933 : Nat := 118140960795 + 286933 * 2 ^ 59
def prefixEnd_286933 : Nat := 4983230072969 + 3 ^ 40 * 286933 * 2
def baseEnd_286933 : Nat := 21827339946167571410063

theorem tailTrace_286933 : CollatzResearch.WordTrace tailWord_286933 prefixEnd_286933 21827339946167571410063 := by
  unfold tailWord_286933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465306269498220100081453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6976870846332146733387635 10465306269498220100081453)
  ·
    refine ⟨3924489851061832537530545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10465306269498220100081453 3924489851061832537530545)
    ·
      refine ⟨2943367388296374403147909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924489851061832537530545 2943367388296374403147909)
      ·
        refine ⟨551881385305570200590233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2943367388296374403147909 551881385305570200590233)
        ·
          refine ⟨413911038979177650442675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551881385305570200590233 413911038979177650442675)
          ·
            refine ⟨620866558468766475664013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413911038979177650442675 620866558468766475664013)
            ·
              refine ⟨232824959425787428374005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620866558468766475664013 232824959425787428374005)
              ·
                refine ⟨21827339946167571410063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232824959425787428374005 21827339946167571410063)
                ·
                  rfl

theorem cell21_286933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 5].length) (baseStart_286933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286933 prefixEnd_286933 := by exact prefixLift 286933
  have htrace : WordTrace (prefixWord ++ tailWord_286933) baseStart_286933 baseEnd_286933 := by
    simpa [prefixWord, tailWord_286933, baseEnd_286933] using wordTrace_append hprefix tailTrace_286933
  have hstable : (prefixWord ++ tailWord_286933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286933).length < 2 ^ (prefixWord ++ tailWord_286933).sum := by decide
  have hdescent : baseEnd_286933 < baseStart_286933 := by decide
  rcases family_descends (prefixWord ++ tailWord_286933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286944 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_286944 : Nat := 118140960795 + 286944 * 2 ^ 59
def prefixEnd_286944 : Nat := 4983230072969 + 3 ^ 40 * 286944 * 2
def baseEnd_286944 : Nat := 65484530188369139546833

theorem tailTrace_286944 : CollatzResearch.WordTrace tailWord_286944 prefixEnd_286944 65484530188369139546833 := by
  unfold tailWord_286944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232853736229184489365943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6977138314972245985821257 5232853736229184489365943)
  ·
    refine ⟨7849280604343776734048915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5232853736229184489365943 7849280604343776734048915)
    ·
      refine ⟨11773920906515665101073373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849280604343776734048915 11773920906515665101073373)
      ·
        refine ⟨4415220339943374412902515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11773920906515665101073373 4415220339943374412902515)
        ·
          refine ⟨6622830509915061619353773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415220339943374412902515 6622830509915061619353773)
          ·
            refine ⟨2483561441218148107257665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6622830509915061619353773 2483561441218148107257665)
            ·
              refine ⟨1862671080913611080443249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483561441218148107257665 1862671080913611080443249)
              ·
                refine ⟨1397003310685208310332437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862671080913611080443249 1397003310685208310332437)
                ·
                  refine ⟨65484530188369139546833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1397003310685208310332437 65484530188369139546833)
                  ·
                    rfl

theorem cell21_286944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_286944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286944 prefixEnd_286944 := by exact prefixLift 286944
  have htrace : WordTrace (prefixWord ++ tailWord_286944) baseStart_286944 baseEnd_286944 := by
    simpa [prefixWord, tailWord_286944, baseEnd_286944] using wordTrace_append hprefix tailTrace_286944
  have hstable : (prefixWord ++ tailWord_286944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286944).length < 2 ^ (prefixWord ++ tailWord_286944).sum := by decide
  have hdescent : baseEnd_286944 < baseStart_286944 := by decide
  rcases family_descends (prefixWord ++ tailWord_286944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286961 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_286961 : Nat := 118140960795 + 286961 * 2 ^ 59
def prefixEnd_286961 : Nat := 4983230072969 + 3 ^ 40 * 286961 * 2
def baseEnd_286961 : Nat := 65488409819980887763465

theorem tailTrace_286961 : CollatzResearch.WordTrace tailWord_286961 prefixEnd_286961 65488409819980887763465 := by
  unfold tailWord_286961
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466327513396780882100737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6977551675597853921400491 10466327513396780882100737)
  ·
    refine ⟨7849745635047585661575553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10466327513396780882100737 7849745635047585661575553)
    ·
      refine ⟨5887309226285689246181665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7849745635047585661575553 5887309226285689246181665)
      ·
        refine ⟨4415481919714266934636249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5887309226285689246181665 4415481919714266934636249)
        ·
          refine ⟨3311611439785700200977187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415481919714266934636249 3311611439785700200977187)
          ·
            refine ⟨4967417159678550301465781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311611439785700200977187 4967417159678550301465781)
            ·
              refine ⟨465695358719864090762417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4967417159678550301465781 465695358719864090762417)
              ·
                refine ⟨349271519039898068071813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465695358719864090762417 349271519039898068071813)
                ·
                  refine ⟨65488409819980887763465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 349271519039898068071813 65488409819980887763465)
                  ·
                    rfl

theorem cell21_286961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_286961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_286961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_286961 prefixEnd_286961 := by exact prefixLift 286961
  have htrace : WordTrace (prefixWord ++ tailWord_286961) baseStart_286961 baseEnd_286961 := by
    simpa [prefixWord, tailWord_286961, baseEnd_286961] using wordTrace_append hprefix tailTrace_286961
  have hstable : (prefixWord ++ tailWord_286961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286961).length < 2 ^ (prefixWord ++ tailWord_286961).sum := by decide
  have hdescent : baseEnd_286961 < baseStart_286961 := by decide
  rcases family_descends (prefixWord ++ tailWord_286961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287015 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 3]
def baseStart_287015 : Nat := 118140960795 + 287015 * 2 ^ 59
def prefixEnd_287015 : Nat := 4983230072969 + 3 ^ 40 * 287015 * 2
def baseEnd_287015 : Nat := 65500733355688793863355

theorem tailTrace_287015 : CollatzResearch.WordTrace tailWord_287015 prefixEnd_287015 65500733355688793863355 := by
  unfold tailWord_287015
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468297055201148104566499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6978864703467432069710999 10468297055201148104566499)
  ·
    refine ⟨15702445582801722156849749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10468297055201148104566499 15702445582801722156849749)
    ·
      refine ⟨184013034173457681525583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 15702445582801722156849749 184013034173457681525583)
      ·
        refine ⟨276019551260186522288375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184013034173457681525583 276019551260186522288375)
        ·
          refine ⟨414029326890279783432563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276019551260186522288375 414029326890279783432563)
          ·
            refine ⟨621043990335419675148845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414029326890279783432563 621043990335419675148845)
            ·
              refine ⟨232891496375782378180817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 621043990335419675148845 232891496375782378180817)
              ·
                refine ⟨174668622281836783635613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232891496375782378180817 174668622281836783635613)
                ·
                  refine ⟨65500733355688793863355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174668622281836783635613 65500733355688793863355)
                  ·
                    rfl

theorem cell21_287015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3].length) (baseStart_287015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287015 prefixEnd_287015 := by exact prefixLift 287015
  have htrace : WordTrace (prefixWord ++ tailWord_287015) baseStart_287015 baseEnd_287015 := by
    simpa [prefixWord, tailWord_287015, baseEnd_287015] using wordTrace_append hprefix tailTrace_287015
  have hstable : (prefixWord ++ tailWord_287015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287015).length < 2 ^ (prefixWord ++ tailWord_287015).sum := by decide
  have hdescent : baseEnd_287015 < baseStart_287015 := by decide
  rcases family_descends (prefixWord ++ tailWord_287015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287020 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_287020 : Nat := 118140960795 + 287020 * 2 ^ 59
def prefixEnd_287020 : Nat := 4983230072969 + 3 ^ 40 * 287020 * 2
def baseEnd_287020 : Nat := 65501874423809896280011

theorem tailTrace_287020 : CollatzResearch.WordTrace tailWord_287020 prefixEnd_287020 65501874423809896280011 := by
  unfold tailWord_287020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234239710091516979249257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6978986280122022638999009 5234239710091516979249257)
  ·
    refine ⟨3925679782568637734436943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5234239710091516979249257 3925679782568637734436943)
    ·
      refine ⟨5888519673852956601655415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925679782568637734436943 5888519673852956601655415)
      ·
        refine ⟨8832779510779434902483123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888519673852956601655415 8832779510779434902483123)
        ·
          refine ⟨13249169266169152353724685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8832779510779434902483123 13249169266169152353724685)
          ·
            refine ⟨4968438474813432132646757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13249169266169152353724685 4968438474813432132646757)
            ·
              refine ⟨931582214027518524871267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4968438474813432132646757 931582214027518524871267)
              ·
                refine ⟨1397373321041277787306901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931582214027518524871267 1397373321041277787306901)
                ·
                  refine ⟨65501874423809896280011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1397373321041277787306901 65501874423809896280011)
                  ·
                    rfl

theorem cell21_287020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_287020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287020 prefixEnd_287020 := by exact prefixLift 287020
  have htrace : WordTrace (prefixWord ++ tailWord_287020) baseStart_287020 baseEnd_287020 := by
    simpa [prefixWord, tailWord_287020, baseEnd_287020] using wordTrace_append hprefix tailTrace_287020
  have hstable : (prefixWord ++ tailWord_287020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287020).length < 2 ^ (prefixWord ++ tailWord_287020).sum := by decide
  have hdescent : baseEnd_287020 < baseStart_287020 := by decide
  rcases family_descends (prefixWord ++ tailWord_287020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287068 : List Nat := [2, 2, 4, 3, 1, 9]
def baseStart_287068 : Nat := 118140960795 + 287068 * 2 ^ 59
def prefixEnd_287068 : Nat := 4983230072969 + 3 ^ 40 * 287068 * 2
def baseEnd_287068 : Nat := 2426401062139721462219

theorem tailTrace_287068 : CollatzResearch.WordTrace tailWord_287068 prefixEnd_287068 2426401062139721462219 := by
  unfold tailWord_287068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235115062004569078122929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6980153416006092104163905 5235115062004569078122929)
  ·
    refine ⟨3926336296503426808592197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5235115062004569078122929 3926336296503426808592197)
    ·
      refine ⟨736188055594392526611037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3926336296503426808592197 736188055594392526611037)
      ·
        refine ⟨276070520847897197479139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 736188055594392526611037 276070520847897197479139)
        ·
          refine ⟨414105781271845796218709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276070520847897197479139 414105781271845796218709)
          ·
            refine ⟨2426401062139721462219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 414105781271845796218709 2426401062139721462219)
            ·
              rfl

theorem cell21_287068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 9].length) (baseStart_287068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287068 prefixEnd_287068 := by exact prefixLift 287068
  have htrace : WordTrace (prefixWord ++ tailWord_287068) baseStart_287068 baseEnd_287068 := by
    simpa [prefixWord, tailWord_287068, baseEnd_287068] using wordTrace_append hprefix tailTrace_287068
  have hstable : (prefixWord ++ tailWord_287068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287068).length < 2 ^ (prefixWord ++ tailWord_287068).sum := by decide
  have hdescent : baseEnd_287068 < baseStart_287068 := by decide
  rcases family_descends (prefixWord ++ tailWord_287068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287130 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_287130 : Nat := 118140960795 + 287130 * 2 ^ 59
def prefixEnd_287130 : Nat := 4983230072969 + 3 ^ 40 * 287130 * 2
def baseEnd_287130 : Nat := 65526977922474149446453

theorem tailTrace_287130 : CollatzResearch.WordTrace tailWord_287130 prefixEnd_287130 65526977922474149446453 := by
  unfold tailWord_287130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618122862446130686250711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6981660966523015163335229 2618122862446130686250711)
  ·
    refine ⟨3927184293669196029376067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618122862446130686250711 3927184293669196029376067)
    ·
      refine ⟨5890776440503794044064101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3927184293669196029376067 5890776440503794044064101)
      ·
        refine ⟨1104520582594461383262019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5890776440503794044064101 1104520582594461383262019)
        ·
          refine ⟨1656780873891692074893029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104520582594461383262019 1656780873891692074893029)
          ·
            refine ⟨310646413854692264042443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1656780873891692074893029 310646413854692264042443)
            ·
              refine ⟨465969620782038396063665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310646413854692264042443 465969620782038396063665)
              ·
                refine ⟨349477215586528797047749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465969620782038396063665 349477215586528797047749)
                ·
                  refine ⟨65526977922474149446453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 349477215586528797047749 65526977922474149446453)
                  ·
                    rfl

theorem cell21_287130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_287130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287130 prefixEnd_287130 := by exact prefixLift 287130
  have htrace : WordTrace (prefixWord ++ tailWord_287130) baseStart_287130 baseEnd_287130 := by
    simpa [prefixWord, tailWord_287130, baseEnd_287130] using wordTrace_append hprefix tailTrace_287130
  have hstable : (prefixWord ++ tailWord_287130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287130).length < 2 ^ (prefixWord ++ tailWord_287130).sum := by decide
  have hdescent : baseEnd_287130 < baseStart_287130 := by decide
  rcases family_descends (prefixWord ++ tailWord_287130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287175 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 3]
def baseStart_287175 : Nat := 118140960795 + 287175 * 2 ^ 59
def prefixEnd_287175 : Nat := 4983230072969 + 3 ^ 40 * 287175 * 2
def baseEnd_287175 : Nat := 65537247535564071196361

theorem tailTrace_287175 : CollatzResearch.WordTrace tailWord_287175 prefixEnd_287175 65537247535564071196361 := by
  unfold tailWord_287175
  simp only [CollatzResearch.WordTrace]
  refine ⟨10474132734621495430390979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6982755156414330286927319 10474132734621495430390979)
  ·
    refine ⟨15711199101932243145586469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10474132734621495430390979 15711199101932243145586469)
    ·
      refine ⟨2945849831612295589797463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15711199101932243145586469 2945849831612295589797463)
      ·
        refine ⟨4418774747418443384696195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945849831612295589797463 4418774747418443384696195)
        ·
          refine ⟨6628162121127665077044293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418774747418443384696195 6628162121127665077044293)
          ·
            refine ⟨1242780397711437201945805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6628162121127665077044293 1242780397711437201945805)
            ·
              refine ⟨466042649141788950729677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1242780397711437201945805 466042649141788950729677)
              ·
                refine ⟨174765993428170856523629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466042649141788950729677 174765993428170856523629)
                ·
                  refine ⟨65537247535564071196361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174765993428170856523629 65537247535564071196361)
                  ·
                    rfl

theorem cell21_287175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3].length) (baseStart_287175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287175 prefixEnd_287175 := by exact prefixLift 287175
  have htrace : WordTrace (prefixWord ++ tailWord_287175) baseStart_287175 baseEnd_287175 := by
    simpa [prefixWord, tailWord_287175, baseEnd_287175] using wordTrace_append hprefix tailTrace_287175
  have hstable : (prefixWord ++ tailWord_287175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287175).length < 2 ^ (prefixWord ++ tailWord_287175).sum := by decide
  have hdescent : baseEnd_287175 < baseStart_287175 := by decide
  rcases family_descends (prefixWord ++ tailWord_287175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287217 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_287217 : Nat := 118140960795 + 287217 * 2 ^ 59
def prefixEnd_287217 : Nat := 4983230072969 + 3 ^ 40 * 287217 * 2
def baseEnd_287217 : Nat := 65546832507781331496275

theorem tailTrace_287217 : CollatzResearch.WordTrace tailWord_287217 prefixEnd_287217 65546832507781331496275 := by
  unfold tailWord_287217
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475664600469336603419905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6983776400312891068946603 10475664600469336603419905)
  ·
    refine ⟨7856748450352002452564929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10475664600469336603419905 7856748450352002452564929)
    ·
      refine ⟨5892561337764001839423697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7856748450352002452564929 5892561337764001839423697)
      ·
        refine ⟨4419421003323001379567773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5892561337764001839423697 4419421003323001379567773)
        ·
          refine ⟨1657282876246125517337915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4419421003323001379567773 1657282876246125517337915)
          ·
            refine ⟨2485924314369188276006873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657282876246125517337915 2485924314369188276006873)
            ·
              refine ⟨1864443235776891207005155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485924314369188276006873 1864443235776891207005155)
              ·
                refine ⟨2796664853665336810507733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864443235776891207005155 2796664853665336810507733)
                ·
                  refine ⟨65546832507781331496275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2796664853665336810507733 65546832507781331496275)
                  ·
                    rfl

theorem cell21_287217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_287217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287217 prefixEnd_287217 := by exact prefixLift 287217
  have htrace : WordTrace (prefixWord ++ tailWord_287217) baseStart_287217 baseEnd_287217 := by
    simpa [prefixWord, tailWord_287217, baseEnd_287217] using wordTrace_append hprefix tailTrace_287217
  have hstable : (prefixWord ++ tailWord_287217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287217).length < 2 ^ (prefixWord ++ tailWord_287217).sum := by decide
  have hdescent : baseEnd_287217 < baseStart_287217 := by decide
  rcases family_descends (prefixWord ++ tailWord_287217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287330 : List Nat := [3, 3, 2, 3, 1, 2, 2, 5]
def baseStart_287330 : Nat := 118140960795 + 287330 * 2 ^ 59
def prefixEnd_287330 : Nat := 4983230072969 + 3 ^ 40 * 287330 * 2
def baseEnd_287330 : Nat := 21857540215772748704237

theorem tailTrace_287330 : CollatzResearch.WordTrace tailWord_287330 prefixEnd_287330 21857540215772748704237 := by
  unfold tailWord_287330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619946512264989225570861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6986524032706637934855629 2619946512264989225570861)
  ·
    refine ⟨982479942099370959589073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2619946512264989225570861 982479942099370959589073)
    ·
      refine ⟨736859956574528219691805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 982479942099370959589073 736859956574528219691805)
      ·
        refine ⟨276322483715448082384427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 736859956574528219691805 276322483715448082384427)
        ·
          refine ⟨414483725573172123576641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276322483715448082384427 414483725573172123576641)
          ·
            refine ⟨310862794179879092682481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414483725573172123576641 310862794179879092682481)
            ·
              refine ⟨233147095634909319511861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310862794179879092682481 233147095634909319511861)
              ·
                refine ⟨21857540215772748704237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233147095634909319511861 21857540215772748704237)
                ·
                  rfl

theorem cell21_287330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_287330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287330 prefixEnd_287330 := by exact prefixLift 287330
  have htrace : WordTrace (prefixWord ++ tailWord_287330) baseStart_287330 baseEnd_287330 := by
    simpa [prefixWord, tailWord_287330, baseEnd_287330] using wordTrace_append hprefix tailTrace_287330
  have hstable : (prefixWord ++ tailWord_287330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287330).length < 2 ^ (prefixWord ++ tailWord_287330).sum := by decide
  have hdescent : baseEnd_287330 < baseStart_287330 := by decide
  rcases family_descends (prefixWord ++ tailWord_287330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287344 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_287344 : Nat := 118140960795 + 287344 * 2 ^ 59
def prefixEnd_287344 : Nat := 4983230072969 + 3 ^ 40 * 287344 * 2
def baseEnd_287344 : Nat := 65575815638057332879349

theorem tailTrace_287344 : CollatzResearch.WordTrace tailWord_287344 prefixEnd_287344 65575815638057332879349 := by
  unfold tailWord_287344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5240148335504618646646543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6986864447339491528862057 5240148335504618646646543)
  ·
    refine ⟨7860222503256927969969815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5240148335504618646646543 7860222503256927969969815)
    ·
      refine ⟨11790333754885391954954723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860222503256927969969815 11790333754885391954954723)
      ·
        refine ⟨17685500632328087932432085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11790333754885391954954723 17685500632328087932432085)
        ·
          refine ⟨414503921070189560916377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17685500632328087932432085 414503921070189560916377)
          ·
            refine ⟨310877940802642170687283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414503921070189560916377 310877940802642170687283)
            ·
              refine ⟨466316911203963256030925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310877940802642170687283 466316911203963256030925)
              ·
                refine ⟨174868841701486221011597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466316911203963256030925 174868841701486221011597)
                ·
                  refine ⟨65575815638057332879349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174868841701486221011597 65575815638057332879349)
                  ·
                    rfl

theorem cell21_287344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_287344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287344 prefixEnd_287344 := by exact prefixLift 287344
  have htrace : WordTrace (prefixWord ++ tailWord_287344) baseStart_287344 baseEnd_287344 := by
    simpa [prefixWord, tailWord_287344, baseEnd_287344] using wordTrace_append hprefix tailTrace_287344
  have hstable : (prefixWord ++ tailWord_287344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287344).length < 2 ^ (prefixWord ++ tailWord_287344).sum := by decide
  have hdescent : baseEnd_287344 < baseStart_287344 := by decide
  rcases family_descends (prefixWord ++ tailWord_287344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287524 : List Nat := [2, 3, 1, 3, 4, 1, 7]
def baseStart_287524 : Nat := 118140960795 + 287524 * 2 ^ 59
def prefixEnd_287524 : Nat := 4983230072969 + 3 ^ 40 * 287524 * 2
def baseEnd_287524 : Nat := 7290766010046335542109

theorem tailTrace_287524 : CollatzResearch.WordTrace tailWord_287524 prefixEnd_287524 7290766010046335542109 := by
  unfold tailWord_287524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243430905178564017422813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6991241206904752023230417 5243430905178564017422813)
  ·
    refine ⟨1966286589441961506533555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5243430905178564017422813 1966286589441961506533555)
    ·
      refine ⟨2949429884162942259800333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966286589441961506533555 2949429884162942259800333)
      ·
        refine ⟨1106036206561103347425125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2949429884162942259800333 1106036206561103347425125)
        ·
          refine ⟨207381788730206877642211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1106036206561103347425125 207381788730206877642211)
          ·
            refine ⟨311072683095310316463317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207381788730206877642211 311072683095310316463317)
            ·
              refine ⟨7290766010046335542109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 311072683095310316463317 7290766010046335542109)
              ·
                rfl

theorem cell21_287524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 7].length) (baseStart_287524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287524 prefixEnd_287524 := by exact prefixLift 287524
  have htrace : WordTrace (prefixWord ++ tailWord_287524) baseStart_287524 baseEnd_287524 := by
    simpa [prefixWord, tailWord_287524, baseEnd_287524] using wordTrace_append hprefix tailTrace_287524
  have hstable : (prefixWord ++ tailWord_287524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287524).length < 2 ^ (prefixWord ++ tailWord_287524).sum := by decide
  have hdescent : baseEnd_287524 < baseStart_287524 := by decide
  rcases family_descends (prefixWord ++ tailWord_287524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287586 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_287586 : Nat := 118140960795 + 287586 * 2 ^ 59
def prefixEnd_287586 : Nat := 4983230072969 + 3 ^ 40 * 287586 * 2
def baseEnd_287586 : Nat := 65631043335118689845521

theorem tailTrace_287586 : CollatzResearch.WordTrace tailWord_287586 prefixEnd_287586 65631043335118689845521 := by
  unfold tailWord_287586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622280784033128155900653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6992748757421675082401741 2622280784033128155900653)
  ·
    refine ⟨983355294012423058462745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2622280784033128155900653 983355294012423058462745)
    ·
      refine ⟨737516470509317293847059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983355294012423058462745 737516470509317293847059)
      ·
        refine ⟨1106274705763975940770589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737516470509317293847059 1106274705763975940770589)
        ·
          refine ⟨414853014661490977788971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1106274705763975940770589 414853014661490977788971)
          ·
            refine ⟨622279521992236466683457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414853014661490977788971 622279521992236466683457)
            ·
              refine ⟨466709641494177350012593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622279521992236466683457 466709641494177350012593)
              ·
                refine ⟨350032231120633012509445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466709641494177350012593 350032231120633012509445)
                ·
                  refine ⟨65631043335118689845521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350032231120633012509445 65631043335118689845521)
                  ·
                    rfl

theorem cell21_287586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_287586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287586 prefixEnd_287586 := by exact prefixLift 287586
  have htrace : WordTrace (prefixWord ++ tailWord_287586) baseStart_287586 baseEnd_287586 := by
    simpa [prefixWord, tailWord_287586, baseEnd_287586] using wordTrace_append hprefix tailTrace_287586
  have hstable : (prefixWord ++ tailWord_287586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287586).length < 2 ^ (prefixWord ++ tailWord_287586).sum := by decide
  have hdescent : baseEnd_287586 < baseStart_287586 := by decide
  rcases family_descends (prefixWord ++ tailWord_287586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287597 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_287597 : Nat := 118140960795 + 287597 * 2 ^ 59
def prefixEnd_287597 : Nat := 4983230072969 + 3 ^ 40 * 287597 * 2
def baseEnd_287597 : Nat := 65633553684985115162165

theorem tailTrace_287597 : CollatzResearch.WordTrace tailWord_287597 prefixEnd_287597 65633553684985115162165 := by
  unfold tailWord_287597
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489524339092661502253045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993016226061774334835363 10489524339092661502253045)
  ·
    refine ⟨983392906789937015836223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10489524339092661502253045 983392906789937015836223)
    ·
      refine ⟨1475089360184905523754335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983392906789937015836223 1475089360184905523754335)
      ·
        refine ⟨2212634040277358285631503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475089360184905523754335 2212634040277358285631503)
        ·
          refine ⟨3318951060416037428447255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212634040277358285631503 3318951060416037428447255)
          ·
            refine ⟨4978426590624056142670883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318951060416037428447255 4978426590624056142670883)
            ·
              refine ⟨7467639885936084214006325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978426590624056142670883 7467639885936084214006325)
              ·
                refine ⟨700091239306507895063093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7467639885936084214006325 700091239306507895063093)
                ·
                  refine ⟨65633553684985115162165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 700091239306507895063093 65633553684985115162165)
                  ·
                    rfl

theorem cell21_287597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_287597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287597 prefixEnd_287597 := by exact prefixLift 287597
  have htrace : WordTrace (prefixWord ++ tailWord_287597) baseStart_287597 baseEnd_287597 := by
    simpa [prefixWord, tailWord_287597, baseEnd_287597] using wordTrace_append hprefix tailTrace_287597
  have hstable : (prefixWord ++ tailWord_287597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287597).length < 2 ^ (prefixWord ++ tailWord_287597).sum := by decide
  have hdescent : baseEnd_287597 < baseStart_287597 := by decide
  rcases family_descends (prefixWord ++ tailWord_287597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287673 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_287673 : Nat := 118140960795 + 287673 * 2 ^ 59
def prefixEnd_287673 : Nat := 4983230072969 + 3 ^ 40 * 287673 * 2
def baseEnd_287673 : Nat := 65650897920425871895343

theorem tailTrace_287673 : CollatzResearch.WordTrace tailWord_287673 prefixEnd_287673 65650897920425871895343 := by
  unfold tailWord_287673
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492296286817326482019673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6994864191211550988013115 10492296286817326482019673)
  ·
    refine ⟨7869222215112994861514755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10492296286817326482019673 7869222215112994861514755)
    ·
      refine ⟨11803833322669492292272133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7869222215112994861514755 11803833322669492292272133)
      ·
        refine ⟨2213218748000529804801025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11803833322669492292272133 2213218748000529804801025)
        ·
          refine ⟨1659914061000397353600769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213218748000529804801025 1659914061000397353600769)
          ·
            refine ⟨1244935545750298015200577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659914061000397353600769 1244935545750298015200577)
            ·
              refine ⟨933701659312723511400433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244935545750298015200577 933701659312723511400433)
              ·
                refine ⟨700276244484542633550325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933701659312723511400433 700276244484542633550325)
                ·
                  refine ⟨65650897920425871895343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 700276244484542633550325 65650897920425871895343)
                  ·
                    rfl

theorem cell21_287673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_287673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287673 prefixEnd_287673 := by exact prefixLift 287673
  have htrace : WordTrace (prefixWord ++ tailWord_287673) baseStart_287673 baseEnd_287673 := by
    simpa [prefixWord, tailWord_287673, baseEnd_287673] using wordTrace_append hprefix tailTrace_287673
  have hstable : (prefixWord ++ tailWord_287673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287673).length < 2 ^ (prefixWord ++ tailWord_287673).sum := by decide
  have hdescent : baseEnd_287673 < baseStart_287673 := by decide
  rcases family_descends (prefixWord ++ tailWord_287673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287687 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_287687 : Nat := 118140960795 + 287687 * 2 ^ 59
def prefixEnd_287687 : Nat := 4983230072969 + 3 ^ 40 * 287687 * 2
def baseEnd_287687 : Nat := 65654092911164958661981

theorem tailTrace_287687 : CollatzResearch.WordTrace tailWord_287687 prefixEnd_287687 65654092911164958661981 := by
  unfold tailWord_287687
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492806908766606873029315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6995204605844404582019543 10492806908766606873029315)
  ·
    refine ⟨15739210363149910309543973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10492806908766606873029315 15739210363149910309543973)
    ·
      refine ⟨2951101943090608183039495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15739210363149910309543973 2951101943090608183039495)
      ·
        refine ⟨4426652914635912274559243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951101943090608183039495 4426652914635912274559243)
        ·
          refine ⟨6639979371953868411838865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4426652914635912274559243 6639979371953868411838865)
          ·
            refine ⟨4979984528965401308879149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6639979371953868411838865 4979984528965401308879149)
            ·
              refine ⟨1867494198362025490829681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4979984528965401308879149 1867494198362025490829681)
              ·
                refine ⟨1400620648771519118122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867494198362025490829681 1400620648771519118122261)
                ·
                  refine ⟨65654092911164958661981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1400620648771519118122261 65654092911164958661981)
                  ·
                    rfl

theorem cell21_287687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_287687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287687 prefixEnd_287687 := by exact prefixLift 287687
  have htrace : WordTrace (prefixWord ++ tailWord_287687) baseStart_287687 baseEnd_287687 := by
    simpa [prefixWord, tailWord_287687, baseEnd_287687] using wordTrace_append hprefix tailTrace_287687
  have hstable : (prefixWord ++ tailWord_287687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287687).length < 2 ^ (prefixWord ++ tailWord_287687).sum := by decide
  have hdescent : baseEnd_287687 < baseStart_287687 := by decide
  rcases family_descends (prefixWord ++ tailWord_287687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287808 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_287808 : Nat := 118140960795 + 287808 * 2 ^ 59
def prefixEnd_287808 : Nat := 4983230072969 + 3 ^ 40 * 287808 * 2
def baseEnd_287808 : Nat := 65681706759695637145067

theorem tailTrace_287808 : CollatzResearch.WordTrace tailWord_287808 prefixEnd_287808 65681706759695637145067 := by
  unfold tailWord_287808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248610070664122269092039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6998146760885496358789385 5248610070664122269092039)
  ·
    refine ⟨7872915105996183403638059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5248610070664122269092039 7872915105996183403638059)
    ·
      refine ⟨11809372658994275105457089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7872915105996183403638059 11809372658994275105457089)
      ·
        refine ⟨8857029494245706329092817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11809372658994275105457089 8857029494245706329092817)
        ·
          refine ⟨6642772120684279746819613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8857029494245706329092817 6642772120684279746819613)
          ·
            refine ⟨2491039545256604905057355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6642772120684279746819613 2491039545256604905057355)
            ·
              refine ⟨3736559317884907357586033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491039545256604905057355 3736559317884907357586033)
              ·
                refine ⟨2802419488413680518189525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3736559317884907357586033 2802419488413680518189525)
                ·
                  refine ⟨65681706759695637145067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2802419488413680518189525 65681706759695637145067)
                  ·
                    rfl

theorem cell21_287808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_287808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287808 prefixEnd_287808 := by exact prefixLift 287808
  have htrace : WordTrace (prefixWord ++ tailWord_287808) baseStart_287808 baseEnd_287808 := by
    simpa [prefixWord, tailWord_287808, baseEnd_287808] using wordTrace_append hprefix tailTrace_287808
  have hstable : (prefixWord ++ tailWord_287808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287808).length < 2 ^ (prefixWord ++ tailWord_287808).sum := by decide
  have hdescent : baseEnd_287808 < baseStart_287808 := by decide
  rcases family_descends (prefixWord ++ tailWord_287808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287814 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_287814 : Nat := 118140960795 + 287814 * 2 ^ 59
def prefixEnd_287814 : Nat := 4983230072969 + 3 ^ 40 * 287814 * 2
def baseEnd_287814 : Nat := 65683076041440960045055

theorem tailTrace_287814 : CollatzResearch.WordTrace tailWord_287814 prefixEnd_287814 65683076041440960045055 := by
  unfold tailWord_287814
  simp only [CollatzResearch.WordTrace]
  refine ⟨328044968103328361340703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6998292652871005041934997 328044968103328361340703)
  ·
    refine ⟨492067452154992542011055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328044968103328361340703 492067452154992542011055)
    ·
      refine ⟨738101178232488813016583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492067452154992542011055 738101178232488813016583)
      ·
        refine ⟨1107151767348733219524875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738101178232488813016583 1107151767348733219524875)
        ·
          refine ⟨1660727651023099829287313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107151767348733219524875 1660727651023099829287313)
          ·
            refine ⟨1245545738267324871965485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660727651023099829287313 1245545738267324871965485)
            ·
              refine ⟨467079651850246826987057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1245545738267324871965485 467079651850246826987057)
              ·
                refine ⟨350309738887685120240293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467079651850246826987057 350309738887685120240293)
                ·
                  refine ⟨65683076041440960045055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350309738887685120240293 65683076041440960045055)
                  ·
                    rfl

theorem cell21_287814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_287814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287814 prefixEnd_287814 := by exact prefixLift 287814
  have htrace : WordTrace (prefixWord ++ tailWord_287814) baseStart_287814 baseEnd_287814 := by
    simpa [prefixWord, tailWord_287814, baseEnd_287814] using wordTrace_append hprefix tailTrace_287814
  have hstable : (prefixWord ++ tailWord_287814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287814).length < 2 ^ (prefixWord ++ tailWord_287814).sum := by decide
  have hdescent : baseEnd_287814 < baseStart_287814 := by decide
  rcases family_descends (prefixWord ++ tailWord_287814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287842 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_287842 : Nat := 118140960795 + 287842 * 2 ^ 59
def prefixEnd_287842 : Nat := 4983230072969 + 3 ^ 40 * 287842 * 2
def baseEnd_287842 : Nat := 65689466022919133578331

theorem tailTrace_287842 : CollatzResearch.WordTrace tailWord_287842 prefixEnd_287842 65689466022919133578331 := by
  unfold tailWord_287842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624615055801267086230445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6998973482136712229947853 2624615055801267086230445)
  ·
    refine ⟨984230645925475157336417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2624615055801267086230445 984230645925475157336417)
    ·
      refine ⟨738172984444106368002313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 984230645925475157336417 738172984444106368002313)
      ·
        refine ⟨553629738333079776001735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738172984444106368002313 553629738333079776001735)
        ·
          refine ⟨830444607499619664002603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553629738333079776001735 830444607499619664002603)
          ·
            refine ⟨1245666911249429496003905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830444607499619664002603 1245666911249429496003905)
            ·
              refine ⟨934250183437072122002929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245666911249429496003905 934250183437072122002929)
              ·
                refine ⟨700687637577804091502197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934250183437072122002929 700687637577804091502197)
                ·
                  refine ⟨65689466022919133578331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 700687637577804091502197 65689466022919133578331)
                  ·
                    rfl

theorem cell21_287842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_287842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287842 prefixEnd_287842 := by exact prefixLift 287842
  have htrace : WordTrace (prefixWord ++ tailWord_287842) baseStart_287842 baseEnd_287842 := by
    simpa [prefixWord, tailWord_287842, baseEnd_287842] using wordTrace_append hprefix tailTrace_287842
  have hstable : (prefixWord ++ tailWord_287842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287842).length < 2 ^ (prefixWord ++ tailWord_287842).sum := by decide
  have hdescent : baseEnd_287842 < baseStart_287842 := by decide
  rcases family_descends (prefixWord ++ tailWord_287842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287890 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_287890 : Nat := 118140960795 + 287890 * 2 ^ 59
def prefixEnd_287890 : Nat := 4983230072969 + 3 ^ 40 * 287890 * 2
def baseEnd_287890 : Nat := 65700420276881716778233

theorem tailTrace_287890 : CollatzResearch.WordTrace tailWord_287890 prefixEnd_287890 65700420276881716778233 := by
  unfold tailWord_287890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625052731757793135667281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7000140618020781695112749 2625052731757793135667281)
  ·
    refine ⟨1968789548818344851750461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2625052731757793135667281 1968789548818344851750461)
    ·
      refine ⟨738296080806879319406423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1968789548818344851750461 738296080806879319406423)
      ·
        refine ⟨1107444121210318979109635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738296080806879319406423 1107444121210318979109635)
        ·
          refine ⟨1661166181815478468664453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107444121210318979109635 1661166181815478468664453)
          ·
            refine ⟨311468659090402212874585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1661166181815478468664453 311468659090402212874585)
            ·
              refine ⟨233601494317801659655939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311468659090402212874585 233601494317801659655939)
              ·
                refine ⟨350402241476702489483909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233601494317801659655939 350402241476702489483909)
                ·
                  refine ⟨65700420276881716778233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350402241476702489483909 65700420276881716778233)
                  ·
                    rfl

theorem cell21_287890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_287890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287890 prefixEnd_287890 := by exact prefixLift 287890
  have htrace : WordTrace (prefixWord ++ tailWord_287890) baseStart_287890 baseEnd_287890 := by
    simpa [prefixWord, tailWord_287890, baseEnd_287890] using wordTrace_append hprefix tailTrace_287890
  have hstable : (prefixWord ++ tailWord_287890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287890).length < 2 ^ (prefixWord ++ tailWord_287890).sum := by decide
  have hdescent : baseEnd_287890 < baseStart_287890 := by decide
  rcases family_descends (prefixWord ++ tailWord_287890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287929 : List Nat := [1, 2, 1, 4, 1, 12]
def baseStart_287929 : Nat := 118140960795 + 287929 * 2 ^ 59
def prefixEnd_287929 : Nat := 4983230072969 + 3 ^ 40 * 287929 * 2
def baseEnd_287929 : Nat := 2433678541045419097339

theorem tailTrace_287929 : CollatzResearch.WordTrace tailWord_287929 prefixEnd_287929 2433678541045419097339 := by
  unfold tailWord_287929
  simp only [CollatzResearch.WordTrace]
  refine ⟨10501633373889882203338841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7001088915926588135559227 10501633373889882203338841)
  ·
    refine ⟨7876225030417411652504131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10501633373889882203338841 7876225030417411652504131)
    ·
      refine ⟨11814337545626117478756197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7876225030417411652504131 11814337545626117478756197)
      ·
        refine ⟨2215188289804897027266787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11814337545626117478756197 2215188289804897027266787)
        ·
          refine ⟨3322782434707345540900181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215188289804897027266787 3322782434707345540900181)
          ·
            refine ⟨2433678541045419097339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3322782434707345540900181 2433678541045419097339)
            ·
              rfl

theorem cell21_287929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 12].length) (baseStart_287929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287929 prefixEnd_287929 := by exact prefixLift 287929
  have htrace : WordTrace (prefixWord ++ tailWord_287929) baseStart_287929 baseEnd_287929 := by
    simpa [prefixWord, tailWord_287929, baseEnd_287929] using wordTrace_append hprefix tailTrace_287929
  have hstable : (prefixWord ++ tailWord_287929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287929).length < 2 ^ (prefixWord ++ tailWord_287929).sum := by decide
  have hdescent : baseEnd_287929 < baseStart_287929 := by decide
  rcases family_descends (prefixWord ++ tailWord_287929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287932 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_287932 : Nat := 118140960795 + 287932 * 2 ^ 59
def prefixEnd_287932 : Nat := 4983230072969 + 3 ^ 40 * 287932 * 2
def baseEnd_287932 : Nat := 65710005249098977078147

theorem tailTrace_287932 : CollatzResearch.WordTrace tailWord_287932 prefixEnd_287932 65710005249098977078147 := by
  unfold tailWord_287932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250871396439506857849025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7001161861919342477132033 5250871396439506857849025)
  ·
    refine ⟨3938153547329630143386769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5250871396439506857849025 3938153547329630143386769)
    ·
      refine ⟨2953615160497222607540077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3938153547329630143386769 2953615160497222607540077)
      ·
        refine ⟨1107605685186458477827529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2953615160497222607540077 1107605685186458477827529)
        ·
          refine ⟨830704263889843858370647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107605685186458477827529 830704263889843858370647)
          ·
            refine ⟨1246056395834765787555971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830704263889843858370647 1246056395834765787555971)
            ·
              refine ⟨1869084593752148681333957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246056395834765787555971 1869084593752148681333957)
              ·
                refine ⟨350453361328527877750117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1869084593752148681333957 350453361328527877750117)
                ·
                  refine ⟨65710005249098977078147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350453361328527877750117 65710005249098977078147)
                  ·
                    rfl

theorem cell21_287932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_287932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287932 prefixEnd_287932 := by exact prefixLift 287932
  have htrace : WordTrace (prefixWord ++ tailWord_287932) baseStart_287932 baseEnd_287932 := by
    simpa [prefixWord, tailWord_287932, baseEnd_287932] using wordTrace_append hprefix tailTrace_287932
  have hstable : (prefixWord ++ tailWord_287932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287932).length < 2 ^ (prefixWord ++ tailWord_287932).sum := by decide
  have hdescent : baseEnd_287932 < baseStart_287932 := by decide
  rcases family_descends (prefixWord ++ tailWord_287932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287938 : List Nat := [3, 5, 1, 1, 3, 1, 1, 6]
def baseStart_287938 : Nat := 118140960795 + 287938 * 2 ^ 59
def prefixEnd_287938 : Nat := 4983230072969 + 3 ^ 40 * 287938 * 2
def baseEnd_287938 : Nat := 21903791510281433326045

theorem tailTrace_287938 : CollatzResearch.WordTrace tailWord_287938 prefixEnd_287938 21903791510281433326045 := by
  unfold tailWord_287938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625490407714319185104117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7001307753904851160277645 2625490407714319185104117)
  ·
    refine ⟨246139725723217423603511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2625490407714319185104117 246139725723217423603511)
    ·
      refine ⟨369209588584826135405267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246139725723217423603511 369209588584826135405267)
      ·
        refine ⟨553814382877239203107901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369209588584826135405267 553814382877239203107901)
        ·
          refine ⟨207680393578964701165463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 553814382877239203107901 207680393578964701165463)
          ·
            refine ⟨311520590368447051748195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207680393578964701165463 311520590368447051748195)
            ·
              refine ⟨467280885552670577622293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311520590368447051748195 467280885552670577622293)
              ·
                refine ⟨21903791510281433326045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 467280885552670577622293 21903791510281433326045)
                ·
                  rfl

theorem cell21_287938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_287938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287938 prefixEnd_287938 := by exact prefixLift 287938
  have htrace : WordTrace (prefixWord ++ tailWord_287938) baseStart_287938 baseEnd_287938 := by
    simpa [prefixWord, tailWord_287938, baseEnd_287938] using wordTrace_append hprefix tailTrace_287938
  have hstable : (prefixWord ++ tailWord_287938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287938).length < 2 ^ (prefixWord ++ tailWord_287938).sum := by decide
  have hdescent : baseEnd_287938 < baseStart_287938 := by decide
  rcases family_descends (prefixWord ++ tailWord_287938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287946 : List Nat := [3, 1, 2, 1, 3, 2, 3, 6]
def baseStart_287946 : Nat := 118140960795 + 287946 * 2 ^ 59
def prefixEnd_287946 : Nat := 4983230072969 + 3 ^ 40 * 287946 * 2
def baseEnd_287946 : Nat := 21904400079946021281595

theorem tailTrace_287946 : CollatzResearch.WordTrace tailWord_287946 prefixEnd_287946 21904400079946021281595 := by
  unfold tailWord_287946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625563353707073526676923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7001502276552196071138461 2625563353707073526676923)
  ·
    refine ⟨3938345030560610290015385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2625563353707073526676923 3938345030560610290015385)
    ·
      refine ⟨2953758772920457717511539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3938345030560610290015385 2953758772920457717511539)
      ·
        refine ⟨4430638159380686576267309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953758772920457717511539 4430638159380686576267309)
        ·
          refine ⟨1661489309767757466100241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4430638159380686576267309 1661489309767757466100241)
          ·
            refine ⟨1246116982325818099575181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661489309767757466100241 1246116982325818099575181)
            ·
              refine ⟨467293868372181787340693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1246116982325818099575181 467293868372181787340693)
              ·
                refine ⟨21904400079946021281595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 467293868372181787340693 21904400079946021281595)
                ·
                  rfl

theorem cell21_287946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_287946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_287946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_287946 prefixEnd_287946 := by exact prefixLift 287946
  have htrace : WordTrace (prefixWord ++ tailWord_287946) baseStart_287946 baseEnd_287946 := by
    simpa [prefixWord, tailWord_287946, baseEnd_287946] using wordTrace_append hprefix tailTrace_287946
  have hstable : (prefixWord ++ tailWord_287946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287946).length < 2 ^ (prefixWord ++ tailWord_287946).sum := by decide
  have hdescent : baseEnd_287946 < baseStart_287946 := by decide
  rcases family_descends (prefixWord ++ tailWord_287946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288005 : List Nat := [1, 3, 1, 1, 2, 1, 4, 8]
def baseStart_288005 : Nat := 118140960795 + 288005 * 2 ^ 59
def prefixEnd_288005 : Nat := 4983230072969 + 3 ^ 40 * 288005 * 2
def baseEnd_288005 : Nat := 21908888281222357453777

theorem tailTrace_288005 : CollatzResearch.WordTrace tailWord_288005 prefixEnd_288005 21908888281222357453777 := by
  unfold tailWord_288005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504405321614547183105469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7002936881076364788736979 10504405321614547183105469)
  ·
    refine ⟨3939151995605455193664551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10504405321614547183105469 3939151995605455193664551)
    ·
      refine ⟨5908727993408182790496827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939151995605455193664551 5908727993408182790496827)
      ·
        refine ⟨8863091990112274185745241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908727993408182790496827 8863091990112274185745241)
        ·
          refine ⟨6647318992584205639308931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8863091990112274185745241 6647318992584205639308931)
          ·
            refine ⟨9970978488876308458963397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647318992584205639308931 9970978488876308458963397)
            ·
              refine ⟨1869558466664307836055637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9970978488876308458963397 1869558466664307836055637)
              ·
                refine ⟨21908888281222357453777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1869558466664307836055637 21908888281222357453777)
                ·
                  rfl

theorem cell21_288005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_288005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288005 prefixEnd_288005 := by exact prefixLift 288005
  have htrace : WordTrace (prefixWord ++ tailWord_288005) baseStart_288005 baseEnd_288005 := by
    simpa [prefixWord, tailWord_288005, baseEnd_288005] using wordTrace_append hprefix tailTrace_288005
  have hstable : (prefixWord ++ tailWord_288005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288005).length < 2 ^ (prefixWord ++ tailWord_288005).sum := by decide
  have hdescent : baseEnd_288005 < baseStart_288005 := by decide
  rcases family_descends (prefixWord ++ tailWord_288005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288053 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_288053 : Nat := 118140960795 + 288053 * 2 ^ 59
def prefixEnd_288053 : Nat := 4983230072969 + 3 ^ 40 * 288053 * 2
def baseEnd_288053 : Nat := 65737619097629655561233

theorem tailTrace_288053 : CollatzResearch.WordTrace tailWord_288053 prefixEnd_288053 65737619097629655561233 := by
  unfold tailWord_288053
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506156025440651380852813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7004104016960434253901875 10506156025440651380852813)
  ·
    refine ⟨3939808509540244267819805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10506156025440651380852813 3939808509540244267819805)
    ·
      refine ⟨1477428191077591600432427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3939808509540244267819805 1477428191077591600432427)
      ·
        refine ⟨2216142286616387400648641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477428191077591600432427 2216142286616387400648641)
        ·
          refine ⟨1662106714962290550486481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216142286616387400648641 1662106714962290550486481)
          ·
            refine ⟨1246580036221717912864861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662106714962290550486481 1246580036221717912864861)
            ·
              refine ⟨467467513583144217324323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1246580036221717912864861 467467513583144217324323)
              ·
                refine ⟨701201270374716325986485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467467513583144217324323 701201270374716325986485)
                ·
                  refine ⟨65737619097629655561233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 701201270374716325986485 65737619097629655561233)
                  ·
                    rfl

theorem cell21_288053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_288053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288053 prefixEnd_288053 := by exact prefixLift 288053
  have htrace : WordTrace (prefixWord ++ tailWord_288053) baseStart_288053 baseEnd_288053 := by
    simpa [prefixWord, tailWord_288053, baseEnd_288053] using wordTrace_append hprefix tailTrace_288053
  have hstable : (prefixWord ++ tailWord_288053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288053).length < 2 ^ (prefixWord ++ tailWord_288053).sum := by decide
  have hdescent : baseEnd_288053 < baseStart_288053 := by decide
  rcases family_descends (prefixWord ++ tailWord_288053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288081 : List Nat := [1, 2, 2, 1, 4, 1, 1, 9]
def baseStart_288081 : Nat := 118140960795 + 288081 * 2 ^ 59
def prefixEnd_288081 : Nat := 4983230072969 + 3 ^ 40 * 288081 * 2
def baseEnd_288081 : Nat := 21914669693035943031503

theorem tailTrace_288081 : CollatzResearch.WordTrace tailWord_288081 prefixEnd_288081 21914669693035943031503 := by
  unfold tailWord_288081
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507177269339212162872097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7004784846226141441914731 10507177269339212162872097)
  ·
    refine ⟨7880382952004409122154073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10507177269339212162872097 7880382952004409122154073)
    ·
      refine ⟨5910287214003306841615555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7880382952004409122154073 5910287214003306841615555)
      ·
        refine ⟨8865430821004960262423333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910287214003306841615555 8865430821004960262423333)
        ·
          refine ⟨1662268278938430049204375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8865430821004960262423333 1662268278938430049204375)
          ·
            refine ⟨2493402418407645073806563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662268278938430049204375 2493402418407645073806563)
            ·
              refine ⟨3740103627611467610709845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493402418407645073806563 3740103627611467610709845)
              ·
                refine ⟨21914669693035943031503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3740103627611467610709845 21914669693035943031503)
                ·
                  rfl

theorem cell21_288081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_288081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288081 prefixEnd_288081 := by exact prefixLift 288081
  have htrace : WordTrace (prefixWord ++ tailWord_288081) baseStart_288081 baseEnd_288081 := by
    simpa [prefixWord, tailWord_288081, baseEnd_288081] using wordTrace_append hprefix tailTrace_288081
  have hstable : (prefixWord ++ tailWord_288081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288081).length < 2 ^ (prefixWord ++ tailWord_288081).sum := by decide
  have hdescent : baseEnd_288081 < baseStart_288081 := by decide
  rcases family_descends (prefixWord ++ tailWord_288081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288104 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_288104 : Nat := 118140960795 + 288104 * 2 ^ 59
def prefixEnd_288104 : Nat := 4983230072969 + 3 ^ 40 * 288104 * 2
def baseEnd_288104 : Nat := 65749257992464900211129

theorem tailTrace_288104 : CollatzResearch.WordTrace tailWord_288104 prefixEnd_288104 65749257992464900211129 := by
  unfold tailWord_288104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254008074127943545479683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7005344098837258060639577 5254008074127943545479683)
  ·
    refine ⟨7881012111191915318219525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5254008074127943545479683 7881012111191915318219525)
    ·
      refine ⟨1477689770848484122166161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7881012111191915318219525 1477689770848484122166161)
      ·
        refine ⟨1108267328136363091624621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1477689770848484122166161 1108267328136363091624621)
        ·
          refine ⟨415600248051136159359233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1108267328136363091624621 415600248051136159359233)
          ·
            refine ⟨311700186038352119519425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415600248051136159359233 311700186038352119519425)
            ·
              refine ⟨233775139528764089639569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311700186038352119519425 233775139528764089639569)
              ·
                refine ⟨175331354646573067229677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233775139528764089639569 175331354646573067229677)
                ·
                  refine ⟨65749257992464900211129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175331354646573067229677 65749257992464900211129)
                  ·
                    rfl

theorem cell21_288104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_288104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288104 prefixEnd_288104 := by exact prefixLift 288104
  have htrace : WordTrace (prefixWord ++ tailWord_288104) baseStart_288104 baseEnd_288104 := by
    simpa [prefixWord, tailWord_288104, baseEnd_288104] using wordTrace_append hprefix tailTrace_288104
  have hstable : (prefixWord ++ tailWord_288104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288104).length < 2 ^ (prefixWord ++ tailWord_288104).sum := by decide
  have hdescent : baseEnd_288104 < baseStart_288104 := by decide
  rcases family_descends (prefixWord ++ tailWord_288104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288112 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_288112 : Nat := 118140960795 + 288112 * 2 ^ 59
def prefixEnd_288112 : Nat := 4983230072969 + 3 ^ 40 * 288112 * 2
def baseEnd_288112 : Nat := 65751083701458664077779

theorem tailTrace_288112 : CollatzResearch.WordTrace tailWord_288112 prefixEnd_288112 65751083701458664077779 := by
  unfold tailWord_288112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254153966113452228625295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7005538621484602971500393 5254153966113452228625295)
  ·
    refine ⟨7881230949170178342937943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5254153966113452228625295 7881230949170178342937943)
    ·
      refine ⟨11821846423755267514406915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7881230949170178342937943 11821846423755267514406915)
      ·
        refine ⟨17732769635632901271610373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11821846423755267514406915 17732769635632901271610373)
        ·
          refine ⟨3324894306681168988426945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17732769635632901271610373 3324894306681168988426945)
          ·
            refine ⟨2493670730010876741320209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3324894306681168988426945 2493670730010876741320209)
            ·
              refine ⟨1870253047508157555990157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2493670730010876741320209 1870253047508157555990157)
              ·
                refine ⟨701344892815559083496309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1870253047508157555990157 701344892815559083496309)
                ·
                  refine ⟨65751083701458664077779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 701344892815559083496309 65751083701458664077779)
                  ·
                    rfl

theorem cell21_288112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_288112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288112 prefixEnd_288112 := by exact prefixLift 288112
  have htrace : WordTrace (prefixWord ++ tailWord_288112) baseStart_288112 baseEnd_288112 := by
    simpa [prefixWord, tailWord_288112, baseEnd_288112] using wordTrace_append hprefix tailTrace_288112
  have hstable : (prefixWord ++ tailWord_288112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288112).length < 2 ^ (prefixWord ++ tailWord_288112).sum := by decide
  have hdescent : baseEnd_288112 < baseStart_288112 := by decide
  rcases family_descends (prefixWord ++ tailWord_288112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288385 : List Nat := [1, 2, 4, 2, 1, 2, 9]
def baseStart_288385 : Nat := 118140960795 + 288385 * 2 ^ 59
def prefixEnd_288385 : Nat := 4983230072969 + 3 ^ 40 * 288385 * 2
def baseEnd_288385 : Nat := 7312598446763428447469

theorem tailTrace_288385 : CollatzResearch.WordTrace tailWord_288385 prefixEnd_288385 7312598446763428447469 := by
  unfold tailWord_288385
  simp only [CollatzResearch.WordTrace]
  refine ⟨10518265060237872081938609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7012176706825248054625739 10518265060237872081938609)
  ·
    refine ⟨7888698795178404061453957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10518265060237872081938609 7888698795178404061453957)
    ·
      refine ⟨1479131024095950761522617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7888698795178404061453957 1479131024095950761522617)
      ·
        refine ⟨1109348268071963071141963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479131024095950761522617 1109348268071963071141963)
        ·
          refine ⟨1664022402107944606712945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109348268071963071141963 1664022402107944606712945)
          ·
            refine ⟨1248016801580958455034709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664022402107944606712945 1248016801580958455034709)
            ·
              refine ⟨7312598446763428447469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1248016801580958455034709 7312598446763428447469)
              ·
                rfl

theorem cell21_288385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 9].length) (baseStart_288385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288385 prefixEnd_288385 := by exact prefixLift 288385
  have htrace : WordTrace (prefixWord ++ tailWord_288385) baseStart_288385 baseEnd_288385 := by
    simpa [prefixWord, tailWord_288385, baseEnd_288385] using wordTrace_append hprefix tailTrace_288385
  have hstable : (prefixWord ++ tailWord_288385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288385).length < 2 ^ (prefixWord ++ tailWord_288385).sum := by decide
  have hdescent : baseEnd_288385 < baseStart_288385 := by decide
  rcases family_descends (prefixWord ++ tailWord_288385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288447 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_288447 : Nat := 118140960795 + 288447 * 2 ^ 59
def prefixEnd_288447 : Nat := 4983230072969 + 3 ^ 40 * 288447 * 2
def baseEnd_288447 : Nat := 65827535265572525993761

theorem tailTrace_288447 : CollatzResearch.WordTrace tailWord_288447 prefixEnd_288447 65827535265572525993761 := by
  unfold tailWord_288447
  simp only [CollatzResearch.WordTrace]
  refine ⟨10520526386013256670695595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7013684257342171113797063 10520526386013256670695595)
  ·
    refine ⟨15780789579019885006043393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10520526386013256670695595 15780789579019885006043393)
    ·
      refine ⟨11835592184264913754532545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15780789579019885006043393 11835592184264913754532545)
      ·
        refine ⟨8876694138198685315899409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11835592184264913754532545 8876694138198685315899409)
        ·
          refine ⟨6657520603649013986924557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8876694138198685315899409 6657520603649013986924557)
          ·
            refine ⟨2496570226368380245096709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6657520603649013986924557 2496570226368380245096709)
            ·
              refine ⟨468106917444071295955633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2496570226368380245096709 468106917444071295955633)
              ·
                refine ⟨351080188083053471966725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468106917444071295955633 351080188083053471966725)
                ·
                  refine ⟨65827535265572525993761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351080188083053471966725 65827535265572525993761)
                  ·
                    rfl

theorem cell21_288447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_288447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288447 prefixEnd_288447 := by exact prefixLift 288447
  have htrace : WordTrace (prefixWord ++ tailWord_288447) baseStart_288447 baseEnd_288447 := by
    simpa [prefixWord, tailWord_288447, baseEnd_288447] using wordTrace_append hprefix tailTrace_288447
  have hstable : (prefixWord ++ tailWord_288447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288447).length < 2 ^ (prefixWord ++ tailWord_288447).sum := by decide
  have hdescent : baseEnd_288447 < baseStart_288447 := by decide
  rcases family_descends (prefixWord ++ tailWord_288447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288568 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_288568 : Nat := 118140960795 + 288568 * 2 ^ 59
def prefixEnd_288568 : Nat := 4983230072969 + 3 ^ 40 * 288568 * 2
def baseEnd_288568 : Nat := 65855149114103204476847

theorem tailTrace_288568 : CollatzResearch.WordTrace tailWord_288568 prefixEnd_288568 65855149114103204476847 := by
  unfold tailWord_288568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262469809287447167925179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7016626412383262890566905 5262469809287447167925179)
  ·
    refine ⟨7893704713931170751887769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5262469809287447167925179 7893704713931170751887769)
    ·
      refine ⟨5920278535448378063915827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7893704713931170751887769 5920278535448378063915827)
      ·
        refine ⟨8880417803172567095873741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920278535448378063915827 8880417803172567095873741)
        ·
          refine ⟨3330156676189712660952653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8880417803172567095873741 3330156676189712660952653)
          ·
            refine ⟨1248808753571142247857245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3330156676189712660952653 1248808753571142247857245)
            ·
              refine ⟨468303282589178342946467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1248808753571142247857245 468303282589178342946467)
              ·
                refine ⟨702454923883767514419701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468303282589178342946467 702454923883767514419701)
                ·
                  refine ⟨65855149114103204476847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702454923883767514419701 65855149114103204476847)
                  ·
                    rfl

theorem cell21_288568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_288568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288568 prefixEnd_288568 := by exact prefixLift 288568
  have htrace : WordTrace (prefixWord ++ tailWord_288568) baseStart_288568 baseEnd_288568 := by
    simpa [prefixWord, tailWord_288568, baseEnd_288568] using wordTrace_append hprefix tailTrace_288568
  have hstable : (prefixWord ++ tailWord_288568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288568).length < 2 ^ (prefixWord ++ tailWord_288568).sum := by decide
  have hdescent : baseEnd_288568 < baseStart_288568 := by decide
  rcases family_descends (prefixWord ++ tailWord_288568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288627 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_288627 : Nat := 118140960795 + 288627 * 2 ^ 59
def prefixEnd_288627 : Nat := 4983230072969 + 3 ^ 40 * 288627 * 2
def baseEnd_288627 : Nat := 65868613717932212993393

theorem tailTrace_288627 : CollatzResearch.WordTrace tailWord_288627 prefixEnd_288627 65868613717932212993393 := by
  unfold tailWord_288627
  simp only [CollatzResearch.WordTrace]
  refine ⟨10527091525361147412248135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7018061016907431608165423 10527091525361147412248135)
  ·
    refine ⟨15790637288041721118372203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10527091525361147412248135 15790637288041721118372203)
    ·
      refine ⟨23685955932062581677558305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15790637288041721118372203 23685955932062581677558305)
      ·
        refine ⟨17764466949046936258168729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23685955932062581677558305 17764466949046936258168729)
        ·
          refine ⟨13323350211785202193626547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17764466949046936258168729 13323350211785202193626547)
          ·
            refine ⟨19985025317677803290439821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13323350211785202193626547 19985025317677803290439821)
            ·
              refine ⟨7494384494129176233914933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19985025317677803290439821 7494384494129176233914933)
              ·
                refine ⟨702598546324610271929525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7494384494129176233914933 702598546324610271929525)
                ·
                  refine ⟨65868613717932212993393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702598546324610271929525 65868613717932212993393)
                  ·
                    rfl

theorem cell21_288627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_288627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288627 prefixEnd_288627 := by exact prefixLift 288627
  have htrace : WordTrace (prefixWord ++ tailWord_288627) baseStart_288627 baseEnd_288627 := by
    simpa [prefixWord, tailWord_288627, baseEnd_288627] using wordTrace_append hprefix tailTrace_288627
  have hstable : (prefixWord ++ tailWord_288627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288627).length < 2 ^ (prefixWord ++ tailWord_288627).sum := by decide
  have hdescent : baseEnd_288627 < baseStart_288627 := by decide
  rcases family_descends (prefixWord ++ tailWord_288627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288661 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 3]
def baseStart_288661 : Nat := 118140960795 + 288661 * 2 ^ 59
def prefixEnd_288661 : Nat := 4983230072969 + 3 ^ 40 * 288661 * 2
def baseEnd_288661 : Nat := 65876372981155709426657

theorem tailTrace_288661 : CollatzResearch.WordTrace tailWord_288661 prefixEnd_288661 65876372981155709426657 := by
  unfold tailWord_288661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528331607237971218985837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7018887738158647479323891 10528331607237971218985837)
  ·
    refine ⟨3948124352714239207119689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10528331607237971218985837 3948124352714239207119689)
    ·
      refine ⟨2961093264535679405339767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3948124352714239207119689 2961093264535679405339767)
      ·
        refine ⟨4441639896803519108009651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961093264535679405339767 4441639896803519108009651)
        ·
          refine ⟨6662459845205278662014477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441639896803519108009651 6662459845205278662014477)
          ·
            refine ⟨2498422441951979498255429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6662459845205278662014477 2498422441951979498255429)
            ·
              refine ⟨468454207865996155922893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2498422441951979498255429 468454207865996155922893)
              ·
                refine ⟨175670327949748558471085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468454207865996155922893 175670327949748558471085)
                ·
                  refine ⟨65876372981155709426657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175670327949748558471085 65876372981155709426657)
                  ·
                    rfl

theorem cell21_288661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_288661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288661 prefixEnd_288661 := by exact prefixLift 288661
  have htrace : WordTrace (prefixWord ++ tailWord_288661) baseStart_288661 baseEnd_288661 := by
    simpa [prefixWord, tailWord_288661, baseEnd_288661] using wordTrace_append hprefix tailTrace_288661
  have hstable : (prefixWord ++ tailWord_288661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288661).length < 2 ^ (prefixWord ++ tailWord_288661).sum := by decide
  have hdescent : baseEnd_288661 < baseStart_288661 := by decide
  rcases family_descends (prefixWord ++ tailWord_288661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288703 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_288703 : Nat := 118140960795 + 288703 * 2 ^ 59
def prefixEnd_288703 : Nat := 4983230072969 + 3 ^ 40 * 288703 * 2
def baseEnd_288703 : Nat := 65885957953372969726571

theorem tailTrace_288703 : CollatzResearch.WordTrace tailWord_288703 prefixEnd_288703 65885957953372969726571 := by
  unfold tailWord_288703
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529863473085812392014763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7019908982057208261343175 10529863473085812392014763)
  ·
    refine ⟨15794795209628718588022145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10529863473085812392014763 15794795209628718588022145)
    ·
      refine ⟨11846096407221538941016609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15794795209628718588022145 11846096407221538941016609)
      ·
        refine ⟨8884572305416154205762457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11846096407221538941016609 8884572305416154205762457)
        ·
          refine ⟨6663429229062115654321843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8884572305416154205762457 6663429229062115654321843)
          ·
            refine ⟨9995143843593173481482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663429229062115654321843 9995143843593173481482765)
            ·
              refine ⟨3748178941347440055556037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9995143843593173481482765 3748178941347440055556037)
              ·
                refine ⟨702783551502645010416757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3748178941347440055556037 702783551502645010416757)
                ·
                  refine ⟨65885957953372969726571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702783551502645010416757 65885957953372969726571)
                  ·
                    rfl

theorem cell21_288703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_288703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288703 prefixEnd_288703 := by exact prefixLift 288703
  have htrace : WordTrace (prefixWord ++ tailWord_288703) baseStart_288703 baseEnd_288703 := by
    simpa [prefixWord, tailWord_288703, baseEnd_288703] using wordTrace_append hprefix tailTrace_288703
  have hstable : (prefixWord ++ tailWord_288703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288703).length < 2 ^ (prefixWord ++ tailWord_288703).sum := by decide
  have hdescent : baseEnd_288703 < baseStart_288703 := by decide
  rcases family_descends (prefixWord ++ tailWord_288703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288855 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_288855 : Nat := 118140960795 + 288855 * 2 ^ 59
def prefixEnd_288855 : Nat := 4983230072969 + 3 ^ 40 * 288855 * 2
def baseEnd_288855 : Nat := 65920646424254483192927

theorem tailTrace_288855 : CollatzResearch.WordTrace tailWord_288855 prefixEnd_288855 65920646424254483192927 := by
  unfold tailWord_288855
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535407368535142351548019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7023604912356761567698679 10535407368535142351548019)
  ·
    refine ⟨15803111052802713527322029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10535407368535142351548019 15803111052802713527322029)
    ·
      refine ⟨5926166644801017572745761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15803111052802713527322029 5926166644801017572745761)
      ·
        refine ⟨4444624983600763179559321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5926166644801017572745761 4444624983600763179559321)
        ·
          refine ⟨3333468737700572384669491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444624983600763179559321 3333468737700572384669491)
          ·
            refine ⟨5000203106550858577004237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333468737700572384669491 5000203106550858577004237)
            ·
              refine ⟨1875076164956571966376589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5000203106550858577004237 1875076164956571966376589)
              ·
                refine ⟨703153561858714487391221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1875076164956571966376589 703153561858714487391221)
                ·
                  refine ⟨65920646424254483192927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703153561858714487391221 65920646424254483192927)
                  ·
                    rfl

theorem cell21_288855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_288855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288855 prefixEnd_288855 := by exact prefixLift 288855
  have htrace : WordTrace (prefixWord ++ tailWord_288855) baseStart_288855 baseEnd_288855 := by
    simpa [prefixWord, tailWord_288855, baseEnd_288855] using wordTrace_append hprefix tailTrace_288855
  have hstable : (prefixWord ++ tailWord_288855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288855).length < 2 ^ (prefixWord ++ tailWord_288855).sum := by decide
  have hdescent : baseEnd_288855 < baseStart_288855 := by decide
  rcases family_descends (prefixWord ++ tailWord_288855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288861 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 4]
def baseStart_288861 : Nat := 118140960795 + 288861 * 2 ^ 59
def prefixEnd_288861 : Nat := 4983230072969 + 3 ^ 40 * 288861 * 2
def baseEnd_288861 : Nat := 65922015705999806092915

theorem tailTrace_288861 : CollatzResearch.WordTrace tailWord_288861 prefixEnd_288861 65922015705999806092915 := by
  unfold tailWord_288861
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535626206513405376266437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7023750804342270250844291 10535626206513405376266437)
  ·
    refine ⟨1975429913721263508049957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10535626206513405376266437 1975429913721263508049957)
    ·
      refine ⟨370393108822736907759367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1975429913721263508049957 370393108822736907759367)
      ·
        refine ⟨555589663234105361639051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370393108822736907759367 555589663234105361639051)
        ·
          refine ⟨833384494851158042458577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555589663234105361639051 833384494851158042458577)
          ·
            refine ⟨625038371138368531843933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833384494851158042458577 625038371138368531843933)
            ·
              refine ⟨234389389176888199441475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625038371138368531843933 234389389176888199441475)
              ·
                refine ⟨351584083765332299162213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234389389176888199441475 351584083765332299162213)
                ·
                  refine ⟨65922015705999806092915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351584083765332299162213 65922015705999806092915)
                  ·
                    rfl

theorem cell21_288861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_288861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_288861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_288861 prefixEnd_288861 := by exact prefixLift 288861
  have htrace : WordTrace (prefixWord ++ tailWord_288861) baseStart_288861 baseEnd_288861 := by
    simpa [prefixWord, tailWord_288861, baseEnd_288861] using wordTrace_append hprefix tailTrace_288861
  have hstable : (prefixWord ++ tailWord_288861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288861).length < 2 ^ (prefixWord ++ tailWord_288861).sum := by decide
  have hdescent : baseEnd_288861 < baseStart_288861 := by decide
  rcases family_descends (prefixWord ++ tailWord_288861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
