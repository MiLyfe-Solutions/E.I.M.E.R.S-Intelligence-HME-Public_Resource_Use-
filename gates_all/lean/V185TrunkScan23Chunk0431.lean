import V185TrunkScan23Chunk0430

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2548151 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_2548151 : Nat := 118140960795 + 2548151 * 2 ^ 59
def prefixEnd_2548151 : Nat := 4983230072969 + 3 ^ 40 * 2548151 * 2
def baseEnd_2548151 : Nat := 1308426243234965081193773

theorem tailTrace_2548151 : CollatzResearch.WordTrace tailWord_2548151 prefixEnd_2548151 1308426243234965081193773 := by
  unfold tailWord_2548151
  simp only [CollatzResearch.WordTrace]
  refine ⟨92938702191491591388700307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61959134794327727592466871 92938702191491591388700307)
  ·
    refine ⟨139408053287237387083050461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92938702191491591388700307 139408053287237387083050461)
    ·
      refine ⟨52278019982714020156143923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139408053287237387083050461 52278019982714020156143923)
      ·
        refine ⟨78417029974071030234215885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52278019982714020156143923 78417029974071030234215885)
        ·
          refine ⟨29406386240276636337830957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78417029974071030234215885 29406386240276636337830957)
          ·
            refine ⟨11027394840103738626686609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29406386240276636337830957 11027394840103738626686609)
            ·
              refine ⟨8270546130077803970014957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11027394840103738626686609 8270546130077803970014957)
              ·
                refine ⟨3101454798779176488755609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8270546130077803970014957 3101454798779176488755609)
                ·
                  refine ⟨2326091099084382366566707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101454798779176488755609 2326091099084382366566707)
                  ·
                    refine ⟨3489136648626573549850061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2326091099084382366566707 3489136648626573549850061)
                    ·
                      refine ⟨1308426243234965081193773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3489136648626573549850061 1308426243234965081193773)
                      ·
                        rfl

theorem cell23_2548151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_2548151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548151 prefixEnd_2548151 := by exact prefixLift 2548151
  have htrace : WordTrace (prefixWord ++ tailWord_2548151) baseStart_2548151 baseEnd_2548151 := by
    simpa [prefixWord, tailWord_2548151, baseEnd_2548151] using wordTrace_append hprefix tailTrace_2548151
  have hstable : (prefixWord ++ tailWord_2548151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548151).length < 2 ^ (prefixWord ++ tailWord_2548151).sum := by decide
  have hdescent : baseEnd_2548151 < baseStart_2548151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548177 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_2548177 : Nat := 118140960795 + 2548177 * 2 ^ 59
def prefixEnd_2548177 : Nat := 4983230072969 + 3 ^ 40 * 2548177 * 2
def baseEnd_2548177 : Nat := 1308439593731981979468653

theorem tailTrace_2548177 : CollatzResearch.WordTrace tailWord_2548177 prefixEnd_2548177 1308439593731981979468653 := by
  unfold tailWord_2548177
  simp only [CollatzResearch.WordTrace]
  refine ⟨92939650489397397829146785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61959766992931598552764523 92939650489397397829146785)
  ·
    refine ⟨69704737867048048371860089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92939650489397397829146785 69704737867048048371860089)
    ·
      refine ⟨52278553400286036278895067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69704737867048048371860089 52278553400286036278895067)
      ·
        refine ⟨78417830100429054418342601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52278553400286036278895067 78417830100429054418342601)
        ·
          refine ⟨58813372575321790813756951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78417830100429054418342601 58813372575321790813756951)
          ·
            refine ⟨88220058862982686220635427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58813372575321790813756951 88220058862982686220635427)
            ·
              refine ⟨132330088294474029330953141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88220058862982686220635427 132330088294474029330953141)
              ·
                refine ⟨12405945777606940249776857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132330088294474029330953141 12405945777606940249776857)
                ·
                  refine ⟨9304459333205205187332643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12405945777606940249776857 9304459333205205187332643)
                  ·
                    refine ⟨13956688999807807780998965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9304459333205205187332643 13956688999807807780998965)
                    ·
                      refine ⟨1308439593731981979468653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13956688999807807780998965 1308439593731981979468653)
                      ·
                        rfl

theorem cell23_2548177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_2548177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548177 prefixEnd_2548177 := by exact prefixLift 2548177
  have htrace : WordTrace (prefixWord ++ tailWord_2548177) baseStart_2548177 baseEnd_2548177 := by
    simpa [prefixWord, tailWord_2548177, baseEnd_2548177] using wordTrace_append hprefix tailTrace_2548177
  have hstable : (prefixWord ++ tailWord_2548177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548177).length < 2 ^ (prefixWord ++ tailWord_2548177).sum := by decide
  have hdescent : baseEnd_2548177 < baseStart_2548177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548214 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2548214 : Nat := 118140960795 + 2548214 * 2 ^ 59
def prefixEnd_2548214 : Nat := 4983230072969 + 3 ^ 40 * 2548214 * 2
def baseEnd_2548214 : Nat := 145384288057355370522887

theorem tailTrace_2548214 : CollatzResearch.WordTrace tailWord_2548214 prefixEnd_2548214 145384288057355370522887 := by
  unfold tailWord_2548214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808812499391459571765231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61960666660175568765495797 5808812499391459571765231)
  ·
    refine ⟨8713218749087189357647847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808812499391459571765231 8713218749087189357647847)
    ·
      refine ⟨13069828123630784036471771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8713218749087189357647847 13069828123630784036471771)
      ·
        refine ⟨19604742185446176054707657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069828123630784036471771 19604742185446176054707657)
        ·
          refine ⟨14703556639084632041030743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19604742185446176054707657 14703556639084632041030743)
          ·
            refine ⟨22055334958626948061546115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703556639084632041030743 22055334958626948061546115)
            ·
              refine ⟨33083002437940422092319173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22055334958626948061546115 33083002437940422092319173)
              ·
                refine ⟨6203062957113829142309845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33083002437940422092319173 6203062957113829142309845)
                ·
                  refine ⟨145384288057355370522887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6203062957113829142309845 145384288057355370522887)
                  ·
                    rfl

theorem cell23_2548214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2548214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548214 prefixEnd_2548214 := by exact prefixLift 2548214
  have htrace : WordTrace (prefixWord ++ tailWord_2548214) baseStart_2548214 baseEnd_2548214 := by
    simpa [prefixWord, tailWord_2548214, baseEnd_2548214] using wordTrace_append hprefix tailTrace_2548214
  have hstable : (prefixWord ++ tailWord_2548214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548214).length < 2 ^ (prefixWord ++ tailWord_2548214).sum := by decide
  have hdescent : baseEnd_2548214 < baseStart_2548214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548227 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 7]
def baseStart_2548227 : Nat := 118140960795 + 2548227 * 2 ^ 59
def prefixEnd_2548227 : Nat := 4983230072969 + 3 ^ 40 * 2548227 * 2
def baseEnd_2548227 : Nat := 436155089254902261281141

theorem tailTrace_2548227 : CollatzResearch.WordTrace tailWord_2548227 prefixEnd_2548227 436155089254902261281141 := by
  unfold tailWord_2548227
  simp only [CollatzResearch.WordTrace]
  refine ⟨92941474139216256368466935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61960982759477504245644623 92941474139216256368466935)
  ·
    refine ⟨139412211208824384552700403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92941474139216256368466935 139412211208824384552700403)
    ·
      refine ⟨209118316813236576829050605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139412211208824384552700403 209118316813236576829050605)
      ·
        refine ⟨78419368804963716310893977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209118316813236576829050605 78419368804963716310893977)
        ·
          refine ⟨58814526603722787233170483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78419368804963716310893977 58814526603722787233170483)
          ·
            refine ⟨88221789905584180849755725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58814526603722787233170483 88221789905584180849755725)
            ·
              refine ⟨33083171214594067818658397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88221789905584180849755725 33083171214594067818658397)
              ·
                refine ⟨12406189205472775431996899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33083171214594067818658397 12406189205472775431996899)
                ·
                  refine ⟨18609283808209163147995349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12406189205472775431996899 18609283808209163147995349)
                  ·
                    refine ⟨436155089254902261281141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18609283808209163147995349 436155089254902261281141)
                    ·
                      rfl

theorem cell23_2548227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_2548227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548227 prefixEnd_2548227 := by exact prefixLift 2548227
  have htrace : WordTrace (prefixWord ++ tailWord_2548227) baseStart_2548227 baseEnd_2548227 := by
    simpa [prefixWord, tailWord_2548227, baseEnd_2548227] using wordTrace_append hprefix tailTrace_2548227
  have hstable : (prefixWord ++ tailWord_2548227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548227).length < 2 ^ (prefixWord ++ tailWord_2548227).sum := by decide
  have hdescent : baseEnd_2548227 < baseStart_2548227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548248 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 5]
def baseStart_2548248 : Nat := 118140960795 + 2548248 * 2 ^ 59
def prefixEnd_2548248 : Nat := 4983230072969 + 3 ^ 40 * 2548248 * 2
def baseEnd_2548248 : Nat := 145386227873161244631203

theorem tailTrace_2548248 : CollatzResearch.WordTrace tailWord_2548248 prefixEnd_2548248 145386227873161244631203 := by
  unfold tailWord_2548248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46471120036070088477490699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61961493381426784636654265 46471120036070088477490699)
  ·
    refine ⟨69706680054105132716236049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46471120036070088477490699 69706680054105132716236049)
    ·
      refine ⟨52280010040578849537177037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69706680054105132716236049 52280010040578849537177037)
      ·
        refine ⟨19605003765217068576441389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52280010040578849537177037 19605003765217068576441389)
        ·
          refine ⟨7351876411956400716165521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19605003765217068576441389 7351876411956400716165521)
          ·
            refine ⟨5513907308967300537124141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351876411956400716165521 5513907308967300537124141)
            ·
              refine ⟨2067715240862737701421553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5513907308967300537124141 2067715240862737701421553)
              ·
                refine ⟨1550786430647053276066165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067715240862737701421553 1550786430647053276066165)
                ·
                  refine ⟨145386227873161244631203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1550786430647053276066165 145386227873161244631203)
                  ·
                    rfl

theorem cell23_2548248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 5].length) (baseStart_2548248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548248 prefixEnd_2548248 := by exact prefixLift 2548248
  have htrace : WordTrace (prefixWord ++ tailWord_2548248) baseStart_2548248 baseEnd_2548248 := by
    simpa [prefixWord, tailWord_2548248, baseEnd_2548248] using wordTrace_append hprefix tailTrace_2548248
  have hstable : (prefixWord ++ tailWord_2548248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548248).length < 2 ^ (prefixWord ++ tailWord_2548248).sum := by decide
  have hdescent : baseEnd_2548248 < baseStart_2548248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548267 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_2548267 : Nat := 118140960795 + 2548267 * 2 ^ 59
def prefixEnd_2548267 : Nat := 4983230072969 + 3 ^ 40 * 2548267 * 2
def baseEnd_2548267 : Nat := 1308485806990886627343239

theorem tailTrace_2548267 : CollatzResearch.WordTrace tailWord_2548267 prefixEnd_2548267 1308485806990886627343239 := by
  unfold tailWord_2548267
  simp only [CollatzResearch.WordTrace]
  refine ⟨92942933059071343199923055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61961955372714228799948703 92942933059071343199923055)
  ·
    refine ⟨139414399588607014799884583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92942933059071343199923055 139414399588607014799884583)
    ·
      refine ⟨209121599382910522199826875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139414399588607014799884583 209121599382910522199826875)
      ·
        refine ⟨313682399074365783299740313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209121599382910522199826875 313682399074365783299740313)
        ·
          refine ⟨235261799305774337474805235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313682399074365783299740313 235261799305774337474805235)
          ·
            refine ⟨352892698958661506212207853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235261799305774337474805235 352892698958661506212207853)
            ·
              refine ⟨132334762109498064829577945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352892698958661506212207853 132334762109498064829577945)
              ·
                refine ⟨99251071582123548622183459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132334762109498064829577945 99251071582123548622183459)
                ·
                  refine ⟨148876607373185322933275189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99251071582123548622183459 148876607373185322933275189)
                  ·
                    refine ⟨13957181941236124024994549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148876607373185322933275189 13957181941236124024994549)
                    ·
                      refine ⟨1308485806990886627343239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13957181941236124024994549 1308485806990886627343239)
                      ·
                        rfl

theorem cell23_2548267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_2548267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548267 prefixEnd_2548267 := by exact prefixLift 2548267
  have htrace : WordTrace (prefixWord ++ tailWord_2548267) baseStart_2548267 baseEnd_2548267 := by
    simpa [prefixWord, tailWord_2548267, baseEnd_2548267] using wordTrace_append hprefix tailTrace_2548267
  have hstable : (prefixWord ++ tailWord_2548267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548267).length < 2 ^ (prefixWord ++ tailWord_2548267).sum := by decide
  have hdescent : baseEnd_2548267 < baseStart_2548267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548278 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2548278 : Nat := 118140960795 + 2548278 * 2 ^ 59
def prefixEnd_2548278 : Nat := 4983230072969 + 3 ^ 40 * 2548278 * 2
def baseEnd_2548278 : Nat := 436163818426028694768563

theorem tailTrace_2548278 : CollatzResearch.WordTrace tailWord_2548278 prefixEnd_2548278 436163818426028694768563 := by
  unfold tailWord_2548278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808958391376968254910843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61962222841354328052382325 5808958391376968254910843)
  ·
    refine ⟨8713437587065452382366265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808958391376968254910843 8713437587065452382366265)
    ·
      refine ⟨6535078190299089286774699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8713437587065452382366265 6535078190299089286774699)
      ·
        refine ⟨9802617285448633930162049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6535078190299089286774699 9802617285448633930162049)
        ·
          refine ⟨7351962964086475447621537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9802617285448633930162049 7351962964086475447621537)
          ·
            refine ⟨5513972223064856585716153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351962964086475447621537 5513972223064856585716153)
            ·
              refine ⟨4135479167298642439287115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513972223064856585716153 4135479167298642439287115)
              ·
                refine ⟨6203218750947963658930673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135479167298642439287115 6203218750947963658930673)
                ·
                  refine ⟨4652414063210972744198005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6203218750947963658930673 4652414063210972744198005)
                  ·
                    refine ⟨436163818426028694768563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4652414063210972744198005 436163818426028694768563)
                    ·
                      rfl

theorem cell23_2548278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2548278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548278 prefixEnd_2548278 := by exact prefixLift 2548278
  have htrace : WordTrace (prefixWord ++ tailWord_2548278) baseStart_2548278 baseEnd_2548278 := by
    simpa [prefixWord, tailWord_2548278, baseEnd_2548278] using wordTrace_append hprefix tailTrace_2548278
  have hstable : (prefixWord ++ tailWord_2548278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548278).length < 2 ^ (prefixWord ++ tailWord_2548278).sum := by decide
  have hdescent : baseEnd_2548278 < baseStart_2548278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548281 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2548281 : Nat := 118140960795 + 2548281 * 2 ^ 59
def prefixEnd_2548281 : Nat := 4983230072969 + 3 ^ 40 * 2548281 * 2
def baseEnd_2548281 : Nat := 1308492995720049572568175

theorem tailTrace_2548281 : CollatzResearch.WordTrace tailWord_2548281 prefixEnd_2548281 1308492995720049572568175 := by
  unfold tailWord_2548281
  simp only [CollatzResearch.WordTrace]
  refine ⟨92943443681020623590932697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61962295787347082393955131 92943443681020623590932697)
  ·
    refine ⟨69707582760765467693199523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92943443681020623590932697 69707582760765467693199523)
    ·
      refine ⟨104561374141148201539799285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69707582760765467693199523 104561374141148201539799285)
      ·
        refine ⟨9802628825732643894356183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104561374141148201539799285 9802628825732643894356183)
        ·
          refine ⟨14703943238598965841534275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802628825732643894356183 14703943238598965841534275)
          ·
            refine ⟨22055914857898448762301413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703943238598965841534275 22055914857898448762301413)
            ·
              refine ⟨4135484035855959142931515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22055914857898448762301413 4135484035855959142931515)
              ·
                refine ⟨6203226053783938714397273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135484035855959142931515 6203226053783938714397273)
                ·
                  refine ⟨4652419540337954035797955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6203226053783938714397273 4652419540337954035797955)
                  ·
                    refine ⟨6978629310506931053696933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652419540337954035797955 6978629310506931053696933)
                    ·
                      refine ⟨1308492995720049572568175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6978629310506931053696933 1308492995720049572568175)
                      ·
                        rfl

theorem cell23_2548281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2548281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548281 prefixEnd_2548281 := by exact prefixLift 2548281
  have htrace : WordTrace (prefixWord ++ tailWord_2548281) baseStart_2548281 baseEnd_2548281 := by
    simpa [prefixWord, tailWord_2548281, baseEnd_2548281] using wordTrace_append hprefix tailTrace_2548281
  have hstable : (prefixWord ++ tailWord_2548281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548281).length < 2 ^ (prefixWord ++ tailWord_2548281).sum := by decide
  have hdescent : baseEnd_2548281 < baseStart_2548281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548314 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2548314 : Nat := 118140960795 + 2548314 * 2 ^ 59
def prefixEnd_2548314 : Nat := 4983230072969 + 3 ^ 40 * 2548314 * 2
def baseEnd_2548314 : Nat := 1308509940581647943455523

theorem tailTrace_2548314 : CollatzResearch.WordTrace tailWord_2548314 prefixEnd_2548314 1308509940581647943455523 := by
  unfold tailWord_2548314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23236161822475267556720999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61963098193267380151255997 23236161822475267556720999)
  ·
    refine ⟨34854242733712901335081499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23236161822475267556720999 34854242733712901335081499)
    ·
      refine ⟨52281364100569352002622249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34854242733712901335081499 52281364100569352002622249)
      ·
        refine ⟨39211023075427014001966687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52281364100569352002622249 39211023075427014001966687)
        ·
          refine ⟨58816534613140521002950031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39211023075427014001966687 58816534613140521002950031)
          ·
            refine ⟨88224801919710781504425047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58816534613140521002950031 88224801919710781504425047)
            ·
              refine ⟨132337202879566172256637571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88224801919710781504425047 132337202879566172256637571)
              ·
                refine ⟨198505804319349258384956357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132337202879566172256637571 198505804319349258384956357)
                ·
                  refine ⟨37219838309877985947179317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198505804319349258384956357 37219838309877985947179317)
                  ·
                    refine ⟨3489359841551061182548061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37219838309877985947179317 3489359841551061182548061)
                    ·
                      refine ⟨1308509940581647943455523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3489359841551061182548061 1308509940581647943455523)
                      ·
                        rfl

theorem cell23_2548314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2548314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548314 prefixEnd_2548314 := by exact prefixLift 2548314
  have htrace : WordTrace (prefixWord ++ tailWord_2548314) baseStart_2548314 baseEnd_2548314 := by
    simpa [prefixWord, tailWord_2548314, baseEnd_2548314] using wordTrace_append hprefix tailTrace_2548314
  have hstable : (prefixWord ++ tailWord_2548314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548314).length < 2 ^ (prefixWord ++ tailWord_2548314).sum := by decide
  have hdescent : baseEnd_2548314 < baseStart_2548314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548342 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2548342 : Nat := 118140960795 + 2548342 * 2 ^ 59
def prefixEnd_2548342 : Nat := 4983230072969 + 3 ^ 40 * 2548342 * 2
def baseEnd_2548342 : Nat := 436174772679991277968465

theorem tailTrace_2548342 : CollatzResearch.WordTrace tailWord_2548342 prefixEnd_2548342 436174772679991277968465 := by
  unfold tailWord_2548342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809104283362476938056455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61963779022533087339268853 5809104283362476938056455)
  ·
    refine ⟨8713656425043715407084683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5809104283362476938056455 8713656425043715407084683)
    ·
      refine ⟨13070484637565573110627025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8713656425043715407084683 13070484637565573110627025)
      ·
        refine ⟨9802863478174179832970269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13070484637565573110627025 9802863478174179832970269)
        ·
          refine ⟨3676073804315317437363851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9802863478174179832970269 3676073804315317437363851)
          ·
            refine ⟨5514110706472976156045777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676073804315317437363851 5514110706472976156045777)
            ·
              refine ⟨4135583029854732117034333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5514110706472976156045777 4135583029854732117034333)
              ·
                refine ⟨1550843636195524543887875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135583029854732117034333 1550843636195524543887875)
                ·
                  refine ⟨2326265454293286815831813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550843636195524543887875 2326265454293286815831813)
                  ·
                    refine ⟨436174772679991277968465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2326265454293286815831813 436174772679991277968465)
                    ·
                      rfl

theorem cell23_2548342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2548342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548342 prefixEnd_2548342 := by exact prefixLift 2548342
  have htrace : WordTrace (prefixWord ++ tailWord_2548342) baseStart_2548342 baseEnd_2548342 := by
    simpa [prefixWord, tailWord_2548342, baseEnd_2548342] using wordTrace_append hprefix tailTrace_2548342
  have hstable : (prefixWord ++ tailWord_2548342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548342).length < 2 ^ (prefixWord ++ tailWord_2548342).sum := by decide
  have hdescent : baseEnd_2548342 < baseStart_2548342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548381 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2548381 : Nat := 118140960795 + 2548381 * 2 ^ 59
def prefixEnd_2548381 : Nat := 4983230072969 + 3 ^ 40 * 2548381 * 2
def baseEnd_2548381 : Nat := 436181447928499727105905

theorem tailTrace_2548381 : CollatzResearch.WordTrace tailWord_2548381 prefixEnd_2548381 436181447928499727105905 := by
  unfold tailWord_2548381
  simp only [CollatzResearch.WordTrace]
  refine ⟨92947090980658340669572997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61964727320438893779715331 92947090980658340669572997)
  ·
    refine ⟨17427579558873438875544937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92947090980658340669572997 17427579558873438875544937)
    ·
      refine ⟨13070684669155079156658703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17427579558873438875544937 13070684669155079156658703)
      ·
        refine ⟨19606027003732618734988055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13070684669155079156658703 19606027003732618734988055)
        ·
          refine ⟨29409040505598928102482083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19606027003732618734988055 29409040505598928102482083)
          ·
            refine ⟨44113560758398392153723125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29409040505598928102482083 44113560758398392153723125)
            ·
              refine ⟨4135646321099849264411543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44113560758398392153723125 4135646321099849264411543)
              ·
                refine ⟨6203469481649773896617315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135646321099849264411543 6203469481649773896617315)
                ·
                  refine ⟨9305204222474660844925973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6203469481649773896617315 9305204222474660844925973)
                  ·
                    refine ⟨436181447928499727105905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9305204222474660844925973 436181447928499727105905)
                    ·
                      rfl

theorem cell23_2548381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2548381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548381 prefixEnd_2548381 := by exact prefixLift 2548381
  have htrace : WordTrace (prefixWord ++ tailWord_2548381) baseStart_2548381 baseEnd_2548381 := by
    simpa [prefixWord, tailWord_2548381, baseEnd_2548381] using wordTrace_append hprefix tailTrace_2548381
  have hstable : (prefixWord ++ tailWord_2548381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548381).length < 2 ^ (prefixWord ++ tailWord_2548381).sum := by decide
  have hdescent : baseEnd_2548381 < baseStart_2548381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548388 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_2548388 : Nat := 118140960795 + 2548388 * 2 ^ 59
def prefixEnd_2548388 : Nat := 4983230072969 + 3 ^ 40 * 2548388 * 2
def baseEnd_2548388 : Nat := 1308547938150080653930183

theorem tailTrace_2548388 : CollatzResearch.WordTrace tailWord_2548388 prefixEnd_2548388 1308547938150080653930183 := by
  unfold tailWord_2548388
  simp only [CollatzResearch.WordTrace]
  refine ⟨46473673145816490432538909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61964897527755320576718545 46473673145816490432538909)
  ·
    refine ⟨17427627429681183912202091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46473673145816490432538909 17427627429681183912202091)
    ·
      refine ⟨26141441144521775868303137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17427627429681183912202091 26141441144521775868303137)
      ·
        refine ⟨19606080858391331901227353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26141441144521775868303137 19606080858391331901227353)
        ·
          refine ⟨14704560643793498925920515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19606080858391331901227353 14704560643793498925920515)
          ·
            refine ⟨22056840965690248388880773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14704560643793498925920515 22056840965690248388880773)
            ·
              refine ⟨4135657681066921572915145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22056840965690248388880773 4135657681066921572915145)
              ·
                refine ⟨3101743260800191179686359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4135657681066921572915145 3101743260800191179686359)
                ·
                  refine ⟨4652614891200286769529539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101743260800191179686359 4652614891200286769529539)
                  ·
                    refine ⟨6978922336800430154294309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652614891200286769529539 6978922336800430154294309)
                    ·
                      refine ⟨1308547938150080653930183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6978922336800430154294309 1308547938150080653930183)
                      ·
                        rfl

theorem cell23_2548388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_2548388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548388 prefixEnd_2548388 := by exact prefixLift 2548388
  have htrace : WordTrace (prefixWord ++ tailWord_2548388) baseStart_2548388 baseEnd_2548388 := by
    simpa [prefixWord, tailWord_2548388, baseEnd_2548388] using wordTrace_append hprefix tailTrace_2548388
  have hstable : (prefixWord ++ tailWord_2548388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548388).length < 2 ^ (prefixWord ++ tailWord_2548388).sum := by decide
  have hdescent : baseEnd_2548388 < baseStart_2548388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548431 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 9, 2]
def baseStart_2548431 : Nat := 118140960795 + 2548431 * 2 ^ 59
def prefixEnd_2548431 : Nat := 4983230072969 + 3 ^ 40 * 2548431 * 2
def baseEnd_2548431 : Nat := 1308570017818223985692485

theorem tailTrace_2548431 : CollatzResearch.WordTrace tailWord_2548431 prefixEnd_2548431 1308570017818223985692485 := by
  unfold tailWord_2548431
  simp only [CollatzResearch.WordTrace]
  refine ⟨92948914630477199208893147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61965943086984799472595431 92948914630477199208893147)
  ·
    refine ⟨139423371945715798813339721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92948914630477199208893147 139423371945715798813339721)
    ·
      refine ⟨104567528959286849110004791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139423371945715798813339721 104567528959286849110004791)
      ·
        refine ⟨156851293438930273665007187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104567528959286849110004791 156851293438930273665007187)
        ·
          refine ⟨235276940158395410497510781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156851293438930273665007187 235276940158395410497510781)
          ·
            refine ⟨88228852559398278936566543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235276940158395410497510781 88228852559398278936566543)
            ·
              refine ⟨132343278839097418404849815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88228852559398278936566543 132343278839097418404849815)
              ·
                refine ⟨198514918258646127607274723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132343278839097418404849815 198514918258646127607274723)
                ·
                  refine ⟨297772377387969191410912085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198514918258646127607274723 297772377387969191410912085)
                  ·
                    refine ⟨1744760023757631980923313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 297772377387969191410912085 1744760023757631980923313)
                    ·
                      refine ⟨1308570017818223985692485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744760023757631980923313 1308570017818223985692485)
                      ·
                        rfl

theorem cell23_2548431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9, 2].length) (baseStart_2548431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548431 prefixEnd_2548431 := by exact prefixLift 2548431
  have htrace : WordTrace (prefixWord ++ tailWord_2548431) baseStart_2548431 baseEnd_2548431 := by
    simpa [prefixWord, tailWord_2548431, baseEnd_2548431] using wordTrace_append hprefix tailTrace_2548431
  have hstable : (prefixWord ++ tailWord_2548431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548431).length < 2 ^ (prefixWord ++ tailWord_2548431).sum := by decide
  have hdescent : baseEnd_2548431 < baseStart_2548431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548478 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2548478 : Nat := 118140960795 + 2548478 * 2 ^ 59
def prefixEnd_2548478 : Nat := 4983230072969 + 3 ^ 40 * 2548478 * 2
def baseEnd_2548478 : Nat := 1308594151408985301804769

theorem tailTrace_2548478 : CollatzResearch.WordTrace tailWord_2548478 prefixEnd_2548478 1308594151408985301804769 := by
  unfold tailWord_2548478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11618828607663365779481761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61967085907537950823902725 11618828607663365779481761)
  ·
    refine ⟨8714121455747524334611321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11618828607663365779481761 8714121455747524334611321)
    ·
      refine ⟨6535591091810643250958491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8714121455747524334611321 6535591091810643250958491)
      ·
        refine ⟨9803386637715964876437737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6535591091810643250958491 9803386637715964876437737)
        ·
          refine ⟨7352539978286973657328303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9803386637715964876437737 7352539978286973657328303)
          ·
            refine ⟨11028809967430460485992455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7352539978286973657328303 11028809967430460485992455)
            ·
              refine ⟨16543214951145690728988683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11028809967430460485992455 16543214951145690728988683)
              ·
                refine ⟨24814822426718536093483025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16543214951145690728988683 24814822426718536093483025)
                ·
                  refine ⟨18611116820038902070112269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24814822426718536093483025 18611116820038902070112269)
                  ·
                    refine ⟨6979168807514588276292101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18611116820038902070112269 6979168807514588276292101)
                    ·
                      refine ⟨1308594151408985301804769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6979168807514588276292101 1308594151408985301804769)
                      ·
                        rfl

theorem cell23_2548478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2548478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548478 prefixEnd_2548478 := by exact prefixLift 2548478
  have htrace : WordTrace (prefixWord ++ tailWord_2548478) baseStart_2548478 baseEnd_2548478 := by
    simpa [prefixWord, tailWord_2548478, baseEnd_2548478] using wordTrace_append hprefix tailTrace_2548478
  have hstable : (prefixWord ++ tailWord_2548478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548478).length < 2 ^ (prefixWord ++ tailWord_2548478).sum := by decide
  have hdescent : baseEnd_2548478 < baseStart_2548478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548495 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 2, 2, 2]
def baseStart_2548495 : Nat := 118140960795 + 2548495 * 2 ^ 59
def prefixEnd_2548495 : Nat := 4983230072969 + 3 ^ 40 * 2548495 * 2
def baseEnd_2548495 : Nat := 1308602880580111735292191

theorem tailTrace_2548495 : CollatzResearch.WordTrace tailWord_2548495 prefixEnd_2548495 1308602880580111735292191 := by
  unfold tailWord_2548495
  simp only [CollatzResearch.WordTrace]
  refine ⟨92951248902245338139222939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61967499268163558759481959 92951248902245338139222939)
  ·
    refine ⟨139426873353368007208834409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92951248902245338139222939 139426873353368007208834409)
    ·
      refine ⟨104570155015026005406625807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139426873353368007208834409 104570155015026005406625807)
      ·
        refine ⟨156855232522539008109938711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104570155015026005406625807 156855232522539008109938711)
        ·
          refine ⟨235282848783808512164908067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156855232522539008109938711 235282848783808512164908067)
          ·
            refine ⟨352924273175712768247362101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235282848783808512164908067 352924273175712768247362101)
            ·
              refine ⟨33086650610223072023190197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352924273175712768247362101 33086650610223072023190197)
              ·
                refine ⟨3101873494708413002174081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33086650610223072023190197 3101873494708413002174081)
                ·
                  refine ⟨2326405121031309751630561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101873494708413002174081 2326405121031309751630561)
                  ·
                    refine ⟨1744803840773482313722921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2326405121031309751630561 1744803840773482313722921)
                    ·
                      refine ⟨1308602880580111735292191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744803840773482313722921 1308602880580111735292191)
                      ·
                        rfl

theorem cell23_2548495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2, 2].length) (baseStart_2548495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548495 prefixEnd_2548495 := by exact prefixLift 2548495
  have htrace : WordTrace (prefixWord ++ tailWord_2548495) baseStart_2548495 baseEnd_2548495 := by
    simpa [prefixWord, tailWord_2548495, baseEnd_2548495] using wordTrace_append hprefix tailTrace_2548495
  have hstable : (prefixWord ++ tailWord_2548495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548495).length < 2 ^ (prefixWord ++ tailWord_2548495).sum := by decide
  have hdescent : baseEnd_2548495 < baseStart_2548495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548501 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 7]
def baseStart_2548501 : Nat := 118140960795 + 2548501 * 2 ^ 59
def prefixEnd_2548501 : Nat := 4983230072969 + 3 ^ 40 * 2548501 * 2
def baseEnd_2548501 : Nat := 145400662384893190201907

theorem tailTrace_2548501 : CollatzResearch.WordTrace tailWord_2548501 prefixEnd_2548501 145400662384893190201907 := by
  unfold tailWord_2548501
  simp only [CollatzResearch.WordTrace]
  refine ⟨92951467740223601163941357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61967645160149067442627571 92951467740223601163941357)
  ·
    refine ⟨34856800402583850436478009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92951467740223601163941357 34856800402583850436478009)
    ·
      refine ⟨26142600301937887827358507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34856800402583850436478009 26142600301937887827358507)
      ·
        refine ⟨39213900452906831741037761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26142600301937887827358507 39213900452906831741037761)
        ·
          refine ⟨29410425339680123805778321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39213900452906831741037761 29410425339680123805778321)
          ·
            refine ⟨22057819004760092854333741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29410425339680123805778321 22057819004760092854333741)
            ·
              refine ⟨8271682126785034820375153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22057819004760092854333741 8271682126785034820375153)
              ·
                refine ⟨6203761595088776115281365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8271682126785034820375153 6203761595088776115281365)
                ·
                  refine ⟨145400662384893190201907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6203761595088776115281365 145400662384893190201907)
                  ·
                    rfl

theorem cell23_2548501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_2548501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548501 prefixEnd_2548501 := by exact prefixLift 2548501
  have htrace : WordTrace (prefixWord ++ tailWord_2548501) baseStart_2548501 baseEnd_2548501 := by
    simpa [prefixWord, tailWord_2548501, baseEnd_2548501] using wordTrace_append hprefix tailTrace_2548501
  have hstable : (prefixWord ++ tailWord_2548501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548501).length < 2 ^ (prefixWord ++ tailWord_2548501).sum := by decide
  have hdescent : baseEnd_2548501 < baseStart_2548501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548516 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_2548516 : Nat := 118140960795 + 2548516 * 2 ^ 59
def prefixEnd_2548516 : Nat := 4983230072969 + 3 ^ 40 * 2548516 * 2
def baseEnd_2548516 : Nat := 1308613663673856153129595

theorem tailTrace_2548516 : CollatzResearch.WordTrace tailWord_2548516 prefixEnd_2548516 1308613663673856153129595 := by
  unfold tailWord_2548516
  simp only [CollatzResearch.WordTrace]
  refine ⟨46476007417584629362868701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61968009890112839150491601 46476007417584629362868701)
  ·
    refine ⟨17428502781594236011075763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46476007417584629362868701 17428502781594236011075763)
    ·
      refine ⟨26142754172391354016613645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17428502781594236011075763 26142754172391354016613645)
      ·
        refine ⟨9803532814646757756230117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26142754172391354016613645 9803532814646757756230117)
        ·
          refine ⟨1838162402746267079293147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9803532814646757756230117 1838162402746267079293147)
          ·
            refine ⟨2757243604119400618939721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838162402746267079293147 2757243604119400618939721)
            ·
              refine ⟨2067932703089550464204791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2757243604119400618939721 2067932703089550464204791)
              ·
                refine ⟨3101899054634325696307187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067932703089550464204791 3101899054634325696307187)
                ·
                  refine ⟨4652848581951488544460781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101899054634325696307187 4652848581951488544460781)
                  ·
                    refine ⟨1744818218231808204172793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4652848581951488544460781 1744818218231808204172793)
                    ·
                      refine ⟨1308613663673856153129595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744818218231808204172793 1308613663673856153129595)
                      ·
                        rfl

theorem cell23_2548516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_2548516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548516 prefixEnd_2548516 := by exact prefixLift 2548516
  have htrace : WordTrace (prefixWord ++ tailWord_2548516) baseStart_2548516 baseEnd_2548516 := by
    simpa [prefixWord, tailWord_2548516, baseEnd_2548516] using wordTrace_append hprefix tailTrace_2548516
  have hstable : (prefixWord ++ tailWord_2548516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548516).length < 2 ^ (prefixWord ++ tailWord_2548516).sum := by decide
  have hdescent : baseEnd_2548516 < baseStart_2548516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548568 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_2548568 : Nat := 118140960795 + 2548568 * 2 ^ 59
def prefixEnd_2548568 : Nat := 4983230072969 + 3 ^ 40 * 2548568 * 2
def baseEnd_2548568 : Nat := 1308640364667889949679355

theorem tailTrace_2548568 : CollatzResearch.WordTrace tailWord_2548568 prefixEnd_2548568 1308640364667889949679355 := by
  unfold tailWord_2548568
  simp only [CollatzResearch.WordTrace]
  refine ⟨46476955715490435803315179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61969274287320581071086905 46476955715490435803315179)
  ·
    refine ⟨69715433573235653704972769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46476955715490435803315179 69715433573235653704972769)
    ·
      refine ⟨52286575179926740278729577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69715433573235653704972769 52286575179926740278729577)
      ·
        refine ⟨39214931384945055209047183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52286575179926740278729577 39214931384945055209047183)
        ·
          refine ⟨58822397077417582813570775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39214931384945055209047183 58822397077417582813570775)
          ·
            refine ⟨88233595616126374220356163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58822397077417582813570775 88233595616126374220356163)
            ·
              refine ⟨132350393424189561330534245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88233595616126374220356163 132350393424189561330534245)
              ·
                refine ⟨24815698767035542749475171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132350393424189561330534245 24815698767035542749475171)
                ·
                  refine ⟨37223548150553314124212757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24815698767035542749475171 37223548150553314124212757)
                  ·
                    refine ⟨1744853819557186599572473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37223548150553314124212757 1744853819557186599572473)
                    ·
                      refine ⟨1308640364667889949679355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744853819557186599572473 1308640364667889949679355)
                      ·
                        rfl

theorem cell23_2548568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_2548568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548568 prefixEnd_2548568 := by exact prefixLift 2548568
  have htrace : WordTrace (prefixWord ++ tailWord_2548568) baseStart_2548568 baseEnd_2548568 := by
    simpa [prefixWord, tailWord_2548568, baseEnd_2548568] using wordTrace_append hprefix tailTrace_2548568
  have hstable : (prefixWord ++ tailWord_2548568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548568).length < 2 ^ (prefixWord ++ tailWord_2548568).sum := by decide
  have hdescent : baseEnd_2548568 < baseStart_2548568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548581 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2548581 : Nat := 118140960795 + 2548581 * 2 ^ 59
def prefixEnd_2548581 : Nat := 4983230072969 + 3 ^ 40 * 2548581 * 2
def baseEnd_2548581 : Nat := 1308647039916398398816795

theorem tailTrace_2548581 : CollatzResearch.WordTrace tailWord_2548581 prefixEnd_2548581 1308647039916398398816795 := by
  unfold tailWord_2548581
  simp only [CollatzResearch.WordTrace]
  refine ⟨92954385579933774826853597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61969590386622516551235731 92954385579933774826853597)
  ·
    refine ⟨34857894592475165560070099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92954385579933774826853597 34857894592475165560070099)
    ·
      refine ⟨52286841888712748340105149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34857894592475165560070099 52286841888712748340105149)
      ·
        refine ⟨19607565708267280627539431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52286841888712748340105149 19607565708267280627539431)
        ·
          refine ⟨29411348562400920941309147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19607565708267280627539431 29411348562400920941309147)
          ·
            refine ⟨44117022843601381411963721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29411348562400920941309147 44117022843601381411963721)
            ·
              refine ⟨33087767132701036058972791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44117022843601381411963721 33087767132701036058972791)
              ·
                refine ⟨49631650699051554088459187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33087767132701036058972791 49631650699051554088459187)
                ·
                  refine ⟨74447476048577331132688781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49631650699051554088459187 74447476048577331132688781)
                  ·
                    refine ⟨27917803518216499174758293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74447476048577331132688781 27917803518216499174758293)
                    ·
                      refine ⟨1308647039916398398816795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27917803518216499174758293 1308647039916398398816795)
                      ·
                        rfl

theorem cell23_2548581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2548581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548581 prefixEnd_2548581 := by exact prefixLift 2548581
  have htrace : WordTrace (prefixWord ++ tailWord_2548581) baseStart_2548581 baseEnd_2548581 := by
    simpa [prefixWord, tailWord_2548581, baseEnd_2548581] using wordTrace_append hprefix tailTrace_2548581
  have hstable : (prefixWord ++ tailWord_2548581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548581).length < 2 ^ (prefixWord ++ tailWord_2548581).sum := by decide
  have hdescent : baseEnd_2548581 < baseStart_2548581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548595 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 1, 4]
def baseStart_2548595 : Nat := 118140960795 + 2548595 * 2 ^ 59
def prefixEnd_2548595 : Nat := 4983230072969 + 3 ^ 40 * 2548595 * 2
def baseEnd_2548595 : Nat := 436218076215187114680577

theorem tailTrace_2548595 : CollatzResearch.WordTrace tailWord_2548595 prefixEnd_2548595 436218076215187114680577 := by
  unfold tailWord_2548595
  simp only [CollatzResearch.WordTrace]
  refine ⟨92954896201883055217863239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61969930801255370145242159 92954896201883055217863239)
  ·
    refine ⟨139432344302824582826794859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92954896201883055217863239 139432344302824582826794859)
    ·
      refine ⟨209148516454236874240192289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139432344302824582826794859 209148516454236874240192289)
      ·
        refine ⟨156861387340677655680144217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209148516454236874240192289 156861387340677655680144217)
        ·
          refine ⟨117646040505508241760108163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156861387340677655680144217 117646040505508241760108163)
          ·
            refine ⟨176469060758262362640162245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117646040505508241760108163 176469060758262362640162245)
            ·
              refine ⟨33087948892174192995030421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176469060758262362640162245 33087948892174192995030421)
              ·
                refine ⟨1550997604320665296642051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33087948892174192995030421 1550997604320665296642051)
                ·
                  refine ⟨2326496406480997944963077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550997604320665296642051 2326496406480997944963077)
                  ·
                    refine ⟨436218076215187114680577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2326496406480997944963077 436218076215187114680577)
                    ·
                      rfl

theorem cell23_2548595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 4].length) (baseStart_2548595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548595 prefixEnd_2548595 := by exact prefixLift 2548595
  have htrace : WordTrace (prefixWord ++ tailWord_2548595) baseStart_2548595 baseEnd_2548595 := by
    simpa [prefixWord, tailWord_2548595, baseEnd_2548595] using wordTrace_append hprefix tailTrace_2548595
  have hstable : (prefixWord ++ tailWord_2548595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548595).length < 2 ^ (prefixWord ++ tailWord_2548595).sum := by decide
  have hdescent : baseEnd_2548595 < baseStart_2548595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548652 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 1, 1, 3]
def baseStart_2548652 : Nat := 118140960795 + 2548652 * 2 ^ 59
def prefixEnd_2548652 : Nat := 4983230072969 + 3 ^ 40 * 2548652 * 2
def baseEnd_2548652 : Nat := 1308683497042867621028969

theorem tailTrace_2548652 : CollatzResearch.WordTrace tailWord_2548652 prefixEnd_2548652 1308683497042867621028969 := by
  unfold tailWord_2548652
  simp only [CollatzResearch.WordTrace]
  refine ⟨46478487581338276976344105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61971316775117702635125473 46478487581338276976344105)
  ·
    refine ⟨34858865686003707732258079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46478487581338276976344105 34858865686003707732258079)
    ·
      refine ⟨52288298529005561598387119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34858865686003707732258079 52288298529005561598387119)
      ·
        refine ⟨78432447793508342397580679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52288298529005561598387119 78432447793508342397580679)
        ·
          refine ⟨117648671690262513596371019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78432447793508342397580679 117648671690262513596371019)
          ·
            refine ⟨176473007535393770394556529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117648671690262513596371019 176473007535393770394556529)
            ·
              refine ⟨132354755651545327795917397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176473007535393770394556529 132354755651545327795917397)
              ·
                refine ⟨1551032292791546810108407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 132354755651545327795917397 1551032292791546810108407)
                ·
                  refine ⟨2326548439187320215162611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551032292791546810108407 2326548439187320215162611)
                  ·
                    refine ⟨3489822658780980322743917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2326548439187320215162611 3489822658780980322743917)
                    ·
                      refine ⟨1308683497042867621028969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3489822658780980322743917 1308683497042867621028969)
                      ·
                        rfl

theorem cell23_2548652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_2548652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548652 prefixEnd_2548652 := by exact prefixLift 2548652
  have htrace : WordTrace (prefixWord ++ tailWord_2548652) baseStart_2548652 baseEnd_2548652 := by
    simpa [prefixWord, tailWord_2548652, baseEnd_2548652] using wordTrace_append hprefix tailTrace_2548652
  have hstable : (prefixWord ++ tailWord_2548652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548652).length < 2 ^ (prefixWord ++ tailWord_2548652).sum := by decide
  have hdescent : baseEnd_2548652 < baseStart_2548652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548692 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2548692 : Nat := 118140960795 + 2548692 * 2 ^ 59
def prefixEnd_2548692 : Nat := 4983230072969 + 3 ^ 40 * 2548692 * 2
def baseEnd_2548692 : Nat := 1308704036269047464528785

theorem tailTrace_2548692 : CollatzResearch.WordTrace tailWord_2548692 prefixEnd_2548692 1308704036269047464528785 := by
  unfold tailWord_2548692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46479217041265820392072165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61972289388354427189429553 46479217041265820392072165)
  ·
    refine ⟨8714853195237341323513531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46479217041265820392072165 8714853195237341323513531)
    ·
      refine ⟨13072279792856011985270297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8714853195237341323513531 13072279792856011985270297)
      ·
        refine ⟨9804209844642008988952723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13072279792856011985270297 9804209844642008988952723)
        ·
          refine ⟨14706314766963013483429085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804209844642008988952723 14706314766963013483429085)
          ·
            refine ⟨5514868037611130056285907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14706314766963013483429085 5514868037611130056285907)
            ·
              refine ⟨8272302056416695084428861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514868037611130056285907 8272302056416695084428861)
              ·
                refine ⟨3102113271156260656660823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8272302056416695084428861 3102113271156260656660823)
                ·
                  refine ⟨4653169906734390984991235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102113271156260656660823 4653169906734390984991235)
                  ·
                    refine ⟨6979754860101586477486853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4653169906734390984991235 6979754860101586477486853)
                    ·
                      refine ⟨1308704036269047464528785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6979754860101586477486853 1308704036269047464528785)
                      ·
                        rfl

theorem cell23_2548692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2548692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548692 prefixEnd_2548692 := by exact prefixLift 2548692
  have htrace : WordTrace (prefixWord ++ tailWord_2548692) baseStart_2548692 baseEnd_2548692 := by
    simpa [prefixWord, tailWord_2548692, baseEnd_2548692] using wordTrace_append hprefix tailTrace_2548692
  have hstable : (prefixWord ++ tailWord_2548692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548692).length < 2 ^ (prefixWord ++ tailWord_2548692).sum := by decide
  have hdescent : baseEnd_2548692 < baseStart_2548692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548698 : List Nat := [3, 1, 1, 2, 4, 2, 10]
def baseStart_2548698 : Nat := 118140960795 + 2548698 * 2 ^ 59
def prefixEnd_2548698 : Nat := 4983230072969 + 3 ^ 40 * 2548698 * 2
def baseEnd_2548698 : Nat := 16156877989542894333997

theorem tailTrace_2548698 : CollatzResearch.WordTrace tailWord_2548698 prefixEnd_2548698 16156877989542894333997 := by
  unfold tailWord_2548698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239663230127475952215687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61972435280339935872575165 23239663230127475952215687)
  ·
    refine ⟨34859494845191213928323531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23239663230127475952215687 34859494845191213928323531)
    ·
      refine ⟨52289242267786820892485297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34859494845191213928323531 52289242267786820892485297)
      ·
        refine ⟨39216931700840115669363973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52289242267786820892485297 39216931700840115669363973)
        ·
          refine ⟨7353174693907521688005745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39216931700840115669363973 7353174693907521688005745)
          ·
            refine ⟨5514881020430641266004309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7353174693907521688005745 5514881020430641266004309)
            ·
              refine ⟨16156877989542894333997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5514881020430641266004309 16156877989542894333997)
              ·
                rfl

theorem cell23_2548698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 10].length) (baseStart_2548698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548698 prefixEnd_2548698 := by exact prefixLift 2548698
  have htrace : WordTrace (prefixWord ++ tailWord_2548698) baseStart_2548698 baseEnd_2548698 := by
    simpa [prefixWord, tailWord_2548698, baseEnd_2548698] using wordTrace_append hprefix tailTrace_2548698
  have hstable : (prefixWord ++ tailWord_2548698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548698).length < 2 ^ (prefixWord ++ tailWord_2548698).sum := by decide
  have hdescent : baseEnd_2548698 < baseStart_2548698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548722 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2548722 : Nat := 118140960795 + 2548722 * 2 ^ 59
def prefixEnd_2548722 : Nat := 4983230072969 + 3 ^ 40 * 2548722 * 2
def baseEnd_2548722 : Nat := 1308719440688682347153647

theorem tailTrace_2548722 : CollatzResearch.WordTrace tailWord_2548722 prefixEnd_2548722 1308719440688682347153647 := by
  unfold tailWord_2548722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239882068105738976934105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61973018848281970605157613 23239882068105738976934105)
  ·
    refine ⟨17429911551079304232700579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23239882068105738976934105 17429911551079304232700579)
    ·
      refine ⟨26144867326618956349050869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17429911551079304232700579 26144867326618956349050869)
      ·
        refine ⟨2451081311870527157723519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26144867326618956349050869 2451081311870527157723519)
        ·
          refine ⟨3676621967805790736585279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451081311870527157723519 3676621967805790736585279)
          ·
            refine ⟨5514932951708686104877919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676621967805790736585279 5514932951708686104877919)
            ·
              refine ⟨8272399427563029157316879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514932951708686104877919 8272399427563029157316879)
              ·
                refine ⟨12408599141344543735975319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8272399427563029157316879 12408599141344543735975319)
                ·
                  refine ⟨18612898712016815603962979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12408599141344543735975319 18612898712016815603962979)
                  ·
                    refine ⟨27919348068025223405944469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18612898712016815603962979 27919348068025223405944469)
                    ·
                      refine ⟨1308719440688682347153647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27919348068025223405944469 1308719440688682347153647)
                      ·
                        rfl

theorem cell23_2548722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2548722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548722 prefixEnd_2548722 := by exact prefixLift 2548722
  have htrace : WordTrace (prefixWord ++ tailWord_2548722) baseStart_2548722 baseEnd_2548722 := by
    simpa [prefixWord, tailWord_2548722, baseEnd_2548722] using wordTrace_append hprefix tailTrace_2548722
  have hstable : (prefixWord ++ tailWord_2548722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548722).length < 2 ^ (prefixWord ++ tailWord_2548722).sum := by decide
  have hdescent : baseEnd_2548722 < baseStart_2548722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548829 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2548829 : Nat := 118140960795 + 2548829 * 2 ^ 59
def prefixEnd_2548829 : Nat := 4983230072969 + 3 ^ 40 * 2548829 * 2
def baseEnd_2548829 : Nat := 1308774383118713428515655

theorem tailTrace_2548829 : CollatzResearch.WordTrace tailWord_2548829 prefixEnd_2548829 1308774383118713428515655 := by
  unfold tailWord_2548829
  simp only [CollatzResearch.WordTrace]
  refine ⟨92963430883035313181881541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61975620588690208787921027 92963430883035313181881541)
  ·
    refine ⟨17430643290569121221602789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92963430883035313181881541 17430643290569121221602789)
    ·
      refine ⟨3268245616981710229050523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17430643290569121221602789 3268245616981710229050523)
      ·
        refine ⟨4902368425472565343575785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268245616981710229050523 4902368425472565343575785)
        ·
          refine ⟨3676776319104424007681839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4902368425472565343575785 3676776319104424007681839)
          ·
            refine ⟨5515164478656636011522759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676776319104424007681839 5515164478656636011522759)
            ·
              refine ⟨8272746717984954017284139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515164478656636011522759 8272746717984954017284139)
              ·
                refine ⟨12409120076977431025926209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8272746717984954017284139 12409120076977431025926209)
                ·
                  refine ⟨9306840057733073269444657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12409120076977431025926209 9306840057733073269444657)
                  ·
                    refine ⟨6980130043299804952083493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9306840057733073269444657 6980130043299804952083493)
                    ·
                      refine ⟨1308774383118713428515655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6980130043299804952083493 1308774383118713428515655)
                      ·
                        rfl

theorem cell23_2548829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2548829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548829 prefixEnd_2548829 := by exact prefixLift 2548829
  have htrace : WordTrace (prefixWord ++ tailWord_2548829) baseStart_2548829 baseEnd_2548829 := by
    simpa [prefixWord, tailWord_2548829, baseEnd_2548829] using wordTrace_append hprefix tailTrace_2548829
  have hstable : (prefixWord ++ tailWord_2548829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548829).length < 2 ^ (prefixWord ++ tailWord_2548829).sum := by decide
  have hdescent : baseEnd_2548829 < baseStart_2548829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548855 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_2548855 : Nat := 118140960795 + 2548855 * 2 ^ 59
def prefixEnd_2548855 : Nat := 4983230072969 + 3 ^ 40 * 2548855 * 2
def baseEnd_2548855 : Nat := 1308787733615730326790535

theorem tailTrace_2548855 : CollatzResearch.WordTrace tailWord_2548855 prefixEnd_2548855 1308787733615730326790535 := by
  unfold tailWord_2548855
  simp only [CollatzResearch.WordTrace]
  refine ⟨92964379180941119622328019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61976252787294079748218679 92964379180941119622328019)
  ·
    refine ⟨139446568771411679433492029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92964379180941119622328019 139446568771411679433492029)
    ·
      refine ⟨52292463289279379787559511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139446568771411679433492029 52292463289279379787559511)
      ·
        refine ⟨78438694933919069681339267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52292463289279379787559511 78438694933919069681339267)
        ·
          refine ⟨117658042400878604522008901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78438694933919069681339267 117658042400878604522008901)
          ·
            refine ⟨22060882950164738347876669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117658042400878604522008901 22060882950164738347876669)
            ·
              refine ⟨8272831106311776880453751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22060882950164738347876669 8272831106311776880453751)
              ·
                refine ⟨12409246659467665320680627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8272831106311776880453751 12409246659467665320680627)
                ·
                  refine ⟨18613869989201497981020941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12409246659467665320680627 18613869989201497981020941)
                  ·
                    refine ⟨6980201245950561742882853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18613869989201497981020941 6980201245950561742882853)
                    ·
                      refine ⟨1308787733615730326790535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6980201245950561742882853 1308787733615730326790535)
                      ·
                        rfl

theorem cell23_2548855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_2548855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548855 prefixEnd_2548855 := by exact prefixLift 2548855
  have htrace : WordTrace (prefixWord ++ tailWord_2548855) baseStart_2548855 baseEnd_2548855 := by
    simpa [prefixWord, tailWord_2548855, baseEnd_2548855] using wordTrace_append hprefix tailTrace_2548855
  have hstable : (prefixWord ++ tailWord_2548855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548855).length < 2 ^ (prefixWord ++ tailWord_2548855).sum := by decide
  have hdescent : baseEnd_2548855 < baseStart_2548855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548892 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2548892 : Nat := 118140960795 + 2548892 * 2 ^ 59
def prefixEnd_2548892 : Nat := 4983230072969 + 3 ^ 40 * 2548892 * 2
def baseEnd_2548892 : Nat := 1308806732399946682027865

theorem tailTrace_2548892 : CollatzResearch.WordTrace tailWord_2548892 prefixEnd_2548892 1308806732399946682027865 := by
  unfold tailWord_2548892
  simp only [CollatzResearch.WordTrace]
  refine ⟨46482864340903537470712465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61977152454538049960949953 46482864340903537470712465)
  ·
    refine ⟨34862148255677653103034349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46482864340903537470712465 34862148255677653103034349)
    ·
      refine ⟨13073305595879119913637881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34862148255677653103034349 13073305595879119913637881)
      ·
        refine ⟨9804979196909339935228411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13073305595879119913637881 9804979196909339935228411)
        ·
          refine ⟨14707468795364009902842617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804979196909339935228411 14707468795364009902842617)
          ·
            refine ⟨11030601596523007427131963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14707468795364009902842617 11030601596523007427131963)
            ·
              refine ⟨16545902394784511140697945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11030601596523007427131963 16545902394784511140697945)
              ·
                refine ⟨12409426796088383355523459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16545902394784511140697945 12409426796088383355523459)
                ·
                  refine ⟨18614140194132575033285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12409426796088383355523459 18614140194132575033285189)
                  ·
                    refine ⟨3490151286399857818740973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18614140194132575033285189 3490151286399857818740973)
                    ·
                      refine ⟨1308806732399946682027865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490151286399857818740973 1308806732399946682027865)
                      ·
                        rfl

theorem cell23_2548892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2548892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548892 prefixEnd_2548892 := by exact prefixLift 2548892
  have htrace : WordTrace (prefixWord ++ tailWord_2548892) baseStart_2548892 baseEnd_2548892 := by
    simpa [prefixWord, tailWord_2548892, baseEnd_2548892] using wordTrace_append hprefix tailTrace_2548892
  have hstable : (prefixWord ++ tailWord_2548892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548892).length < 2 ^ (prefixWord ++ tailWord_2548892).sum := by decide
  have hdescent : baseEnd_2548892 < baseStart_2548892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548945 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_2548945 : Nat := 118140960795 + 2548945 * 2 ^ 59
def prefixEnd_2548945 : Nat := 4983230072969 + 3 ^ 40 * 2548945 * 2
def baseEnd_2548945 : Nat := 1308833946874634974665121

theorem tailTrace_2548945 : CollatzResearch.WordTrace tailWord_2548945 prefixEnd_2548945 1308833946874634974665121 := by
  unfold tailWord_2548945
  simp only [CollatzResearch.WordTrace]
  refine ⟨92967661750615064993104289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61978441167076709995402859 92967661750615064993104289)
  ·
    refine ⟨69725746312961298744828217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92967661750615064993104289 69725746312961298744828217)
    ·
      refine ⟨52294309734720974058621163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69725746312961298744828217 52294309734720974058621163)
      ·
        refine ⟨78441464602081461087931745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52294309734720974058621163 78441464602081461087931745)
        ·
          refine ⟨58831098451561095815948809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78441464602081461087931745 58831098451561095815948809)
          ·
            refine ⟨44123323838670821861961607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58831098451561095815948809 44123323838670821861961607)
            ·
              refine ⟨66184985758006232792942411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44123323838670821861961607 66184985758006232792942411)
              ·
                refine ⟨99277478637009349189413617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66184985758006232792942411 99277478637009349189413617)
                ·
                  refine ⟨74458108977757011892060213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99277478637009349189413617 74458108977757011892060213)
                  ·
                    refine ⟨6980447716664719864880645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74458108977757011892060213 6980447716664719864880645)
                    ·
                      refine ⟨1308833946874634974665121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6980447716664719864880645 1308833946874634974665121)
                      ·
                        rfl

theorem cell23_2548945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_2548945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548945 prefixEnd_2548945 := by exact prefixLift 2548945
  have htrace : WordTrace (prefixWord ++ tailWord_2548945) baseStart_2548945 baseEnd_2548945 := by
    simpa [prefixWord, tailWord_2548945, baseEnd_2548945] using wordTrace_append hprefix tailTrace_2548945
  have hstable : (prefixWord ++ tailWord_2548945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548945).length < 2 ^ (prefixWord ++ tailWord_2548945).sum := by decide
  have hdescent : baseEnd_2548945 < baseStart_2548945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548972 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_2548972 : Nat := 118140960795 + 2548972 * 2 ^ 59
def prefixEnd_2548972 : Nat := 4983230072969 + 3 ^ 40 * 2548972 * 2
def baseEnd_2548972 : Nat := 436282603617435456342499

theorem tailTrace_2548972 : CollatzResearch.WordTrace tailWord_2548972 prefixEnd_2548972 436282603617435456342499 := by
  unfold tailWord_2548972
  simp only [CollatzResearch.WordTrace]
  refine ⟨46484323260758624302168585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61979097681011499069558113 46484323260758624302168585)
  ·
    refine ⟨34863242445568968226626439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46484323260758624302168585 34863242445568968226626439)
    ·
      refine ⟨52294863668353452339939659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34863242445568968226626439 52294863668353452339939659)
      ·
        refine ⟨78442295502530178509909489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52294863668353452339939659 78442295502530178509909489)
        ·
          refine ⟨58831721626897633882432117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78442295502530178509909489 58831721626897633882432117)
          ·
            refine ⟨5515473902521653176478011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58831721626897633882432117 5515473902521653176478011)
            ·
              refine ⟨8273210853782479764717017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515473902521653176478011 8273210853782479764717017)
              ·
                refine ⟨6204908140336859823537763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8273210853782479764717017 6204908140336859823537763)
                ·
                  refine ⟨9307362210505289735306645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204908140336859823537763 9307362210505289735306645)
                  ·
                    refine ⟨436282603617435456342499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9307362210505289735306645 436282603617435456342499)
                    ·
                      rfl

theorem cell23_2548972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_2548972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548972 prefixEnd_2548972 := by exact prefixLift 2548972
  have htrace : WordTrace (prefixWord ++ tailWord_2548972) baseStart_2548972 baseEnd_2548972 := by
    simpa [prefixWord, tailWord_2548972, baseEnd_2548972] using wordTrace_append hprefix tailTrace_2548972
  have hstable : (prefixWord ++ tailWord_2548972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548972).length < 2 ^ (prefixWord ++ tailWord_2548972).sum := by decide
  have hdescent : baseEnd_2548972 < baseStart_2548972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548990 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2548990 : Nat := 118140960795 + 2548990 * 2 ^ 59
def prefixEnd_2548990 : Nat := 4983230072969 + 3 ^ 40 * 2548990 * 2
def baseEnd_2548990 : Nat := 1308857053504087298602415

theorem tailTrace_2548990 : CollatzResearch.WordTrace tailWord_2548990 prefixEnd_2548990 1308857053504087298602415 := by
  unfold tailWord_2548990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621162879431504709811553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61979535356968025118994949 11621162879431504709811553)
  ·
    refine ⟨8715872159573628532358665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11621162879431504709811553 8715872159573628532358665)
    ·
      refine ⟨6536904119680221399268999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8715872159573628532358665 6536904119680221399268999)
      ·
        refine ⟨9805356179520332098903499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536904119680221399268999 9805356179520332098903499)
        ·
          refine ⟨14708034269280498148355249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9805356179520332098903499 14708034269280498148355249)
          ·
            refine ⟨11031025701960373611266437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14708034269280498148355249 11031025701960373611266437)
            ·
              refine ⟨2068317319117570052112457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11031025701960373611266437 2068317319117570052112457)
              ·
                refine ⟨1551237989338177539084343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068317319117570052112457 1551237989338177539084343)
                ·
                  refine ⟨2326856984007266308626515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551237989338177539084343 2326856984007266308626515)
                  ·
                    refine ⟨3490285476010899462939773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2326856984007266308626515 3490285476010899462939773)
                    ·
                      refine ⟨1308857053504087298602415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490285476010899462939773 1308857053504087298602415)
                      ·
                        rfl

theorem cell23_2548990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2548990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548990 prefixEnd_2548990 := by exact prefixLift 2548990
  have htrace : WordTrace (prefixWord ++ tailWord_2548990) baseStart_2548990 baseEnd_2548990 := by
    simpa [prefixWord, tailWord_2548990, baseEnd_2548990] using wordTrace_append hprefix tailTrace_2548990
  have hstable : (prefixWord ++ tailWord_2548990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548990).length < 2 ^ (prefixWord ++ tailWord_2548990).sum := by decide
  have hdescent : baseEnd_2548990 < baseStart_2548990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549029 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_2549029 : Nat := 118140960795 + 2549029 * 2 ^ 59
def prefixEnd_2549029 : Nat := 4983230072969 + 3 ^ 40 * 2549029 * 2
def baseEnd_2549029 : Nat := 1308877079249612646014735

theorem tailTrace_2549029 : CollatzResearch.WordTrace tailWord_2549029 prefixEnd_2549029 1308877079249612646014735 := by
  unfold tailWord_2549029
  simp only [CollatzResearch.WordTrace]
  refine ⟨92970725482310747339162141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61980483654873831559441427 92970725482310747339162141)
  ·
    refine ⟨34864022055866530252185803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92970725482310747339162141 34864022055866530252185803)
    ·
      refine ⟨52296033083799795378278705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34864022055866530252185803 52296033083799795378278705)
      ·
        refine ⟨39222024812849846533709029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52296033083799795378278705 39222024812849846533709029)
        ·
          refine ⟨7354129652409346225070443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39222024812849846533709029 7354129652409346225070443)
          ·
            refine ⟨11031194478614019337605665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354129652409346225070443 11031194478614019337605665)
            ·
              refine ⟨8273395858960514503204249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11031194478614019337605665 8273395858960514503204249)
              ·
                refine ⟨6205046894220385877403187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8273395858960514503204249 6205046894220385877403187)
                ·
                  refine ⟨9307570341330578816104781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205046894220385877403187 9307570341330578816104781)
                  ·
                    refine ⟨3490338877998967056039293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9307570341330578816104781 3490338877998967056039293)
                    ·
                      refine ⟨1308877079249612646014735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490338877998967056039293 1308877079249612646014735)
                      ·
                        rfl

theorem cell23_2549029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_2549029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549029 prefixEnd_2549029 := by exact prefixLift 2549029
  have htrace : WordTrace (prefixWord ++ tailWord_2549029) baseStart_2549029 baseEnd_2549029 := by
    simpa [prefixWord, tailWord_2549029, baseEnd_2549029] using wordTrace_append hprefix tailTrace_2549029
  have hstable : (prefixWord ++ tailWord_2549029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549029).length < 2 ^ (prefixWord ++ tailWord_2549029).sum := by decide
  have hdescent : baseEnd_2549029 < baseStart_2549029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549035 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_2549035 : Nat := 118140960795 + 2549035 * 2 ^ 59
def prefixEnd_2549035 : Nat := 4983230072969 + 3 ^ 40 * 2549035 * 2
def baseEnd_2549035 : Nat := 1308880160133539622539707

theorem tailTrace_2549035 : CollatzResearch.WordTrace tailWord_2549035 prefixEnd_2549035 1308880160133539622539707 := by
  unfold tailWord_2549035
  simp only [CollatzResearch.WordTrace]
  refine ⟨92970944320289010363880559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61980629546859340242587039 92970944320289010363880559)
  ·
    refine ⟨139456416480433515545820839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92970944320289010363880559 139456416480433515545820839)
    ·
      refine ⟨209184624720650273318731259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139456416480433515545820839 209184624720650273318731259)
      ·
        refine ⟨313776937080975409978096889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209184624720650273318731259 313776937080975409978096889)
        ·
          refine ⟨235332702810731557483572667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313776937080975409978096889 235332702810731557483572667)
          ·
            refine ⟨352999054216097336225359001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235332702810731557483572667 352999054216097336225359001)
            ·
              refine ⟨264749290662073002169019251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352999054216097336225359001 264749290662073002169019251)
              ·
                refine ⟨397123935993109503253528877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264749290662073002169019251 397123935993109503253528877)
                ·
                  refine ⟨148921475997416063720073329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397123935993109503253528877 148921475997416063720073329)
                  ·
                    refine ⟨111691106998062047790054997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148921475997416063720073329 111691106998062047790054997)
                    ·
                      refine ⟨1308880160133539622539707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111691106998062047790054997 1308880160133539622539707)
                      ·
                        rfl

theorem cell23_2549035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_2549035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549035 prefixEnd_2549035 := by exact prefixLift 2549035
  have htrace : WordTrace (prefixWord ++ tailWord_2549035) baseStart_2549035 baseEnd_2549035 := by
    simpa [prefixWord, tailWord_2549035, baseEnd_2549035] using wordTrace_append hprefix tailTrace_2549035
  have hstable : (prefixWord ++ tailWord_2549035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549035).length < 2 ^ (prefixWord ++ tailWord_2549035).sum := by decide
  have hdescent : baseEnd_2549035 < baseStart_2549035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549063 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_2549063 : Nat := 118140960795 + 2549063 * 2 ^ 59
def prefixEnd_2549063 : Nat := 4983230072969 + 3 ^ 40 * 2549063 * 2
def baseEnd_2549063 : Nat := 1308894537591865512989579

theorem tailTrace_2549063 : CollatzResearch.WordTrace tailWord_2549063 prefixEnd_2549063 1308894537591865512989579 := by
  unfold tailWord_2549063
  simp only [CollatzResearch.WordTrace]
  refine ⟨92971965564187571145899843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61981310376125047430599895 92971965564187571145899843)
  ·
    refine ⟨139457948346281356718849765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92971965564187571145899843 139457948346281356718849765)
    ·
      refine ⟨26148365314927754384784331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139457948346281356718849765 26148365314927754384784331)
      ·
        refine ⟨39222547972391631577176497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26148365314927754384784331 39222547972391631577176497)
        ·
          refine ⟨29416910979293723682882373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39222547972391631577176497 29416910979293723682882373)
          ·
            refine ⟨5515670808617573190540445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29416910979293723682882373 5515670808617573190540445)
            ·
              refine ⟨2068376553231589946452667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5515670808617573190540445 2068376553231589946452667)
              ·
                refine ⟨3102564829847384919679001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068376553231589946452667 3102564829847384919679001)
                ·
                  refine ⟨2326923622385538689759251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3102564829847384919679001 2326923622385538689759251)
                  ·
                    refine ⟨3490385433578308034638877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2326923622385538689759251 3490385433578308034638877)
                    ·
                      refine ⟨1308894537591865512989579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490385433578308034638877 1308894537591865512989579)
                      ·
                        rfl

theorem cell23_2549063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_2549063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549063 prefixEnd_2549063 := by exact prefixLift 2549063
  have htrace : WordTrace (prefixWord ++ tailWord_2549063) baseStart_2549063 baseEnd_2549063 := by
    simpa [prefixWord, tailWord_2549063, baseEnd_2549063] using wordTrace_append hprefix tailTrace_2549063
  have hstable : (prefixWord ++ tailWord_2549063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549063).length < 2 ^ (prefixWord ++ tailWord_2549063).sum := by decide
  have hdescent : baseEnd_2549063 < baseStart_2549063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549072 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_2549072 : Nat := 118140960795 + 2549072 * 2 ^ 59
def prefixEnd_2549072 : Nat := 4983230072969 + 3 ^ 40 * 2549072 * 2
def baseEnd_2549072 : Nat := 1308899158917755977777037

theorem tailTrace_2549072 : CollatzResearch.WordTrace tailWord_2549072 prefixEnd_2549072 1308899158917755977777037 := by
  unfold tailWord_2549072
  simp only [CollatzResearch.WordTrace]
  refine ⟨46486146910577482841488735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61981529214103310455318313 46486146910577482841488735)
  ·
    refine ⟨69729220365866224262233103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46486146910577482841488735 69729220365866224262233103)
    ·
      refine ⟨104593830548799336393349655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69729220365866224262233103 104593830548799336393349655)
      ·
        refine ⟨156890745823199004590024483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104593830548799336393349655 156890745823199004590024483)
        ·
          refine ⟨235336118734798506885036725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156890745823199004590024483 235336118734798506885036725)
          ·
            refine ⟨22062761131387360020472193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235336118734798506885036725 22062761131387360020472193)
            ·
              refine ⟨16547070848540520015354145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22062761131387360020472193 16547070848540520015354145)
              ·
                refine ⟨12410303136405390011515609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16547070848540520015354145 12410303136405390011515609)
                ·
                  refine ⟨9307727352304042508636707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12410303136405390011515609 9307727352304042508636707)
                  ·
                    refine ⟨13961591028456063762955061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9307727352304042508636707 13961591028456063762955061)
                    ·
                      refine ⟨1308899158917755977777037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13961591028456063762955061 1308899158917755977777037)
                      ·
                        rfl

theorem cell23_2549072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_2549072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549072 prefixEnd_2549072 := by exact prefixLift 2549072
  have htrace : WordTrace (prefixWord ++ tailWord_2549072) baseStart_2549072 baseEnd_2549072 := by
    simpa [prefixWord, tailWord_2549072, baseEnd_2549072] using wordTrace_append hprefix tailTrace_2549072
  have hstable : (prefixWord ++ tailWord_2549072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549072).length < 2 ^ (prefixWord ++ tailWord_2549072).sum := by decide
  have hdescent : baseEnd_2549072 < baseStart_2549072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549082 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2549082 : Nat := 118140960795 + 2549082 * 2 ^ 59
def prefixEnd_2549082 : Nat := 4983230072969 + 3 ^ 40 * 2549082 * 2
def baseEnd_2549082 : Nat := 1308904293724300938651991

theorem tailTrace_2549082 : CollatzResearch.WordTrace tailWord_2549082 prefixEnd_2549082 1308904293724300938651991 := by
  unfold tailWord_2549082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243164637779684347710375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61981772367412491593894333 23243164637779684347710375)
  ·
    refine ⟨34864746956669526521565563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23243164637779684347710375 34864746956669526521565563)
    ·
      refine ⟨52297120435004289782348345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34864746956669526521565563 52297120435004289782348345)
      ·
        refine ⟨39222840326253217336761259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52297120435004289782348345 39222840326253217336761259)
        ·
          refine ⟨58834260489379826005141889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39222840326253217336761259 58834260489379826005141889)
          ·
            refine ⟨44125695367034869503856417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58834260489379826005141889 44125695367034869503856417)
            ·
              refine ⟨33094271525276152127892313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44125695367034869503856417 33094271525276152127892313)
              ·
                refine ⟨24820703643957114095919235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33094271525276152127892313 24820703643957114095919235)
                ·
                  refine ⟨37231055465935671143878853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24820703643957114095919235 37231055465935671143878853)
                  ·
                    refine ⟨6980822899862938339477285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37231055465935671143878853 6980822899862938339477285)
                    ·
                      refine ⟨1308904293724300938651991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6980822899862938339477285 1308904293724300938651991)
                      ·
                        rfl

theorem cell23_2549082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2549082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549082 prefixEnd_2549082 := by exact prefixLift 2549082
  have htrace : WordTrace (prefixWord ++ tailWord_2549082) baseStart_2549082 baseEnd_2549082 := by
    simpa [prefixWord, tailWord_2549082, baseEnd_2549082] using wordTrace_append hprefix tailTrace_2549082
  have hstable : (prefixWord ++ tailWord_2549082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549082).length < 2 ^ (prefixWord ++ tailWord_2549082).sum := by decide
  have hdescent : baseEnd_2549082 < baseStart_2549082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549132 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2549132 : Nat := 118140960795 + 2549132 * 2 ^ 59
def prefixEnd_2549132 : Nat := 4983230072969 + 3 ^ 40 * 2549132 * 2
def baseEnd_2549132 : Nat := 1308929967757025743026761

theorem tailTrace_2549132 : CollatzResearch.WordTrace tailWord_2549132 prefixEnd_2549132 1308929967757025743026761 := by
  unfold tailWord_2549132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46487241100468797965080825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61982988133958397286774433 46487241100468797965080825)
  ·
    refine ⟨34865430825351598473810619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46487241100468797965080825 34865430825351598473810619)
    ·
      refine ⟨52298146238027397710715929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34865430825351598473810619 52298146238027397710715929)
      ·
        refine ⟨39223609678520548283036947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52298146238027397710715929 39223609678520548283036947)
        ·
          refine ⟨58835414517780822424555421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39223609678520548283036947 58835414517780822424555421)
          ·
            refine ⟨22063280444167808409208283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58835414517780822424555421 22063280444167808409208283)
            ·
              refine ⟨33094920666251712613812425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22063280444167808409208283 33094920666251712613812425)
              ·
                refine ⟨24821190499688784460359319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33094920666251712613812425 24821190499688784460359319)
                ·
                  refine ⟨37231785749533176690538979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24821190499688784460359319 37231785749533176690538979)
                  ·
                    refine ⟨55847678624299765035808469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37231785749533176690538979 55847678624299765035808469)
                    ·
                      refine ⟨1308929967757025743026761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55847678624299765035808469 1308929967757025743026761)
                      ·
                        rfl

theorem cell23_2549132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2549132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549132 prefixEnd_2549132 := by exact prefixLift 2549132
  have htrace : WordTrace (prefixWord ++ tailWord_2549132) baseStart_2549132 baseEnd_2549132 := by
    simpa [prefixWord, tailWord_2549132, baseEnd_2549132] using wordTrace_append hprefix tailTrace_2549132
  have hstable : (prefixWord ++ tailWord_2549132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549132).length < 2 ^ (prefixWord ++ tailWord_2549132).sum := by decide
  have hdescent : baseEnd_2549132 < baseStart_2549132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549149 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2549149 : Nat := 118140960795 + 2549149 * 2 ^ 59
def prefixEnd_2549149 : Nat := 4983230072969 + 3 ^ 40 * 2549149 * 2
def baseEnd_2549149 : Nat := 1308938696928152176514183

theorem tailTrace_2549149 : CollatzResearch.WordTrace tailWord_2549149 prefixEnd_2549149 1308938696928152176514183 := by
  unfold tailWord_2549149
  simp only [CollatzResearch.WordTrace]
  refine ⟨92975102241876007833530501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61983401494584005222353667 92975102241876007833530501)
  ·
    refine ⟨17432831670351751468786969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92975102241876007833530501 17432831670351751468786969)
    ·
      refine ⟨13074623752763813601590227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17432831670351751468786969 13074623752763813601590227)
      ·
        refine ⟨19611935629145720402385341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13074623752763813601590227 19611935629145720402385341)
        ·
          refine ⟨7354475860929645150894503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19611935629145720402385341 7354475860929645150894503)
          ·
            refine ⟨11031713791394467726341755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354475860929645150894503 11031713791394467726341755)
            ·
              refine ⟨16547570687091701589512633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11031713791394467726341755 16547570687091701589512633)
              ·
                refine ⟨12410678015318776192134475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16547570687091701589512633 12410678015318776192134475)
                ·
                  refine ⟨18616017022978164288201713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12410678015318776192134475 18616017022978164288201713)
                  ·
                    refine ⟨13962012767233623216151285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18616017022978164288201713 13962012767233623216151285)
                    ·
                      refine ⟨1308938696928152176514183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13962012767233623216151285 1308938696928152176514183)
                      ·
                        rfl

theorem cell23_2549149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2549149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549149 prefixEnd_2549149 := by exact prefixLift 2549149
  have htrace : WordTrace (prefixWord ++ tailWord_2549149) baseStart_2549149 baseEnd_2549149 := by
    simpa [prefixWord, tailWord_2549149, baseEnd_2549149] using wordTrace_append hprefix tailTrace_2549149
  have hstable : (prefixWord ++ tailWord_2549149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549149).length < 2 ^ (prefixWord ++ tailWord_2549149).sum := by decide
  have hdescent : baseEnd_2549149 < baseStart_2549149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549196 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2549196 : Nat := 118140960795 + 2549196 * 2 ^ 59
def prefixEnd_2549196 : Nat := 4983230072969 + 3 ^ 40 * 2549196 * 2
def baseEnd_2549196 : Nat := 1308962830518913492626467

theorem tailTrace_2549196 : CollatzResearch.WordTrace tailWord_2549196 prefixEnd_2549196 1308962830518913492626467 := by
  unfold tailWord_2549196
  simp only [CollatzResearch.WordTrace]
  refine ⟨46488408236352867430245721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61984544315137156573660961 46488408236352867430245721)
  ·
    refine ⟨34866306177264650572684291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46488408236352867430245721 34866306177264650572684291)
    ·
      refine ⟨52299459265896975859026437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34866306177264650572684291 52299459265896975859026437)
      ·
        refine ⟨9806148612355682973567457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52299459265896975859026437 9806148612355682973567457)
        ·
          refine ⟨7354611459266762230175593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9806148612355682973567457 7354611459266762230175593)
          ·
            refine ⟨5515958594450071672631695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354611459266762230175593 5515958594450071672631695)
            ·
              refine ⟨8273937891675107508947543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515958594450071672631695 8273937891675107508947543)
              ·
                refine ⟨12410906837512661263421315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273937891675107508947543 12410906837512661263421315)
                ·
                  refine ⟨18616360256268991895131973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12410906837512661263421315 18616360256268991895131973)
                  ·
                    refine ⟨3490567548050435980337245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18616360256268991895131973 3490567548050435980337245)
                    ·
                      refine ⟨1308962830518913492626467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490567548050435980337245 1308962830518913492626467)
                      ·
                        rfl

theorem cell23_2549196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2549196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549196 prefixEnd_2549196 := by exact prefixLift 2549196
  have htrace : WordTrace (prefixWord ++ tailWord_2549196) baseStart_2549196 baseEnd_2549196 := by
    simpa [prefixWord, tailWord_2549196, baseEnd_2549196] using wordTrace_append hprefix tailTrace_2549196
  have hstable : (prefixWord ++ tailWord_2549196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549196).length < 2 ^ (prefixWord ++ tailWord_2549196).sum := by decide
  have hdescent : baseEnd_2549196 < baseStart_2549196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549206 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2549206 : Nat := 118140960795 + 2549206 * 2 ^ 59
def prefixEnd_2549206 : Nat := 4983230072969 + 3 ^ 40 * 2549206 * 2
def baseEnd_2549206 : Nat := 1308967965325458453501421

theorem tailTrace_2549206 : CollatzResearch.WordTrace tailWord_2549206 prefixEnd_2549206 1308967965325458453501421 := by
  unfold tailWord_2549206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811073825166844160522217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61984787468446337712236981 5811073825166844160522217)
  ·
    refine ⟨4358305368875133120391663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5811073825166844160522217 4358305368875133120391663)
    ·
      refine ⟨6537458053312699680587495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4358305368875133120391663 6537458053312699680587495)
      ·
        refine ⟨9806187079969049520881243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6537458053312699680587495 9806187079969049520881243)
        ·
          refine ⟨14709280619953574281321865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806187079969049520881243 14709280619953574281321865)
          ·
            refine ⟨11031960464965180710991399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14709280619953574281321865 11031960464965180710991399)
            ·
              refine ⟨16547940697447771066487099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11031960464965180710991399 16547940697447771066487099)
              ·
                refine ⟨24821911046171656599730649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16547940697447771066487099 24821911046171656599730649)
                ·
                  refine ⟨18616433284628742449797987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24821911046171656599730649 18616433284628742449797987)
                  ·
                    refine ⟨27924649926943113674696981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18616433284628742449797987 27924649926943113674696981)
                    ·
                      refine ⟨1308967965325458453501421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27924649926943113674696981 1308967965325458453501421)
                      ·
                        rfl

theorem cell23_2549206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2549206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549206 prefixEnd_2549206 := by exact prefixLift 2549206
  have htrace : WordTrace (prefixWord ++ tailWord_2549206) baseStart_2549206 baseEnd_2549206 := by
    simpa [prefixWord, tailWord_2549206, baseEnd_2549206] using wordTrace_append hprefix tailTrace_2549206
  have hstable : (prefixWord ++ tailWord_2549206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549206).length < 2 ^ (prefixWord ++ tailWord_2549206).sum := by decide
  have hdescent : baseEnd_2549206 < baseStart_2549206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549219 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2549219 : Nat := 118140960795 + 2549219 * 2 ^ 59
def prefixEnd_2549219 : Nat := 4983230072969 + 3 ^ 40 * 2549219 * 2
def baseEnd_2549219 : Nat := 1308974640573966902638861

theorem tailTrace_2549219 : CollatzResearch.WordTrace tailWord_2549219 prefixEnd_2549219 1308974640573966902638861 := by
  unfold tailWord_2549219
  simp only [CollatzResearch.WordTrace]
  refine ⟨92977655351622409788578711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61985103567748273192385807 92977655351622409788578711)
  ·
    refine ⟨139466483027433614682868067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92977655351622409788578711 139466483027433614682868067)
    ·
      refine ⟨209199724541150422024302101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139466483027433614682868067 209199724541150422024302101)
      ·
        refine ⟨9806237087866426032389161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 209199724541150422024302101 9806237087866426032389161)
        ·
          refine ⟨7354677815899819524291871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9806237087866426032389161 7354677815899819524291871)
          ·
            refine ⟨11032016723849729286437807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354677815899819524291871 11032016723849729286437807)
            ·
              refine ⟨16548025085774593929656711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032016723849729286437807 16548025085774593929656711)
              ·
                refine ⟨24822037628661890894485067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16548025085774593929656711 24822037628661890894485067)
                ·
                  refine ⟨37233056442992836341727601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24822037628661890894485067 37233056442992836341727601)
                  ·
                    refine ⟨27924792332244627256295701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37233056442992836341727601 27924792332244627256295701)
                    ·
                      refine ⟨1308974640573966902638861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27924792332244627256295701 1308974640573966902638861)
                      ·
                        rfl

theorem cell23_2549219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2549219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549219 prefixEnd_2549219 := by exact prefixLift 2549219
  have htrace : WordTrace (prefixWord ++ tailWord_2549219) baseStart_2549219 baseEnd_2549219 := by
    simpa [prefixWord, tailWord_2549219, baseEnd_2549219] using wordTrace_append hprefix tailTrace_2549219
  have hstable : (prefixWord ++ tailWord_2549219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549219).length < 2 ^ (prefixWord ++ tailWord_2549219).sum := by decide
  have hdescent : baseEnd_2549219 < baseStart_2549219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549276 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2549276 : Nat := 118140960795 + 2549276 * 2 ^ 59
def prefixEnd_2549276 : Nat := 4983230072969 + 3 ^ 40 * 2549276 * 2
def baseEnd_2549276 : Nat := 436334636323757726542033

theorem tailTrace_2549276 : CollatzResearch.WordTrace tailWord_2549276 prefixEnd_2549276 436334636323757726542033 := by
  unfold tailWord_2549276
  simp only [CollatzResearch.WordTrace]
  refine ⟨46489867156207954261701841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61986489541610605682269121 46489867156207954261701841)
  ·
    refine ⟨34867400367155965696276381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46489867156207954261701841 34867400367155965696276381)
    ·
      refine ⟨13075275137683487136103643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34867400367155965696276381 13075275137683487136103643)
      ·
        refine ⟨19612912706525230704155465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13075275137683487136103643 19612912706525230704155465)
        ·
          refine ⟨14709684529893923028116599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19612912706525230704155465 14709684529893923028116599)
          ·
            refine ⟨22064526794840884542174899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14709684529893923028116599 22064526794840884542174899)
            ·
              refine ⟨33096790192261326813262349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22064526794840884542174899 33096790192261326813262349)
              ·
                refine ⟨12411296322097997554973381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33096790192261326813262349 12411296322097997554973381)
                ·
                  refine ⟨2327118060393374541557509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12411296322097997554973381 2327118060393374541557509)
                  ·
                    refine ⟨436334636323757726542033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327118060393374541557509 436334636323757726542033)
                    ·
                      rfl

theorem cell23_2549276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2549276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549276 prefixEnd_2549276 := by exact prefixLift 2549276
  have htrace : WordTrace (prefixWord ++ tailWord_2549276) baseStart_2549276 baseEnd_2549276 := by
    simpa [prefixWord, tailWord_2549276, baseEnd_2549276] using wordTrace_append hprefix tailTrace_2549276
  have hstable : (prefixWord ++ tailWord_2549276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549276).length < 2 ^ (prefixWord ++ tailWord_2549276).sum := by decide
  have hdescent : baseEnd_2549276 < baseStart_2549276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549277 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_2549277 : Nat := 118140960795 + 2549277 * 2 ^ 59
def prefixEnd_2549277 : Nat := 4983230072969 + 3 ^ 40 * 2549277 * 2
def baseEnd_2549277 : Nat := 1309004422451927675713595

theorem tailTrace_2549277 : CollatzResearch.WordTrace tailWord_2549277 prefixEnd_2549277 1309004422451927675713595 := by
  unfold tailWord_2549277
  simp only [CollatzResearch.WordTrace]
  refine ⟨92979770785412285694190085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61986513856941523796126723 92979770785412285694190085)
  ·
    refine ⟨17433707022264803567660641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92979770785412285694190085 17433707022264803567660641)
    ·
      refine ⟨13075280266698602675745481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17433707022264803567660641 13075280266698602675745481)
      ·
        refine ⟨9806460200023952006809111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13075280266698602675745481 9806460200023952006809111)
        ·
          refine ⟨14709690300035928010213667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806460200023952006809111 14709690300035928010213667)
          ·
            refine ⟨22064535450053892015320501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14709690300035928010213667 22064535450053892015320501)
            ·
              refine ⟨2068550198442552376436297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22064535450053892015320501 2068550198442552376436297)
              ·
                refine ⟨1551412648831914282327223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068550198442552376436297 1551412648831914282327223)
                ·
                  refine ⟨2327118973247871423490835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551412648831914282327223 2327118973247871423490835)
                  ·
                    refine ⟨3490678459871807135236253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2327118973247871423490835 3490678459871807135236253)
                    ·
                      refine ⟨1309004422451927675713595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490678459871807135236253 1309004422451927675713595)
                      ·
                        rfl

theorem cell23_2549277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_2549277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549277 prefixEnd_2549277 := by exact prefixLift 2549277
  have htrace : WordTrace (prefixWord ++ tailWord_2549277) baseStart_2549277 baseEnd_2549277 := by
    simpa [prefixWord, tailWord_2549277, baseEnd_2549277] using wordTrace_append hprefix tailTrace_2549277
  have hstable : (prefixWord ++ tailWord_2549277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549277).length < 2 ^ (prefixWord ++ tailWord_2549277).sum := by decide
  have hdescent : baseEnd_2549277 < baseStart_2549277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549279 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2549279 : Nat := 118140960795 + 2549279 * 2 ^ 59
def prefixEnd_2549279 : Nat := 4983230072969 + 3 ^ 40 * 2549279 * 2
def baseEnd_2549279 : Nat := 1309005449413236667888585

theorem tailTrace_2549279 : CollatzResearch.WordTrace tailWord_2549279 prefixEnd_2549279 1309005449413236667888585 := by
  unfold tailWord_2549279
  simp only [CollatzResearch.WordTrace]
  refine ⟨92979843731405040035762891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61986562487603360023841927 92979843731405040035762891)
  ·
    refine ⟨139469765597107560053644337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92979843731405040035762891 139469765597107560053644337)
    ·
      refine ⟨104602324197830670040233253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139469765597107560053644337 104602324197830670040233253)
      ·
        refine ⟨19612935787093250632543735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104602324197830670040233253 19612935787093250632543735)
        ·
          refine ⟨29419403680639875948815603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19612935787093250632543735 29419403680639875948815603)
          ·
            refine ⟨44129105520959813923223405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29419403680639875948815603 44129105520959813923223405)
            ·
              refine ⟨16548414570359930221208777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44129105520959813923223405 16548414570359930221208777)
              ·
                refine ⟨12411310927769947665906583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16548414570359930221208777 12411310927769947665906583)
                ·
                  refine ⟨18616966391654921498859875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12411310927769947665906583 18616966391654921498859875)
                  ·
                    refine ⟨27925449587482382248289813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18616966391654921498859875 27925449587482382248289813)
                    ·
                      refine ⟨1309005449413236667888585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27925449587482382248289813 1309005449413236667888585)
                      ·
                        rfl

theorem cell23_2549279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2549279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549279 prefixEnd_2549279 := by exact prefixLift 2549279
  have htrace : WordTrace (prefixWord ++ tailWord_2549279) baseStart_2549279 baseEnd_2549279 := by
    simpa [prefixWord, tailWord_2549279, baseEnd_2549279] using wordTrace_append hprefix tailTrace_2549279
  have hstable : (prefixWord ++ tailWord_2549279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549279).length < 2 ^ (prefixWord ++ tailWord_2549279).sum := by decide
  have hdescent : baseEnd_2549279 < baseStart_2549279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549303 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_2549303 : Nat := 118140960795 + 2549303 * 2 ^ 59
def prefixEnd_2549303 : Nat := 4983230072969 + 3 ^ 40 * 2549303 * 2
def baseEnd_2549303 : Nat := 1309017772948944573988475

theorem tailTrace_2549303 : CollatzResearch.WordTrace tailWord_2549303 prefixEnd_2549303 1309017772948944573988475 := by
  unfold tailWord_2549303
  simp only [CollatzResearch.WordTrace]
  refine ⟨92980719083318092134636563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61987146055545394756424375 92980719083318092134636563)
  ·
    refine ⟨139471078624977138201954845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92980719083318092134636563 139471078624977138201954845)
    ·
      refine ⟨52301654484366426825733067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139471078624977138201954845 52301654484366426825733067)
      ·
        refine ⟨78452481726549640238599601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52301654484366426825733067 78452481726549640238599601)
        ·
          refine ⟨58839361294912230178949701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78452481726549640238599601 58839361294912230178949701)
          ·
            refine ⟨11032380242796043158553069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58839361294912230178949701 11032380242796043158553069)
            ·
              refine ⟨4137142591048516184457401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11032380242796043158553069 4137142591048516184457401)
              ·
                refine ⟨3102856943286387138343051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137142591048516184457401 3102856943286387138343051)
                ·
                  refine ⟨4654285414929580707514577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102856943286387138343051 4654285414929580707514577)
                  ·
                    refine ⟨3490714061197185530635933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654285414929580707514577 3490714061197185530635933)
                    ·
                      refine ⟨1309017772948944573988475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490714061197185530635933 1309017772948944573988475)
                      ·
                        rfl

theorem cell23_2549303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_2549303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549303 prefixEnd_2549303 := by exact prefixLift 2549303
  have htrace : WordTrace (prefixWord ++ tailWord_2549303) baseStart_2549303 baseEnd_2549303 := by
    simpa [prefixWord, tailWord_2549303, baseEnd_2549303] using wordTrace_append hprefix tailTrace_2549303
  have hstable : (prefixWord ++ tailWord_2549303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549303).length < 2 ^ (prefixWord ++ tailWord_2549303).sum := by decide
  have hdescent : baseEnd_2549303 < baseStart_2549303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549377 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_2549377 : Nat := 118140960795 + 2549377 * 2 ^ 59
def prefixEnd_2549377 : Nat := 4983230072969 + 3 ^ 40 * 2549377 * 2
def baseEnd_2549377 : Nat := 1309055770517377284463135

theorem tailTrace_2549377 : CollatzResearch.WordTrace tailWord_2549377 prefixEnd_2549377 1309055770517377284463135 := by
  unfold tailWord_2549377
  simp only [CollatzResearch.WordTrace]
  refine ⟨92983418085050002772830385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61988945390033335181886923 92983418085050002772830385)
  ·
    refine ⟨69737563563787502079622789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92983418085050002772830385 69737563563787502079622789)
    ·
      refine ⟨13075793168210156639929273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69737563563787502079622789 13075793168210156639929273)
      ·
        refine ⟨9806844876157617479946955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13075793168210156639929273 9806844876157617479946955)
        ·
          refine ⟨14710267314236426219920433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806844876157617479946955 14710267314236426219920433)
          ·
            refine ⟨11032700485677319664940325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14710267314236426219920433 11032700485677319664940325)
            ·
              refine ⟨2068631341064497437176311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11032700485677319664940325 2068631341064497437176311)
              ·
                refine ⟨3102947011596746155764467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068631341064497437176311 3102947011596746155764467)
                ·
                  refine ⟨4654420517395119233646701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102947011596746155764467 4654420517395119233646701)
                  ·
                    refine ⟨1745407694023169712617513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4654420517395119233646701 1745407694023169712617513)
                    ·
                      refine ⟨1309055770517377284463135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745407694023169712617513 1309055770517377284463135)
                      ·
                        rfl

theorem cell23_2549377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_2549377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549377 prefixEnd_2549377 := by exact prefixLift 2549377
  have htrace : WordTrace (prefixWord ++ tailWord_2549377) baseStart_2549377 baseEnd_2549377 := by
    simpa [prefixWord, tailWord_2549377, baseEnd_2549377] using wordTrace_append hprefix tailTrace_2549377
  have hstable : (prefixWord ++ tailWord_2549377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549377).length < 2 ^ (prefixWord ++ tailWord_2549377).sum := by decide
  have hdescent : baseEnd_2549377 < baseStart_2549377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549379 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 11]
def baseStart_2549379 : Nat := 118140960795 + 2549379 * 2 ^ 59
def prefixEnd_2549379 : Nat := 4983230072969 + 3 ^ 40 * 2549379 * 2
def baseEnd_2549379 : Nat := 145450755275409586293125

theorem tailTrace_2549379 : CollatzResearch.WordTrace tailWord_2549379 prefixEnd_2549379 145450755275409586293125 := by
  unfold tailWord_2549379
  simp only [CollatzResearch.WordTrace]
  refine ⟨92983491031042757114403191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61988994020695171409602127 92983491031042757114403191)
  ·
    refine ⟨139475236546564135671604787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92983491031042757114403191 139475236546564135671604787)
    ·
      refine ⟨209212854819846203507407181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139475236546564135671604787 209212854819846203507407181)
      ·
        refine ⟨78454820557442326315277693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209212854819846203507407181 78454820557442326315277693)
        ·
          refine ⟨29420557709040872368229135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78454820557442326315277693 29420557709040872368229135)
          ·
            refine ⟨44130836563561308552343703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29420557709040872368229135 44130836563561308552343703)
            ·
              refine ⟨66196254845341962828515555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44130836563561308552343703 66196254845341962828515555)
              ·
                refine ⟨99294382268012944242773333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66196254845341962828515555 99294382268012944242773333)
                ·
                  refine ⟨145450755275409586293125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 99294382268012944242773333 145450755275409586293125)
                  ·
                    rfl

theorem cell23_2549379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 11].length) (baseStart_2549379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549379 prefixEnd_2549379 := by exact prefixLift 2549379
  have htrace : WordTrace (prefixWord ++ tailWord_2549379) baseStart_2549379 baseEnd_2549379 := by
    simpa [prefixWord, tailWord_2549379, baseEnd_2549379] using wordTrace_append hprefix tailTrace_2549379
  have hstable : (prefixWord ++ tailWord_2549379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549379).length < 2 ^ (prefixWord ++ tailWord_2549379).sum := by decide
  have hdescent : baseEnd_2549379 < baseStart_2549379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549384 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2549384 : Nat := 118140960795 + 2549384 * 2 ^ 59
def prefixEnd_2549384 : Nat := 4983230072969 + 3 ^ 40 * 2549384 * 2
def baseEnd_2549384 : Nat := 1309059364881958757075603

theorem tailTrace_2549384 : CollatzResearch.WordTrace tailWord_2549384 prefixEnd_2549384 1309059364881958757075603 := by
  unfold tailWord_2549384
  simp only [CollatzResearch.WordTrace]
  refine ⟨46491836698012321484167603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61989115597349761978890137 46491836698012321484167603)
  ·
    refine ⟨69737755047018482226251405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46491836698012321484167603 69737755047018482226251405)
    ·
      refine ⟨26151658142631930834844277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69737755047018482226251405 26151658142631930834844277)
      ·
        refine ⟨2451717950871743515766651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26151658142631930834844277 2451717950871743515766651)
        ·
          refine ⟨3677576926307615273649977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451717950871743515766651 3677576926307615273649977)
          ·
            refine ⟨2758182694730711455237483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3677576926307615273649977 2758182694730711455237483)
            ·
              refine ⟨4137274042096067182856225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758182694730711455237483 4137274042096067182856225)
              ·
                refine ⟨3102955531572050387142169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137274042096067182856225 3102955531572050387142169)
                ·
                  refine ⟨2327216648679037790356627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3102955531572050387142169 2327216648679037790356627)
                  ·
                    refine ⟨3490824973018556685534941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2327216648679037790356627 3490824973018556685534941)
                    ·
                      refine ⟨1309059364881958757075603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490824973018556685534941 1309059364881958757075603)
                      ·
                        rfl

theorem cell23_2549384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2549384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549384 prefixEnd_2549384 := by exact prefixLift 2549384
  have htrace : WordTrace (prefixWord ++ tailWord_2549384) baseStart_2549384 baseEnd_2549384 := by
    simpa [prefixWord, tailWord_2549384, baseEnd_2549384] using wordTrace_append hprefix tailTrace_2549384
  have hstable : (prefixWord ++ tailWord_2549384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549384).length < 2 ^ (prefixWord ++ tailWord_2549384).sum := by decide
  have hdescent : baseEnd_2549384 < baseStart_2549384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549426 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_2549426 : Nat := 118140960795 + 2549426 * 2 ^ 59
def prefixEnd_2549426 : Nat := 4983230072969 + 3 ^ 40 * 2549426 * 2
def baseEnd_2549426 : Nat := 436360310356482530916803

theorem tailTrace_2549426 : CollatzResearch.WordTrace tailWord_2549426 prefixEnd_2549426 436360310356482530916803 := by
  unfold tailWord_2549426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246301315468121035341033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61990136841248322760909421 23246301315468121035341033)
  ·
    refine ⟨17434725986601090776505775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23246301315468121035341033 17434725986601090776505775)
    ·
      refine ⟨26152088979901636164758663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17434725986601090776505775 26152088979901636164758663)
      ·
        refine ⟨39228133469852454247137995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26152088979901636164758663 39228133469852454247137995)
        ·
          refine ⟨58842200204778681370706993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39228133469852454247137995 58842200204778681370706993)
          ·
            refine ⟨44131650153584011028030245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58842200204778681370706993 44131650153584011028030245)
            ·
              refine ⟨8274684403797002067755671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44131650153584011028030245 8274684403797002067755671)
              ·
                refine ⟨12412026605695503101633507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8274684403797002067755671 12412026605695503101633507)
                ·
                  refine ⟨18618039908543254652450261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12412026605695503101633507 18618039908543254652450261)
                  ·
                    refine ⟨436360310356482530916803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18618039908543254652450261 436360310356482530916803)
                    ·
                      rfl

theorem cell23_2549426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_2549426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549426 prefixEnd_2549426 := by exact prefixLift 2549426
  have htrace : WordTrace (prefixWord ++ tailWord_2549426) baseStart_2549426 baseEnd_2549426 := by
    simpa [prefixWord, tailWord_2549426, baseEnd_2549426] using wordTrace_append hprefix tailTrace_2549426
  have hstable : (prefixWord ++ tailWord_2549426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549426).length < 2 ^ (prefixWord ++ tailWord_2549426).sum := by decide
  have hdescent : baseEnd_2549426 < baseStart_2549426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549463 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_2549463 : Nat := 118140960795 + 2549463 * 2 ^ 59
def prefixEnd_2549463 : Nat := 4983230072969 + 3 ^ 40 * 2549463 * 2
def baseEnd_2549463 : Nat := 1309099929853663947987739

theorem tailTrace_2549463 : CollatzResearch.WordTrace tailWord_2549463 prefixEnd_2549463 1309099929853663947987739 := by
  unfold tailWord_2549463
  simp only [CollatzResearch.WordTrace]
  refine ⟨92986554762738439460461043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61991036508492292973640695 92986554762738439460461043)
  ·
    refine ⟨139479832144107659190691565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92986554762738439460461043 139479832144107659190691565)
    ·
      refine ⟨52304937054040372196509337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139479832144107659190691565 52304937054040372196509337)
      ·
        refine ⟨39228702790530279147382003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52304937054040372196509337 39228702790530279147382003)
        ·
          refine ⟨58843054185795418721073005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39228702790530279147382003 58843054185795418721073005)
          ·
            refine ⟨22066145319673282020402377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58843054185795418721073005 22066145319673282020402377)
            ·
              refine ⟨16549608989754961515301783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22066145319673282020402377 16549608989754961515301783)
              ·
                refine ⟨24824413484632442272952675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16549608989754961515301783 24824413484632442272952675)
                ·
                  refine ⟨37236620226948663409429013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24824413484632442272952675 37236620226948663409429013)
                  ·
                    refine ⟨1745466573138218597316985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37236620226948663409429013 1745466573138218597316985)
                    ·
                      refine ⟨1309099929853663947987739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745466573138218597316985 1309099929853663947987739)
                      ·
                        rfl

theorem cell23_2549463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_2549463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549463 prefixEnd_2549463 := by exact prefixLift 2549463
  have htrace : WordTrace (prefixWord ++ tailWord_2549463) baseStart_2549463 baseEnd_2549463 := by
    simpa [prefixWord, tailWord_2549463, baseEnd_2549463] using wordTrace_append hprefix tailTrace_2549463
  have hstable : (prefixWord ++ tailWord_2549463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549463).length < 2 ^ (prefixWord ++ tailWord_2549463).sum := by decide
  have hdescent : baseEnd_2549463 < baseStart_2549463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549480 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2549480 : Nat := 118140960795 + 2549480 * 2 ^ 59
def prefixEnd_2549480 : Nat := 4983230072969 + 3 ^ 40 * 2549480 * 2
def baseEnd_2549480 : Nat := 1309108659024790381475161

theorem tailTrace_2549480 : CollatzResearch.WordTrace tailWord_2549480 prefixEnd_2549480 1309108659024790381475161 := by
  unfold tailWord_2549480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46493587401838425681914947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61991449869117900909219929 46493587401838425681914947)
  ·
    refine ⟨69740381102757638522872421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46493587401838425681914947 69740381102757638522872421)
    ·
      refine ⟨13076321456767057223038579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69740381102757638522872421 13076321456767057223038579)
      ·
        refine ⟨19614482185150585834557869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13076321456767057223038579 19614482185150585834557869)
        ·
          refine ⟨7355430819431469687959201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19614482185150585834557869 7355430819431469687959201)
          ·
            refine ⟨5516573114573602265969401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7355430819431469687959201 5516573114573602265969401)
            ·
              refine ⟨4137429835930201699477051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5516573114573602265969401 4137429835930201699477051)
              ·
                refine ⟨6206144753895302549215577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137429835930201699477051 6206144753895302549215577)
                ·
                  refine ⟨4654608565421476911911683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206144753895302549215577 4654608565421476911911683)
                  ·
                    refine ⟨6981912848132215367867525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4654608565421476911911683 6981912848132215367867525)
                    ·
                      refine ⟨1309108659024790381475161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6981912848132215367867525 1309108659024790381475161)
                      ·
                        rfl

theorem cell23_2549480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2549480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549480 prefixEnd_2549480 := by exact prefixLift 2549480
  have htrace : WordTrace (prefixWord ++ tailWord_2549480) baseStart_2549480 baseEnd_2549480 := by
    simpa [prefixWord, tailWord_2549480, baseEnd_2549480] using wordTrace_append hprefix tailTrace_2549480
  have hstable : (prefixWord ++ tailWord_2549480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549480).length < 2 ^ (prefixWord ++ tailWord_2549480).sum := by decide
  have hdescent : baseEnd_2549480 < baseStart_2549480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549483 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3]
def baseStart_2549483 : Nat := 118140960795 + 2549483 * 2 ^ 59
def prefixEnd_2549483 : Nat := 4983230072969 + 3 ^ 40 * 2549483 * 2
def baseEnd_2549483 : Nat := 1309110199466753869737647

theorem tailTrace_2549483 : CollatzResearch.WordTrace tailWord_2549483 prefixEnd_2549483 1309110199466753869737647 := by
  unfold tailWord_2549483
  simp only [CollatzResearch.WordTrace]
  refine ⟨92987284222665982876189103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61991522815110655250792735 92987284222665982876189103)
  ·
    refine ⟨139480926333998974314283655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92987284222665982876189103 139480926333998974314283655)
    ·
      refine ⟨209221389500998461471425483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139480926333998974314283655 209221389500998461471425483)
      ·
        refine ⟨313832084251497692207138225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209221389500998461471425483 313832084251497692207138225)
        ·
          refine ⟨235374063188623269155353669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313832084251497692207138225 235374063188623269155353669)
          ·
            refine ⟨44132636847866862966628813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235374063188623269155353669 44132636847866862966628813)
            ·
              refine ⟨16549738817950073612485805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44132636847866862966628813 16549738817950073612485805)
              ·
                refine ⟨6206152056731277604682177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16549738817950073612485805 6206152056731277604682177)
                ·
                  refine ⟨4654614042548458203511633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206152056731277604682177 4654614042548458203511633)
                  ·
                    refine ⟨3490960531911343652633725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654614042548458203511633 3490960531911343652633725)
                    ·
                      refine ⟨1309110199466753869737647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3490960531911343652633725 1309110199466753869737647)
                      ·
                        rfl

theorem cell23_2549483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3].length) (baseStart_2549483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549483 prefixEnd_2549483 := by exact prefixLift 2549483
  have htrace : WordTrace (prefixWord ++ tailWord_2549483) baseStart_2549483 baseEnd_2549483 := by
    simpa [prefixWord, tailWord_2549483, baseEnd_2549483] using wordTrace_append hprefix tailTrace_2549483
  have hstable : (prefixWord ++ tailWord_2549483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549483).length < 2 ^ (prefixWord ++ tailWord_2549483).sum := by decide
  have hdescent : baseEnd_2549483 < baseStart_2549483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549507 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 1, 4]
def baseStart_2549507 : Nat := 118140960795 + 2549507 * 2 ^ 59
def prefixEnd_2549507 : Nat := 4983230072969 + 3 ^ 40 * 2549507 * 2
def baseEnd_2549507 : Nat := 436374174334153925279179

theorem tailTrace_2549507 : CollatzResearch.WordTrace tailWord_2549507 prefixEnd_2549507 436374174334153925279179 := by
  unfold tailWord_2549507
  simp only [CollatzResearch.WordTrace]
  refine ⟨92988159574579034975062775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61992106383052689983375183 92988159574579034975062775)
  ·
    refine ⟨139482239361868552462594163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92988159574579034975062775 139482239361868552462594163)
    ·
      refine ⟨209223359042802828693891245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139482239361868552462594163 209223359042802828693891245)
      ·
        refine ⟨78458759641051060760209217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209223359042802828693891245 78458759641051060760209217)
        ·
          refine ⟨58844069730788295570156913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78458759641051060760209217 58844069730788295570156913)
          ·
            refine ⟨44133052298091221677617685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58844069730788295570156913 44133052298091221677617685)
            ·
              refine ⟨2068736826473026016138329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44133052298091221677617685 2068736826473026016138329)
              ·
                refine ⟨1551552619854769512103747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068736826473026016138329 1551552619854769512103747)
                ·
                  refine ⟨2327328929782154268155621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551552619854769512103747 2327328929782154268155621)
                  ·
                    refine ⟨436374174334153925279179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327328929782154268155621 436374174334153925279179)
                    ·
                      rfl

theorem cell23_2549507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 4].length) (baseStart_2549507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549507 prefixEnd_2549507 := by exact prefixLift 2549507
  have htrace : WordTrace (prefixWord ++ tailWord_2549507) baseStart_2549507 baseEnd_2549507 := by
    simpa [prefixWord, tailWord_2549507, baseEnd_2549507] using wordTrace_append hprefix tailTrace_2549507
  have hstable : (prefixWord ++ tailWord_2549507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549507).length < 2 ^ (prefixWord ++ tailWord_2549507).sum := by decide
  have hdescent : baseEnd_2549507 < baseStart_2549507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549530 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2549530 : Nat := 118140960795 + 2549530 * 2 ^ 59
def prefixEnd_2549530 : Nat := 4983230072969 + 3 ^ 40 * 2549530 * 2
def baseEnd_2549530 : Nat := 1309134333057515185849931

theorem tailTrace_2549530 : CollatzResearch.WordTrace tailWord_2549530 prefixEnd_2549530 1309134333057515185849931 := by
  unfold tailWord_2549530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247249613373927475787511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61992665635663806602100029 23247249613373927475787511)
  ·
    refine ⟨34870874420060891213681267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23247249613373927475787511 34870874420060891213681267)
    ·
      refine ⟨52306311630091336820521901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34870874420060891213681267 52306311630091336820521901)
      ·
        refine ⟨19614866861284251307695713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52306311630091336820521901 19614866861284251307695713)
        ·
          refine ⟨14711150145963188480771785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19614866861284251307695713 14711150145963188480771785)
          ·
            refine ⟨11033362609472391360578839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14711150145963188480771785 11033362609472391360578839)
            ·
              refine ⟨16550043914208587040868259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033362609472391360578839 16550043914208587040868259)
              ·
                refine ⟨24825065871312880561302389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16550043914208587040868259 24825065871312880561302389)
                ·
                  refine ⟨2327349925435582552622099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24825065871312880561302389 2327349925435582552622099)
                  ·
                    refine ⟨3491024888153373828933149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2327349925435582552622099 3491024888153373828933149)
                    ·
                      refine ⟨1309134333057515185849931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491024888153373828933149 1309134333057515185849931)
                      ·
                        rfl

theorem cell23_2549530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2549530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549530 prefixEnd_2549530 := by exact prefixLift 2549530
  have htrace : WordTrace (prefixWord ++ tailWord_2549530) baseStart_2549530 baseEnd_2549530 := by
    simpa [prefixWord, tailWord_2549530, baseEnd_2549530] using wordTrace_append hprefix tailTrace_2549530
  have hstable : (prefixWord ++ tailWord_2549530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549530).length < 2 ^ (prefixWord ++ tailWord_2549530).sum := by decide
  have hdescent : baseEnd_2549530 < baseStart_2549530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549534 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2549534 : Nat := 118140960795 + 2549534 * 2 ^ 59
def prefixEnd_2549534 : Nat := 4983230072969 + 3 ^ 40 * 2549534 * 2
def baseEnd_2549534 : Nat := 1309136386980133170199913

theorem tailTrace_2549534 : CollatzResearch.WordTrace tailWord_2549534 prefixEnd_2549534 1309136386980133170199913 := by
  unfold tailWord_2549534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623643043185152323286957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61992762896987479057530437 11623643043185152323286957)
  ·
    refine ⟨4358866141194432121232609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11623643043185152323286957 4358866141194432121232609)
    ·
      refine ⟨3269149605895824090924457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4358866141194432121232609 3269149605895824090924457)
      ·
        refine ⟨2451862204421868068193343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269149605895824090924457 2451862204421868068193343)
        ·
          refine ⟨3677793306632802102290015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451862204421868068193343 3677793306632802102290015)
          ·
            refine ⟨5516689959949203153435023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677793306632802102290015 5516689959949203153435023)
            ·
              refine ⟨8275034939923804730152535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516689959949203153435023 8275034939923804730152535)
              ·
                refine ⟨12412552409885707095228803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8275034939923804730152535 12412552409885707095228803)
                ·
                  refine ⟨18618828614828560642843205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12412552409885707095228803 18618828614828560642843205)
                  ·
                    refine ⟨3491030365280355120533101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18618828614828560642843205 3491030365280355120533101)
                    ·
                      refine ⟨1309136386980133170199913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491030365280355120533101 1309136386980133170199913)
                      ·
                        rfl

theorem cell23_2549534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2549534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549534 prefixEnd_2549534 := by exact prefixLift 2549534
  have htrace : WordTrace (prefixWord ++ tailWord_2549534) baseStart_2549534 baseEnd_2549534 := by
    simpa [prefixWord, tailWord_2549534, baseEnd_2549534] using wordTrace_append hprefix tailTrace_2549534
  have hstable : (prefixWord ++ tailWord_2549534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549534).length < 2 ^ (prefixWord ++ tailWord_2549534).sum := by decide
  have hdescent : baseEnd_2549534 < baseStart_2549534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549573 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_2549573 : Nat := 118140960795 + 2549573 * 2 ^ 59
def prefixEnd_2549573 : Nat := 4983230072969 + 3 ^ 40 * 2549573 * 2
def baseEnd_2549573 : Nat := 1309156412725658517612233

theorem tailTrace_2549573 : CollatzResearch.WordTrace tailWord_2549573 prefixEnd_2549573 1309156412725658517612233 := by
  unfold tailWord_2549573
  simp only [CollatzResearch.WordTrace]
  refine ⟨92990566792339928246965373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61993711194893285497976915 92990566792339928246965373)
  ·
    refine ⟨34871462547127473092612015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92990566792339928246965373 34871462547127473092612015)
    ·
      refine ⟨52307193820691209638918023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34871462547127473092612015 52307193820691209638918023)
      ·
        refine ⟨78460790731036814458377035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52307193820691209638918023 78460790731036814458377035)
        ·
          refine ⟨117691186096555221687565553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78460790731036814458377035 117691186096555221687565553)
          ·
            refine ⟨88268389572416416265674165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117691186096555221687565553 88268389572416416265674165)
            ·
              refine ⟨8275161522414039024906953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88268389572416416265674165 8275161522414039024906953)
              ·
                refine ⟨6206371141810529268680215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275161522414039024906953 6206371141810529268680215)
                ·
                  refine ⟨9309556712715793903020323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206371141810529268680215 9309556712715793903020323)
                  ·
                    refine ⟨13964335069073690854530485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9309556712715793903020323 13964335069073690854530485)
                    ·
                      refine ⟨1309156412725658517612233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13964335069073690854530485 1309156412725658517612233)
                      ·
                        rfl

theorem cell23_2549573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_2549573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549573 prefixEnd_2549573 := by exact prefixLift 2549573
  have htrace : WordTrace (prefixWord ++ tailWord_2549573) baseStart_2549573 baseEnd_2549573 := by
    simpa [prefixWord, tailWord_2549573, baseEnd_2549573] using wordTrace_append hprefix tailTrace_2549573
  have hstable : (prefixWord ++ tailWord_2549573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549573).length < 2 ^ (prefixWord ++ tailWord_2549573).sum := by decide
  have hdescent : baseEnd_2549573 < baseStart_2549573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549574 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2549574 : Nat := 118140960795 + 2549574 * 2 ^ 59
def prefixEnd_2549574 : Nat := 4983230072969 + 3 ^ 40 * 2549574 * 2
def baseEnd_2549574 : Nat := 1309156926206313013699729

theorem tailTrace_2549574 : CollatzResearch.WordTrace tailWord_2549574 prefixEnd_2549574 1309156926206313013699729 := by
  unfold tailWord_2549574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905956352041759544304743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61993735510224203611834517 2905956352041759544304743)
  ·
    refine ⟨4358934528062639316457115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2905956352041759544304743 4358934528062639316457115)
    ·
      refine ⟨6538401792093958974685673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4358934528062639316457115 6538401792093958974685673)
      ·
        refine ⟨4903801344070469231014255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6538401792093958974685673 4903801344070469231014255)
        ·
          refine ⟨7355702016105703846521383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903801344070469231014255 7355702016105703846521383)
          ·
            refine ⟨11033553024158555769782075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355702016105703846521383 11033553024158555769782075)
            ·
              refine ⟨16550329536237833654673113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033553024158555769782075 16550329536237833654673113)
              ·
                refine ⟨12412747152178375241004835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16550329536237833654673113 12412747152178375241004835)
                ·
                  refine ⟨18619120728267562861507253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12412747152178375241004835 18619120728267562861507253)
                  ·
                    refine ⟨1745542568275084018266305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18619120728267562861507253 1745542568275084018266305)
                    ·
                      refine ⟨1309156926206313013699729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745542568275084018266305 1309156926206313013699729)
                      ·
                        rfl

theorem cell23_2549574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2549574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549574 prefixEnd_2549574 := by exact prefixLift 2549574
  have htrace : WordTrace (prefixWord ++ tailWord_2549574) baseStart_2549574 baseEnd_2549574 := by
    simpa [prefixWord, tailWord_2549574, baseEnd_2549574] using wordTrace_append hprefix tailTrace_2549574
  have hstable : (prefixWord ++ tailWord_2549574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549574).length < 2 ^ (prefixWord ++ tailWord_2549574).sum := by decide
  have hdescent : baseEnd_2549574 < baseStart_2549574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549637 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_2549637 : Nat := 118140960795 + 2549637 * 2 ^ 59
def prefixEnd_2549637 : Nat := 4983230072969 + 3 ^ 40 * 2549637 * 2
def baseEnd_2549637 : Nat := 1309189275487546267211939

theorem tailTrace_2549637 : CollatzResearch.WordTrace tailWord_2549637 prefixEnd_2549637 1309189275487546267211939 := by
  unfold tailWord_2549637
  simp only [CollatzResearch.WordTrace]
  refine ⟨92992901064108067177295165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61995267376072044784863443 92992901064108067177295165)
  ·
    refine ⟨34872337899040525191485687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92992901064108067177295165 34872337899040525191485687)
    ·
      refine ⟨52308506848560787787228531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34872337899040525191485687 52308506848560787787228531)
      ·
        refine ⟨78462760272841181680842797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52308506848560787787228531 78462760272841181680842797)
        ·
          refine ⟨29423535102315443130316049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78462760272841181680842797 29423535102315443130316049)
          ·
            refine ⟨22067651326736582347737037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29423535102315443130316049 22067651326736582347737037)
            ·
              refine ⟨8275369247526218380401389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22067651326736582347737037 8275369247526218380401389)
              ·
                refine ⟨3103263467822331892650521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8275369247526218380401389 3103263467822331892650521)
                ·
                  refine ⟨2327447600866748919487891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3103263467822331892650521 2327447600866748919487891)
                  ·
                    refine ⟨3491171401300123379231837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2327447600866748919487891 3491171401300123379231837)
                    ·
                      refine ⟨1309189275487546267211939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491171401300123379231837 1309189275487546267211939)
                      ·
                        rfl

theorem cell23_2549637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_2549637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549637 prefixEnd_2549637 := by exact prefixLift 2549637
  have htrace : WordTrace (prefixWord ++ tailWord_2549637) baseStart_2549637 baseEnd_2549637 := by
    simpa [prefixWord, tailWord_2549637, baseEnd_2549637] using wordTrace_append hprefix tailTrace_2549637
  have hstable : (prefixWord ++ tailWord_2549637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549637).length < 2 ^ (prefixWord ++ tailWord_2549637).sum := by decide
  have hdescent : baseEnd_2549637 < baseStart_2549637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549672 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2549672 : Nat := 118140960795 + 2549672 * 2 ^ 59
def prefixEnd_2549672 : Nat := 4983230072969 + 3 ^ 40 * 2549672 * 2
def baseEnd_2549672 : Nat := 1309207247310453630274279

theorem tailTrace_2549672 : CollatzResearch.WordTrace tailWord_2549672 prefixEnd_2549672 1309207247310453630274279 := by
  unfold tailWord_2549672
  simp only [CollatzResearch.WordTrace]
  refine ⟨46497088809490634077409635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61996118412654178769879513 46497088809490634077409635)
  ·
    refine ⟨69745633214235951116114453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46497088809490634077409635 69745633214235951116114453)
    ·
      refine ⟨3269326556917310208567865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69745633214235951116114453 3269326556917310208567865)
      ·
        refine ⟨2451994917687982656425899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269326556917310208567865 2451994917687982656425899)
        ·
          refine ⟨3677992376531973984638849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451994917687982656425899 3677992376531973984638849)
          ·
            refine ⟨2758494282398980488479137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3677992376531973984638849 2758494282398980488479137)
            ·
              refine ⟨2068870711799235366359353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758494282398980488479137 2068870711799235366359353)
              ·
                refine ⟨1551653033849426524769515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068870711799235366359353 1551653033849426524769515)
                ·
                  refine ⟨2327479550774139787154273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551653033849426524769515 2327479550774139787154273)
                  ·
                    refine ⟨1745609663080604840365705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2327479550774139787154273 1745609663080604840365705)
                    ·
                      refine ⟨1309207247310453630274279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745609663080604840365705 1309207247310453630274279)
                      ·
                        rfl

theorem cell23_2549672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2549672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549672 prefixEnd_2549672 := by exact prefixLift 2549672
  have htrace : WordTrace (prefixWord ++ tailWord_2549672) baseStart_2549672 baseEnd_2549672 := by
    simpa [prefixWord, tailWord_2549672, baseEnd_2549672] using wordTrace_append hprefix tailTrace_2549672
  have hstable : (prefixWord ++ tailWord_2549672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549672).length < 2 ^ (prefixWord ++ tailWord_2549672).sum := by decide
  have hdescent : baseEnd_2549672 < baseStart_2549672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549683 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 7]
def baseStart_2549683 : Nat := 118140960795 + 2549683 * 2 ^ 59
def prefixEnd_2549683 : Nat := 4983230072969 + 3 ^ 40 * 2549683 * 2
def baseEnd_2549683 : Nat := 145468099510850343026303

theorem tailTrace_2549683 : CollatzResearch.WordTrace tailWord_2549683 prefixEnd_2549683 145468099510850343026303 := by
  unfold tailWord_2549683
  simp only [CollatzResearch.WordTrace]
  refine ⟨92994578821941417033469703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61996385881294278022313135 92994578821941417033469703)
  ·
    refine ⟨139491868232912125550204555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92994578821941417033469703 139491868232912125550204555)
    ·
      refine ⟨209237802349368188325306833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139491868232912125550204555 209237802349368188325306833)
      ·
        refine ⟨156928351762026141243980125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209237802349368188325306833 156928351762026141243980125)
        ·
          refine ⟨58848131910759802966492547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156928351762026141243980125 58848131910759802966492547)
          ·
            refine ⟨88272197866139704449738821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58848131910759802966492547 88272197866139704449738821)
            ·
              refine ⟨16551037099901194584326029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88272197866139704449738821 16551037099901194584326029)
              ·
                refine ⟨6206638912462947969122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16551037099901194584326029 6206638912462947969122261)
                ·
                  refine ⟨145468099510850343026303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6206638912462947969122261 145468099510850343026303)
                  ·
                    rfl

theorem cell23_2549683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 7].length) (baseStart_2549683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549683 prefixEnd_2549683 := by exact prefixLift 2549683
  have htrace : WordTrace (prefixWord ++ tailWord_2549683) baseStart_2549683 baseEnd_2549683 := by
    simpa [prefixWord, tailWord_2549683, baseEnd_2549683] using wordTrace_append hprefix tailTrace_2549683
  have hstable : (prefixWord ++ tailWord_2549683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549683).length < 2 ^ (prefixWord ++ tailWord_2549683).sum := by decide
  have hdescent : baseEnd_2549683 < baseStart_2549683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549694 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_2549694 : Nat := 118140960795 + 2549694 * 2 ^ 59
def prefixEnd_2549694 : Nat := 4983230072969 + 3 ^ 40 * 2549694 * 2
def baseEnd_2549694 : Nat := 1309218543884852544199177

theorem tailTrace_2549694 : CollatzResearch.WordTrace tailWord_2549694 prefixEnd_2549694 1309218543884852544199177 := by
  unfold tailWord_2549694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624372503112695739015017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61996653349934377274746757 11624372503112695739015017)
  ·
    refine ⟨8718279377334521804261263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11624372503112695739015017 8718279377334521804261263)
    ·
      refine ⟨13077419066001782706391895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8718279377334521804261263 13077419066001782706391895)
      ·
        refine ⟨19616128599002674059587843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13077419066001782706391895 19616128599002674059587843)
        ·
          refine ⟨29424192898504011089381765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19616128599002674059587843 29424192898504011089381765)
          ·
            refine ⟨5517036168469502079259081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29424192898504011089381765 5517036168469502079259081)
            ·
              refine ⟨4137777126352126559444311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5517036168469502079259081 4137777126352126559444311)
              ·
                refine ⟨6206665689528189839166467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137777126352126559444311 6206665689528189839166467)
                ·
                  refine ⟨9309998534292284758749701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206665689528189839166467 9309998534292284758749701)
                  ·
                    refine ⟨1745624725179803392265569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9309998534292284758749701 1745624725179803392265569)
                    ·
                      refine ⟨1309218543884852544199177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745624725179803392265569 1309218543884852544199177)
                      ·
                        rfl

theorem cell23_2549694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_2549694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549694 prefixEnd_2549694 := by exact prefixLift 2549694
  have htrace : WordTrace (prefixWord ++ tailWord_2549694) baseStart_2549694 baseEnd_2549694 := by
    simpa [prefixWord, tailWord_2549694, baseEnd_2549694] using wordTrace_append hprefix tailTrace_2549694
  have hstable : (prefixWord ++ tailWord_2549694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549694).length < 2 ^ (prefixWord ++ tailWord_2549694).sum := by decide
  have hdescent : baseEnd_2549694 < baseStart_2549694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549710 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2549710 : Nat := 118140960795 + 2549710 * 2 ^ 59
def prefixEnd_2549710 : Nat := 4983230072969 + 3 ^ 40 * 2549710 * 2
def baseEnd_2549710 : Nat := 1309226759575324481599103

theorem tailTrace_2549710 : CollatzResearch.WordTrace tailWord_2549710 prefixEnd_2549710 1309226759575324481599103 := by
  unfold tailWord_2549710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624445449105450080587823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61997042395229067096468389 11624445449105450080587823)
  ·
    refine ⟨17436668173658175120881735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11624445449105450080587823 17436668173658175120881735)
    ·
      refine ⟨26155002260487262681322603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17436668173658175120881735 26155002260487262681322603)
      ·
        refine ⟨39232503390730894021983905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26155002260487262681322603 39232503390730894021983905)
        ·
          refine ⟨29424377543048170516487929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39232503390730894021983905 29424377543048170516487929)
          ·
            refine ⟨22068283157286127887365947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29424377543048170516487929 22068283157286127887365947)
            ·
              refine ⟨33102424735929191831048921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22068283157286127887365947 33102424735929191831048921)
              ·
                refine ⟨24826818551946893873286691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33102424735929191831048921 24826818551946893873286691)
                ·
                  refine ⟨37240227827920340809930037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24826818551946893873286691 37240227827920340809930037)
                  ·
                    refine ⟨3491271358867531950930941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37240227827920340809930037 3491271358867531950930941)
                    ·
                      refine ⟨1309226759575324481599103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491271358867531950930941 1309226759575324481599103)
                      ·
                        rfl

theorem cell23_2549710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2549710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549710 prefixEnd_2549710 := by exact prefixLift 2549710
  have htrace : WordTrace (prefixWord ++ tailWord_2549710) baseStart_2549710 baseEnd_2549710 := by
    simpa [prefixWord, tailWord_2549710, baseEnd_2549710] using wordTrace_append hprefix tailTrace_2549710
  have hstable : (prefixWord ++ tailWord_2549710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549710).length < 2 ^ (prefixWord ++ tailWord_2549710).sum := by decide
  have hdescent : baseEnd_2549710 < baseStart_2549710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549717 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 5]
def baseStart_2549717 : Nat := 118140960795 + 2549717 * 2 ^ 59
def prefixEnd_2549717 : Nat := 4983230072969 + 3 ^ 40 * 2549717 * 2
def baseEnd_2549717 : Nat := 145470039326656217134619

theorem tailTrace_2549717 : CollatzResearch.WordTrace tailWord_2549717 prefixEnd_2549717 145470039326656217134619 := by
  unfold tailWord_2549717
  simp only [CollatzResearch.WordTrace]
  refine ⟨92995818903818240840207405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61997212602545493893471603 92995818903818240840207405)
  ·
    refine ⟨34873432088931840315077777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92995818903818240840207405 34873432088931840315077777)
    ·
      refine ⟨26155074066698880236308333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34873432088931840315077777 26155074066698880236308333)
      ·
        refine ⟨9808152775012080088615625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26155074066698880236308333 9808152775012080088615625)
        ·
          refine ⟨7356114581259060066461719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9808152775012080088615625 7356114581259060066461719)
          ·
            refine ⟨11034171871888590099692579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7356114581259060066461719 11034171871888590099692579)
            ·
              refine ⟨16551257807832885149538869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11034171871888590099692579 16551257807832885149538869)
              ·
                refine ⟨1551680419484332982769269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16551257807832885149538869 1551680419484332982769269)
                ·
                  refine ⟨145470039326656217134619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551680419484332982769269 145470039326656217134619)
                  ·
                    rfl

theorem cell23_2549717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_2549717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549717 prefixEnd_2549717 := by exact prefixLift 2549717
  have htrace : WordTrace (prefixWord ++ tailWord_2549717) baseStart_2549717 baseEnd_2549717 := by
    simpa [prefixWord, tailWord_2549717, baseEnd_2549717] using wordTrace_append hprefix tailTrace_2549717
  have hstable : (prefixWord ++ tailWord_2549717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549717).length < 2 ^ (prefixWord ++ tailWord_2549717).sum := by decide
  have hdescent : baseEnd_2549717 < baseStart_2549717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549760 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_2549760 : Nat := 118140960795 + 2549760 * 2 ^ 59
def prefixEnd_2549760 : Nat := 4983230072969 + 3 ^ 40 * 2549760 * 2
def baseEnd_2549760 : Nat := 436417477869349761991291

theorem tailTrace_2549760 : CollatzResearch.WordTrace tailWord_2549760 prefixEnd_2549760 436417477869349761991291 := by
  unfold tailWord_2549760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498693621331229592011367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61998258161774972789348489 46498693621331229592011367)
  ·
    refine ⟨69748040431996844388017051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46498693621331229592011367 69748040431996844388017051)
    ·
      refine ⟨104622060647995266582025577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69748040431996844388017051 104622060647995266582025577)
      ·
        refine ⟨78466545485996449936519183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104622060647995266582025577 78466545485996449936519183)
        ·
          refine ⟨117699818228994674904778775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78466545485996449936519183 117699818228994674904778775)
          ·
            refine ⟨176549727343492012357168163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117699818228994674904778775 176549727343492012357168163)
            ·
              refine ⟨264824591015238018535752245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176549727343492012357168163 264824591015238018535752245)
              ·
                refine ⟨24827305407678564237726773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264824591015238018535752245 24827305407678564237726773)
                ·
                  refine ⟨2327559881969865397286885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24827305407678564237726773 2327559881969865397286885)
                  ·
                    refine ⟨436417477869349761991291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327559881969865397286885 436417477869349761991291)
                    ·
                      rfl

theorem cell23_2549760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_2549760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549760 prefixEnd_2549760 := by exact prefixLift 2549760
  have htrace : WordTrace (prefixWord ++ tailWord_2549760) baseStart_2549760 baseEnd_2549760 := by
    simpa [prefixWord, tailWord_2549760, baseEnd_2549760] using wordTrace_append hprefix tailTrace_2549760
  have hstable : (prefixWord ++ tailWord_2549760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549760).length < 2 ^ (prefixWord ++ tailWord_2549760).sum := by decide
  have hdescent : baseEnd_2549760 < baseStart_2549760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549850 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_2549850 : Nat := 118140960795 + 2549850 * 2 ^ 59
def prefixEnd_2549850 : Nat := 4983230072969 + 3 ^ 40 * 2549850 * 2
def baseEnd_2549850 : Nat := 436432882288984644616153

theorem tailTrace_2549850 : CollatzResearch.WordTrace tailWord_2549850 prefixEnd_2549850 436432882288984644616153 := by
  unfold tailWord_2549850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23250167453084101138699751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62000446541557603036532669 23250167453084101138699751)
  ·
    refine ⟨34875251179626151708049627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23250167453084101138699751 34875251179626151708049627)
    ·
      refine ⟨52312876769439227562074441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34875251179626151708049627 52312876769439227562074441)
      ·
        refine ⟨39234657577079420671555831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52312876769439227562074441 39234657577079420671555831)
        ·
          refine ⟨58851986365619131007333747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39234657577079420671555831 58851986365619131007333747)
          ·
            refine ⟨88277979548428696511000621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58851986365619131007333747 88277979548428696511000621)
            ·
              refine ⟨33104242330660761191625233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88277979548428696511000621 33104242330660761191625233)
              ·
                refine ⟨24828181747995570893718925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33104242330660761191625233 24828181747995570893718925)
                ·
                  refine ⟨9310568155498339085144597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24828181747995570893718925 9310568155498339085144597)
                  ·
                    refine ⟨436432882288984644616153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9310568155498339085144597 436432882288984644616153)
                    ·
                      rfl

theorem cell23_2549850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_2549850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549850 prefixEnd_2549850 := by exact prefixLift 2549850
  have htrace : WordTrace (prefixWord ++ tailWord_2549850) baseStart_2549850 baseEnd_2549850 := by
    simpa [prefixWord, tailWord_2549850, baseEnd_2549850] using wordTrace_append hprefix tailTrace_2549850
  have hstable : (prefixWord ++ tailWord_2549850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549850).length < 2 ^ (prefixWord ++ tailWord_2549850).sum := by decide
  have hdescent : baseEnd_2549850 < baseStart_2549850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549857 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_2549857 : Nat := 118140960795 + 2549857 * 2 ^ 59
def prefixEnd_2549857 : Nat := 4983230072969 + 3 ^ 40 * 2549857 * 2
def baseEnd_2549857 : Nat := 1309302241231535406460927

theorem tailTrace_2549857 : CollatzResearch.WordTrace tailWord_2549857 prefixEnd_2549857 1309302241231535406460927 := by
  unfold tailWord_2549857
  simp only [CollatzResearch.WordTrace]
  refine ⟨93000925123311044750303825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62000616748874029833535883 93000925123311044750303825)
  ·
    refine ⟨69750693842483283562727869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93000925123311044750303825 69750693842483283562727869)
    ·
      refine ⟨26156510190931231336022951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69750693842483283562727869 26156510190931231336022951)
      ·
        refine ⟨39234765286396847004034427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26156510190931231336022951 39234765286396847004034427)
        ·
          refine ⟨58852147929595270506051641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39234765286396847004034427 58852147929595270506051641)
          ·
            refine ⟨44139110947196452879538731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58852147929595270506051641 44139110947196452879538731)
            ·
              refine ⟨66208666420794679319308097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44139110947196452879538731 66208666420794679319308097)
              ·
                refine ⟨49656499815596009489481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66208666420794679319308097 49656499815596009489481073)
                ·
                  refine ⟨37242374861697007117110805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49656499815596009489481073 37242374861697007117110805)
                  ·
                    refine ⟨1745736321642047208614569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37242374861697007117110805 1745736321642047208614569)
                    ·
                      refine ⟨1309302241231535406460927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745736321642047208614569 1309302241231535406460927)
                      ·
                        rfl

theorem cell23_2549857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_2549857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549857 prefixEnd_2549857 := by exact prefixLift 2549857
  have htrace : WordTrace (prefixWord ++ tailWord_2549857) baseStart_2549857 baseEnd_2549857 := by
    simpa [prefixWord, tailWord_2549857, baseEnd_2549857] using wordTrace_append hprefix tailTrace_2549857
  have hstable : (prefixWord ++ tailWord_2549857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549857).length < 2 ^ (prefixWord ++ tailWord_2549857).sum := by decide
  have hdescent : baseEnd_2549857 < baseStart_2549857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549878 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2549878 : Nat := 118140960795 + 2549878 * 2 ^ 59
def prefixEnd_2549878 : Nat := 4983230072969 + 3 ^ 40 * 2549878 * 2
def baseEnd_2549878 : Nat := 1309313024325279824298331

theorem tailTrace_2549878 : CollatzResearch.WordTrace tailWord_2549878 prefixEnd_2549878 1309313024325279824298331 := by
  unfold tailWord_2549878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5812605691014685333551143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62001127370823310224545525 5812605691014685333551143)
  ·
    refine ⟨8718908536522028000326715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5812605691014685333551143 8718908536522028000326715)
    ·
      refine ⟨13078362804783042000490073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8718908536522028000326715 13078362804783042000490073)
      ·
        refine ⟨9808772103587281500367555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13078362804783042000490073 9808772103587281500367555)
        ·
          refine ⟨14713158155380922250551333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9808772103587281500367555 14713158155380922250551333)
          ·
            refine ⟨2758717154133922921978375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14713158155380922250551333 2758717154133922921978375)
            ·
              refine ⟨4138075731200884382967563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758717154133922921978375 4138075731200884382967563)
              ·
                refine ⟨6207113596801326574451345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138075731200884382967563 6207113596801326574451345)
                ·
                  refine ⟨4655335197600994930838509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207113596801326574451345 4655335197600994930838509)
                  ·
                    refine ⟨1745750699100373099064441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4655335197600994930838509 1745750699100373099064441)
                    ·
                      refine ⟨1309313024325279824298331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745750699100373099064441 1309313024325279824298331)
                      ·
                        rfl

theorem cell23_2549878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2549878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549878 prefixEnd_2549878 := by exact prefixLift 2549878
  have htrace : WordTrace (prefixWord ++ tailWord_2549878) baseStart_2549878 baseEnd_2549878 := by
    simpa [prefixWord, tailWord_2549878, baseEnd_2549878] using wordTrace_append hprefix tailTrace_2549878
  have hstable : (prefixWord ++ tailWord_2549878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549878).length < 2 ^ (prefixWord ++ tailWord_2549878).sum := by decide
  have hdescent : baseEnd_2549878 < baseStart_2549878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549891 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 1, 1, 4]
def baseStart_2549891 : Nat := 118140960795 + 2549891 * 2 ^ 59
def prefixEnd_2549891 : Nat := 4983230072969 + 3 ^ 40 * 2549891 * 2
def baseEnd_2549891 : Nat := 1309319699573788273435771

theorem tailTrace_2549891 : CollatzResearch.WordTrace tailWord_2549891 prefixEnd_2549891 1309319699573788273435771 := by
  unfold tailWord_2549891
  simp only [CollatzResearch.WordTrace]
  refine ⟨93002165205187868557041527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62001443470125245704694351 93002165205187868557041527)
  ·
    refine ⟨139503247807781802835562291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93002165205187868557041527 139503247807781802835562291)
    ·
      refine ⟨209254871711672704253343437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139503247807781802835562291 209254871711672704253343437)
      ·
        refine ⟨78470576891877264095003789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209254871711672704253343437 78470576891877264095003789)
        ·
          refine ⟨29426466334453974035626421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78470576891877264095003789 29426466334453974035626421)
          ·
            refine ⟨2758731218855060065839977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29426466334453974035626421 2758731218855060065839977)
            ·
              refine ⟨2069048414141295049379983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758731218855060065839977 2069048414141295049379983)
              ·
                refine ⟨3103572621211942574069975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069048414141295049379983 3103572621211942574069975)
                ·
                  refine ⟨4655358931817913861104963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103572621211942574069975 4655358931817913861104963)
                  ·
                    refine ⟨6983038397726870791657445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655358931817913861104963 6983038397726870791657445)
                    ·
                      refine ⟨1309319699573788273435771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6983038397726870791657445 1309319699573788273435771)
                      ·
                        rfl

theorem cell23_2549891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_2549891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549891 prefixEnd_2549891 := by exact prefixLift 2549891
  have htrace : WordTrace (prefixWord ++ tailWord_2549891) baseStart_2549891 baseEnd_2549891 := by
    simpa [prefixWord, tailWord_2549891, baseEnd_2549891] using wordTrace_append hprefix tailTrace_2549891
  have hstable : (prefixWord ++ tailWord_2549891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549891).length < 2 ^ (prefixWord ++ tailWord_2549891).sum := by decide
  have hdescent : baseEnd_2549891 < baseStart_2549891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549900 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2549900 : Nat := 118140960795 + 2549900 * 2 ^ 59
def prefixEnd_2549900 : Nat := 4983230072969 + 3 ^ 40 * 2549900 * 2
def baseEnd_2549900 : Nat := 1309324320899678738223229

theorem tailTrace_2549900 : CollatzResearch.WordTrace tailWord_2549900 prefixEnd_2549900 1309324320899678738223229 := by
  unfold tailWord_2549900
  simp only [CollatzResearch.WordTrace]
  refine ⟨46501246731077631547059577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62001662308103508729412769 46501246731077631547059577)
  ·
    refine ⟨34875935048308223660294683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46501246731077631547059577 34875935048308223660294683)
    ·
      refine ⟨52313902572462335490442025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34875935048308223660294683 52313902572462335490442025)
      ·
        refine ⟨39235426929346751617831519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52313902572462335490442025 39235426929346751617831519)
        ·
          refine ⟨58853140394020127426747279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39235426929346751617831519 58853140394020127426747279)
          ·
            refine ⟨88279710591030191140120919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58853140394020127426747279 88279710591030191140120919)
            ·
              refine ⟨132419565886545286710181379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88279710591030191140120919 132419565886545286710181379)
              ·
                refine ⟨198629348829817930065272069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132419565886545286710181379 198629348829817930065272069)
                ·
                  refine ⟨37243002905590861887238513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198629348829817930065272069 37243002905590861887238513)
                  ·
                    refine ⟨27932252179193146415428885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37243002905590861887238513 27932252179193146415428885)
                    ·
                      refine ⟨1309324320899678738223229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27932252179193146415428885 1309324320899678738223229)
                      ·
                        rfl

theorem cell23_2549900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2549900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549900 prefixEnd_2549900 := by exact prefixLift 2549900
  have htrace : WordTrace (prefixWord ++ tailWord_2549900) baseStart_2549900 baseEnd_2549900 := by
    simpa [prefixWord, tailWord_2549900, baseEnd_2549900] using wordTrace_append hprefix tailTrace_2549900
  have hstable : (prefixWord ++ tailWord_2549900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549900).length < 2 ^ (prefixWord ++ tailWord_2549900).sum := by decide
  have hdescent : baseEnd_2549900 < baseStart_2549900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549918 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2549918 : Nat := 118140960795 + 2549918 * 2 ^ 59
def prefixEnd_2549918 : Nat := 4983230072969 + 3 ^ 40 * 2549918 * 2
def baseEnd_2549918 : Nat := 436444521183819889266049

theorem tailTrace_2549918 : CollatzResearch.WordTrace tailWord_2549918 prefixEnd_2549918 436444521183819889266049 := by
  unfold tailWord_2549918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625393747011256521034301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62002099984060034778849605 11625393747011256521034301)
  ·
    refine ⟨4359522655129221195387863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11625393747011256521034301 4359522655129221195387863)
    ·
      refine ⟨6539283982693831793081795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359522655129221195387863 6539283982693831793081795)
      ·
        refine ⟨9808925974040747689622693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539283982693831793081795 9808925974040747689622693)
        ·
          refine ⟨1839173620132640191804255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9808925974040747689622693 1839173620132640191804255)
          ·
            refine ⟨2758760430198960287706383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839173620132640191804255 2758760430198960287706383)
            ·
              refine ⟨4138140645298440431559575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758760430198960287706383 4138140645298440431559575)
              ·
                refine ⟨6207210967947660647339363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138140645298440431559575 6207210967947660647339363)
                ·
                  refine ⟨9310816451921490971009045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6207210967947660647339363 9310816451921490971009045)
                  ·
                    refine ⟨436444521183819889266049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9310816451921490971009045 436444521183819889266049)
                    ·
                      rfl

theorem cell23_2549918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2549918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549918 prefixEnd_2549918 := by exact prefixLift 2549918
  have htrace : WordTrace (prefixWord ++ tailWord_2549918) baseStart_2549918 baseEnd_2549918 := by
    simpa [prefixWord, tailWord_2549918, baseEnd_2549918] using wordTrace_append hprefix tailTrace_2549918
  have hstable : (prefixWord ++ tailWord_2549918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549918).length < 2 ^ (prefixWord ++ tailWord_2549918).sum := by decide
  have hdescent : baseEnd_2549918 < baseStart_2549918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549967 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_2549967 : Nat := 118140960795 + 2549967 * 2 ^ 59
def prefixEnd_2549967 : Nat := 4983230072969 + 3 ^ 40 * 2549967 * 2
def baseEnd_2549967 : Nat := 1309358724103529976085421

theorem tailTrace_2549967 : CollatzResearch.WordTrace tailWord_2549967 prefixEnd_2549967 1309358724103529976085421 := by
  unfold tailWord_2549967
  simp only [CollatzResearch.WordTrace]
  refine ⟨93004937152912533536808155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62003291435275022357872103 93004937152912533536808155)
  ·
    refine ⟨139507405729368800305212233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93004937152912533536808155 139507405729368800305212233)
    ·
      refine ⟨104630554297026600228909175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139507405729368800305212233 104630554297026600228909175)
      ·
        refine ⟨156945831445539900343363763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104630554297026600228909175 156945831445539900343363763)
        ·
          refine ⟨235418747168309850515045645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156945831445539900343363763 235418747168309850515045645)
          ·
            refine ⟨88282030188116193943142117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235418747168309850515045645 88282030188116193943142117)
            ·
              refine ⟨16552880660271786364339147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88282030188116193943142117 16552880660271786364339147)
              ·
                refine ⟨24829320990407679546508721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16552880660271786364339147 24829320990407679546508721)
                ·
                  refine ⟨18621990742805759659881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24829320990407679546508721 18621990742805759659881541)
                  ·
                    refine ⟨3491623264276079936227789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18621990742805759659881541 3491623264276079936227789)
                    ·
                      refine ⟨1309358724103529976085421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491623264276079936227789 1309358724103529976085421)
                      ·
                        rfl

theorem cell23_2549967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_2549967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549967 prefixEnd_2549967 := by exact prefixLift 2549967
  have htrace : WordTrace (prefixWord ++ tailWord_2549967) baseStart_2549967 baseEnd_2549967 := by
    simpa [prefixWord, tailWord_2549967, baseEnd_2549967] using wordTrace_append hprefix tailTrace_2549967
  have hstable : (prefixWord ++ tailWord_2549967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549967).length < 2 ^ (prefixWord ++ tailWord_2549967).sum := by decide
  have hdescent : baseEnd_2549967 < baseStart_2549967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549977 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2549977 : Nat := 118140960795 + 2549977 * 2 ^ 59
def prefixEnd_2549977 : Nat := 4983230072969 + 3 ^ 40 * 2549977 * 2
def baseEnd_2549977 : Nat := 1309363858910074936960375

theorem tailTrace_2549977 : CollatzResearch.WordTrace tailWord_2549977 prefixEnd_2549977 1309363858910074936960375 := by
  unfold tailWord_2549977
  simp only [CollatzResearch.WordTrace]
  refine ⟨93005301882876305244672185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62003534588584203496448123 93005301882876305244672185)
  ·
    refine ⟨69753976412157228933504139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93005301882876305244672185 69753976412157228933504139)
    ·
      refine ⟨104630964618235843400256209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69753976412157228933504139 104630964618235843400256209)
      ·
        refine ⟨78473223463676882550192157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104630964618235843400256209 78473223463676882550192157)
        ·
          refine ⟨29427458798878830956322059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78473223463676882550192157 29427458798878830956322059)
          ·
            refine ⟨44141188198318246434483089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29427458798878830956322059 44141188198318246434483089)
            ·
              refine ⟨33105891148738684825862317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44141188198318246434483089 33105891148738684825862317)
              ·
                refine ⟨12414709180777006809698369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33105891148738684825862317 12414709180777006809698369)
                ·
                  refine ⟨9311031885582755107273777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12414709180777006809698369 9311031885582755107273777)
                  ·
                    refine ⟨6983273914187066330455333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9311031885582755107273777 6983273914187066330455333)
                    ·
                      refine ⟨1309363858910074936960375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6983273914187066330455333 1309363858910074936960375)
                      ·
                        rfl

theorem cell23_2549977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2549977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2549977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2549977 prefixEnd_2549977 := by exact prefixLift 2549977
  have htrace : WordTrace (prefixWord ++ tailWord_2549977) baseStart_2549977 baseEnd_2549977 := by
    simpa [prefixWord, tailWord_2549977, baseEnd_2549977] using wordTrace_append hprefix tailTrace_2549977
  have hstable : (prefixWord ++ tailWord_2549977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549977).length < 2 ^ (prefixWord ++ tailWord_2549977).sum := by decide
  have hdescent : baseEnd_2549977 < baseStart_2549977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550027 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_2550027 : Nat := 118140960795 + 2550027 * 2 ^ 59
def prefixEnd_2550027 : Nat := 4983230072969 + 3 ^ 40 * 2550027 * 2
def baseEnd_2550027 : Nat := 1309389532942799741335145

theorem tailTrace_2550027 : CollatzResearch.WordTrace tailWord_2550027 prefixEnd_2550027 1309389532942799741335145 := by
  unfold tailWord_2550027
  simp only [CollatzResearch.WordTrace]
  refine ⟨93007125532695163783992335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62004750355130109189328223 93007125532695163783992335)
  ·
    refine ⟨139510688299042745675988503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93007125532695163783992335 139510688299042745675988503)
    ·
      refine ⟨209266032448564118513982755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139510688299042745675988503 209266032448564118513982755)
      ·
        refine ⟨313899048672846177770974133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209266032448564118513982755 313899048672846177770974133)
        ·
          refine ⟨29428035813079329166028825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313899048672846177770974133 29428035813079329166028825)
          ·
            refine ⟨22071026859809496874521619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29428035813079329166028825 22071026859809496874521619)
            ·
              refine ⟨33106540289714245311782429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22071026859809496874521619 33106540289714245311782429)
              ·
                refine ⟨12414952608642841991918411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33106540289714245311782429 12414952608642841991918411)
                ·
                  refine ⟨18622428912964262987877617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12414952608642841991918411 18622428912964262987877617)
                  ·
                    refine ⟨13966821684723197240908213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18622428912964262987877617 13966821684723197240908213)
                    ·
                      refine ⟨1309389532942799741335145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13966821684723197240908213 1309389532942799741335145)
                      ·
                        rfl

theorem cell23_2550027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_2550027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550027 prefixEnd_2550027 := by exact prefixLift 2550027
  have htrace : WordTrace (prefixWord ++ tailWord_2550027) baseStart_2550027 baseEnd_2550027 := by
    simpa [prefixWord, tailWord_2550027, baseEnd_2550027] using wordTrace_append hprefix tailTrace_2550027
  have hstable : (prefixWord ++ tailWord_2550027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550027).length < 2 ^ (prefixWord ++ tailWord_2550027).sum := by decide
  have hdescent : baseEnd_2550027 < baseStart_2550027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550067 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_2550067 : Nat := 118140960795 + 2550067 * 2 ^ 59
def prefixEnd_2550067 : Nat := 4983230072969 + 3 ^ 40 * 2550067 * 2
def baseEnd_2550067 : Nat := 1309410072168979584834961

theorem tailTrace_2550067 : CollatzResearch.WordTrace tailWord_2550067 prefixEnd_2550067 1309410072168979584834961 := by
  unfold tailWord_2550067
  simp only [CollatzResearch.WordTrace]
  refine ⟨93008584452550250615448455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62005722968366833743632303 93008584452550250615448455)
  ·
    refine ⟨139512876678825375923172683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93008584452550250615448455 139512876678825375923172683)
    ·
      refine ⟨209269315018238063884759025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139512876678825375923172683 209269315018238063884759025)
      ·
        refine ⟨156951986263678547913569269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209269315018238063884759025 156951986263678547913569269)
        ·
          refine ⟨14714248712219863866897119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156951986263678547913569269 14714248712219863866897119)
          ·
            refine ⟨22071373068329795800345679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14714248712219863866897119 22071373068329795800345679)
            ·
              refine ⟨33107059602494693700518519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22071373068329795800345679 33107059602494693700518519)
              ·
                refine ⟨49660589403742040550777779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33107059602494693700518519 49660589403742040550777779)
                ·
                  refine ⟨74490884105613060826166669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49660589403742040550777779 74490884105613060826166669)
                  ·
                    refine ⟨27934081539604897809812501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74490884105613060826166669 27934081539604897809812501)
                    ·
                      refine ⟨1309410072168979584834961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27934081539604897809812501 1309410072168979584834961)
                      ·
                        rfl

theorem cell23_2550067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_2550067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550067 prefixEnd_2550067 := by exact prefixLift 2550067
  have htrace : WordTrace (prefixWord ++ tailWord_2550067) baseStart_2550067 baseEnd_2550067 := by
    simpa [prefixWord, tailWord_2550067, baseEnd_2550067] using wordTrace_append hprefix tailTrace_2550067
  have hstable : (prefixWord ++ tailWord_2550067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550067).length < 2 ^ (prefixWord ++ tailWord_2550067).sum := by decide
  have hdescent : baseEnd_2550067 < baseStart_2550067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550131 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 2, 3, 2]
def baseStart_2550131 : Nat := 118140960795 + 2550131 * 2 ^ 59
def prefixEnd_2550131 : Nat := 4983230072969 + 3 ^ 40 * 2550131 * 2
def baseEnd_2550131 : Nat := 1309442934930867334434667

theorem tailTrace_2550131 : CollatzResearch.WordTrace tailWord_2550131 prefixEnd_2550131 1309442934930867334434667 := by
  unfold tailWord_2550131
  simp only [CollatzResearch.WordTrace]
  refine ⟨93010918724318389545778247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62007279149545593030518831 93010918724318389545778247)
  ·
    refine ⟨139516378086477584318667371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93010918724318389545778247 139516378086477584318667371)
    ·
      refine ⟨209274567129716376478001057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139516378086477584318667371 209274567129716376478001057)
      ·
        refine ⟨156955925347287282358500793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209274567129716376478001057 156955925347287282358500793)
        ·
          refine ⟨117716944010465461768875595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156955925347287282358500793 117716944010465461768875595)
          ·
            refine ⟨176575416015698192653313393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117716944010465461768875595 176575416015698192653313393)
            ·
              refine ⟨132431562011773644489985045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176575416015698192653313393 132431562011773644489985045)
              ·
                refine ⟨6207729469301889585468049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132431562011773644489985045 6207729469301889585468049)
                ·
                  refine ⟨4655797101976417189101037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207729469301889585468049 4655797101976417189101037)
                  ·
                    refine ⟨1745923913241156445912889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4655797101976417189101037 1745923913241156445912889)
                    ·
                      refine ⟨1309442934930867334434667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745923913241156445912889 1309442934930867334434667)
                      ·
                        rfl

theorem cell23_2550131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3, 2].length) (baseStart_2550131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550131 prefixEnd_2550131 := by exact prefixLift 2550131
  have htrace : WordTrace (prefixWord ++ tailWord_2550131) baseStart_2550131 baseEnd_2550131 := by
    simpa [prefixWord, tailWord_2550131, baseEnd_2550131] using wordTrace_append hprefix tailTrace_2550131
  have hstable : (prefixWord ++ tailWord_2550131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550131).length < 2 ^ (prefixWord ++ tailWord_2550131).sum := by decide
  have hdescent : baseEnd_2550131 < baseStart_2550131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550158 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_2550158 : Nat := 118140960795 + 2550158 * 2 ^ 59
def prefixEnd_2550158 : Nat := 4983230072969 + 3 ^ 40 * 2550158 * 2
def baseEnd_2550158 : Nat := 436485599636179576265681

theorem tailTrace_2550158 : CollatzResearch.WordTrace tailWord_2550158 prefixEnd_2550158 436485599636179576265681 := by
  unfold tailWord_2550158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11626487936902571644626391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62007935663480382104674085 11626487936902571644626391)
  ·
    refine ⟨17439731905353857466939587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11626487936902571644626391 17439731905353857466939587)
    ·
      refine ⟨26159597858030786200409381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17439731905353857466939587 26159597858030786200409381)
      ·
        refine ⟨4904924598380772412576759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26159597858030786200409381 4904924598380772412576759)
        ·
          refine ⟨7357386897571158618865139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904924598380772412576759 7357386897571158618865139)
          ·
            refine ⟨11036080346356737928297709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7357386897571158618865139 11036080346356737928297709)
            ·
              refine ⟨4138530129883776723111641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11036080346356737928297709 4138530129883776723111641)
              ·
                refine ⟨3103897597412832542333731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4138530129883776723111641 3103897597412832542333731)
                ·
                  refine ⟨4655846396119248813500597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103897597412832542333731 4655846396119248813500597)
                  ·
                    refine ⟨436485599636179576265681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4655846396119248813500597 436485599636179576265681)
                    ·
                      rfl

theorem cell23_2550158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_2550158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550158 prefixEnd_2550158 := by exact prefixLift 2550158
  have htrace : WordTrace (prefixWord ++ tailWord_2550158) baseStart_2550158 baseEnd_2550158 := by
    simpa [prefixWord, tailWord_2550158, baseEnd_2550158] using wordTrace_append hprefix tailTrace_2550158
  have hstable : (prefixWord ++ tailWord_2550158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550158).length < 2 ^ (prefixWord ++ tailWord_2550158).sum := by decide
  have hdescent : baseEnd_2550158 < baseStart_2550158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550201 : List Nat := [1, 2, 1, 4, 3, 3, 1, 8]
def baseStart_2550201 : Nat := 118140960795 + 2550201 * 2 ^ 59
def prefixEnd_2550201 : Nat := 4983230072969 + 3 ^ 40 * 2550201 * 2
def baseEnd_2550201 : Nat := 48499217725062298539235

theorem tailTrace_2550201 : CollatzResearch.WordTrace tailWord_2550201 prefixEnd_2550201 48499217725062298539235 := by
  unfold tailWord_2550201
  simp only [CollatzResearch.WordTrace]
  refine ⟨93013471834064791500826457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62008981222709861000550971 93013471834064791500826457)
  ·
    refine ⟨69760103875548593625619843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93013471834064791500826457 69760103875548593625619843)
    ·
      refine ⟨104640155813322890438429765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69760103875548593625619843 104640155813322890438429765)
      ·
        refine ⟨19620029214998041957205581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104640155813322890438429765 19620029214998041957205581)
        ·
          refine ⟨7357510955624265733952093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19620029214998041957205581 7357510955624265733952093)
          ·
            refine ⟨2759066608359099650232035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7357510955624265733952093 2759066608359099650232035)
            ·
              refine ⟨4138599912538649475348053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2759066608359099650232035 4138599912538649475348053)
              ·
                refine ⟨48499217725062298539235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4138599912538649475348053 48499217725062298539235)
                ·
                  rfl

theorem cell23_2550201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 8].length) (baseStart_2550201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550201 prefixEnd_2550201 := by exact prefixLift 2550201
  have htrace : WordTrace (prefixWord ++ tailWord_2550201) baseStart_2550201 baseEnd_2550201 := by
    simpa [prefixWord, tailWord_2550201, baseEnd_2550201] using wordTrace_append hprefix tailTrace_2550201
  have hstable : (prefixWord ++ tailWord_2550201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550201).length < 2 ^ (prefixWord ++ tailWord_2550201).sum := by decide
  have hdescent : baseEnd_2550201 < baseStart_2550201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550211 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 3]
def baseStart_2550211 : Nat := 118140960795 + 2550211 * 2 ^ 59
def prefixEnd_2550211 : Nat := 4983230072969 + 3 ^ 40 * 2550211 * 2
def baseEnd_2550211 : Nat := 1309484013383227021434299

theorem tailTrace_2550211 : CollatzResearch.WordTrace tailWord_2550211 prefixEnd_2550211 1309484013383227021434299 := by
  unfold tailWord_2550211
  simp only [CollatzResearch.WordTrace]
  refine ⟨93013836564028563208690487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62009224376019042139126991 93013836564028563208690487)
  ·
    refine ⟨139520754846042844813035731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93013836564028563208690487 139520754846042844813035731)
    ·
      refine ⟨209281132269064267219553597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139520754846042844813035731 209281132269064267219553597)
      ·
        refine ⟨78480424600899100207332599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209281132269064267219553597 78480424600899100207332599)
        ·
          refine ⟨117720636901348650310998899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78480424600899100207332599 117720636901348650310998899)
          ·
            refine ⟨176580955352022975466498349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117720636901348650310998899 176580955352022975466498349)
            ·
              refine ⟨66217858257008615799936881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176580955352022975466498349 66217858257008615799936881)
              ·
                refine ⟨49663393692756461849952661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66217858257008615799936881 49663393692756461849952661)
                ·
                  refine ⟨2327971579347959149216531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49663393692756461849952661 2327971579347959149216531)
                  ·
                    refine ⟨3491957369021938723824797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2327971579347959149216531 3491957369021938723824797)
                    ·
                      refine ⟨1309484013383227021434299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491957369021938723824797 1309484013383227021434299)
                      ·
                        rfl

theorem cell23_2550211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_2550211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550211 prefixEnd_2550211 := by exact prefixLift 2550211
  have htrace : WordTrace (prefixWord ++ tailWord_2550211) baseStart_2550211 baseEnd_2550211 := by
    simpa [prefixWord, tailWord_2550211, baseEnd_2550211] using wordTrace_append hprefix tailTrace_2550211
  have hstable : (prefixWord ++ tailWord_2550211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550211).length < 2 ^ (prefixWord ++ tailWord_2550211).sum := by decide
  have hdescent : baseEnd_2550211 < baseStart_2550211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550212 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2550212 : Nat := 118140960795 + 2550212 * 2 ^ 59
def prefixEnd_2550212 : Nat := 4983230072969 + 3 ^ 40 * 2550212 * 2
def baseEnd_2550212 : Nat := 1309484526863881517521795

theorem tailTrace_2550212 : CollatzResearch.WordTrace tailWord_2550212 prefixEnd_2550212 1309484526863881517521795 := by
  unfold tailWord_2550212
  simp only [CollatzResearch.WordTrace]
  refine ⟨46506936518512470189738445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62009248691349960252984593 46506936518512470189738445)
  ·
    refine ⟨17440101194442176321151917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46506936518512470189738445 17440101194442176321151917)
    ·
      refine ⟨6540037947915816120431969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17440101194442176321151917 6540037947915816120431969)
      ·
        refine ⟨4905028460936862090323977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6540037947915816120431969 4905028460936862090323977)
        ·
          refine ⟨3678771345702646567742983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4905028460936862090323977 3678771345702646567742983)
          ·
            refine ⟨5518157018553969851614475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678771345702646567742983 5518157018553969851614475)
            ·
              refine ⟨8277235527830954777421713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518157018553969851614475 8277235527830954777421713)
              ·
                refine ⟨6207926645873216083066285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8277235527830954777421713 6207926645873216083066285)
                ·
                  refine ⟨2327972492202456031149857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6207926645873216083066285 2327972492202456031149857)
                  ·
                    refine ⟨1745979369151842023362393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2327972492202456031149857 1745979369151842023362393)
                    ·
                      refine ⟨1309484526863881517521795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1745979369151842023362393 1309484526863881517521795)
                      ·
                        rfl

theorem cell23_2550212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2550212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550212 prefixEnd_2550212 := by exact prefixLift 2550212
  have htrace : WordTrace (prefixWord ++ tailWord_2550212) baseStart_2550212 baseEnd_2550212 := by
    simpa [prefixWord, tailWord_2550212, baseEnd_2550212] using wordTrace_append hprefix tailTrace_2550212
  have hstable : (prefixWord ++ tailWord_2550212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550212).length < 2 ^ (prefixWord ++ tailWord_2550212).sum := by decide
  have hdescent : baseEnd_2550212 < baseStart_2550212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550228 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2550228 : Nat := 118140960795 + 2550228 * 2 ^ 59
def prefixEnd_2550228 : Nat := 4983230072969 + 3 ^ 40 * 2550228 * 2
def baseEnd_2550228 : Nat := 1309492742554353454921721

theorem tailTrace_2550228 : CollatzResearch.WordTrace tailWord_2550228 prefixEnd_2550228 1309492742554353454921721 := by
  unfold tailWord_2550228
  simp only [CollatzResearch.WordTrace]
  refine ⟨46507228302483487556029669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62009637736644650074706225 46507228302483487556029669)
  ·
    refine ⟨8720105306715653916755563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46507228302483487556029669 8720105306715653916755563)
    ·
      refine ⟨13080157960073480875133345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8720105306715653916755563 13080157960073480875133345)
      ·
        refine ⟨9810118470055110656350009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13080157960073480875133345 9810118470055110656350009)
        ·
          refine ⟨7357588852541332992262507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9810118470055110656350009 7357588852541332992262507)
          ·
            refine ⟨11036383278811999488393761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7357588852541332992262507 11036383278811999488393761)
            ·
              refine ⟨8277287459108999616295321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11036383278811999488393761 8277287459108999616295321)
              ·
                refine ⟨6207965594331749712221491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8277287459108999616295321 6207965594331749712221491)
                ·
                  refine ⟨9311948391497624568332237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6207965594331749712221491 9311948391497624568332237)
                  ·
                    refine ⟨3491980646811609213124589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9311948391497624568332237 3491980646811609213124589)
                    ·
                      refine ⟨1309492742554353454921721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3491980646811609213124589 1309492742554353454921721)
                      ·
                        rfl

theorem cell23_2550228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2550228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550228 prefixEnd_2550228 := by exact prefixLift 2550228
  have htrace : WordTrace (prefixWord ++ tailWord_2550228) baseStart_2550228 baseEnd_2550228 := by
    simpa [prefixWord, tailWord_2550228, baseEnd_2550228] using wordTrace_append hprefix tailTrace_2550228
  have hstable : (prefixWord ++ tailWord_2550228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550228).length < 2 ^ (prefixWord ++ tailWord_2550228).sum := by decide
  have hdescent : baseEnd_2550228 < baseStart_2550228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550245 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2550245 : Nat := 118140960795 + 2550245 * 2 ^ 59
def prefixEnd_2550245 : Nat := 4983230072969 + 3 ^ 40 * 2550245 * 2
def baseEnd_2550245 : Nat := 1309501471725479888409143

theorem tailTrace_2550245 : CollatzResearch.WordTrace tailWord_2550245 prefixEnd_2550245 1309501471725479888409143 := by
  unfold tailWord_2550245
  simp only [CollatzResearch.WordTrace]
  refine ⟨93015076645905387015428189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62010051097270258010285459 93015076645905387015428189)
  ·
    refine ⟨34880653742214520130785571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93015076645905387015428189 34880653742214520130785571)
    ·
      refine ⟨52320980613321780196178357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34880653742214520130785571 52320980613321780196178357)
      ·
        refine ⟨4905091932498916893391721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52320980613321780196178357 4905091932498916893391721)
        ·
          refine ⟨3678818949374187670043791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4905091932498916893391721 3678818949374187670043791)
          ·
            refine ⟨5518228424061281505065687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678818949374187670043791 5518228424061281505065687)
            ·
              refine ⟨8277342636091922257598531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518228424061281505065687 8277342636091922257598531)
              ·
                refine ⟨12416013954137883386397797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8277342636091922257598531 12416013954137883386397797)
                ·
                  refine ⟨2328002616400853134949587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12416013954137883386397797 2328002616400853134949587)
                  ·
                    refine ⟨3492003924601279702424381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328002616400853134949587 3492003924601279702424381)
                    ·
                      refine ⟨1309501471725479888409143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492003924601279702424381 1309501471725479888409143)
                      ·
                        rfl

theorem cell23_2550245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2550245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550245 prefixEnd_2550245 := by exact prefixLift 2550245
  have htrace : WordTrace (prefixWord ++ tailWord_2550245) baseStart_2550245 baseEnd_2550245 := by
    simpa [prefixWord, tailWord_2550245, baseEnd_2550245] using wordTrace_append hprefix tailTrace_2550245
  have hstable : (prefixWord ++ tailWord_2550245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550245).length < 2 ^ (prefixWord ++ tailWord_2550245).sum := by decide
  have hdescent : baseEnd_2550245 < baseStart_2550245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550262 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2550262 : Nat := 118140960795 + 2550262 * 2 ^ 59
def prefixEnd_2550262 : Nat := 4983230072969 + 3 ^ 40 * 2550262 * 2
def baseEnd_2550262 : Nat := 1309510200896606321896565

theorem tailTrace_2550262 : CollatzResearch.WordTrace tailWord_2550262 prefixEnd_2550262 1309510200896606321896565 := by
  unfold tailWord_2550262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813481042927737432424815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62010464457895865945864693 5813481042927737432424815)
  ·
    refine ⟨8720221564391606148637223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5813481042927737432424815 8720221564391606148637223)
    ·
      refine ⟨13080332346587409222955835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8720221564391606148637223 13080332346587409222955835)
      ·
        refine ⟨19620498519881113834433753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13080332346587409222955835 19620498519881113834433753)
        ·
          refine ⟨14715373889910835375825315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19620498519881113834433753 14715373889910835375825315)
          ·
            refine ⟨22073060834866253063737973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14715373889910835375825315 22073060834866253063737973)
            ·
              refine ⟨2069349453268711224725435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22073060834866253063737973 2069349453268711224725435)
              ·
                refine ⟨3104024179903066837088153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069349453268711224725435 3104024179903066837088153)
                ·
                  refine ⟨2328018134927300127816115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3104024179903066837088153 2328018134927300127816115)
                  ·
                    refine ⟨3492027202390950191724173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328018134927300127816115 3492027202390950191724173)
                    ·
                      refine ⟨1309510200896606321896565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492027202390950191724173 1309510200896606321896565)
                      ·
                        rfl

theorem cell23_2550262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2550262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550262 prefixEnd_2550262 := by exact prefixLift 2550262
  have htrace : WordTrace (prefixWord ++ tailWord_2550262) baseStart_2550262 baseEnd_2550262 := by
    simpa [prefixWord, tailWord_2550262, baseEnd_2550262] using wordTrace_append hprefix tailTrace_2550262
  have hstable : (prefixWord ++ tailWord_2550262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550262).length < 2 ^ (prefixWord ++ tailWord_2550262).sum := by decide
  have hdescent : baseEnd_2550262 < baseStart_2550262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550361 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_2550361 : Nat := 118140960795 + 2550361 * 2 ^ 59
def prefixEnd_2550361 : Nat := 4983230072969 + 3 ^ 40 * 2550361 * 2
def baseEnd_2550361 : Nat := 1309561035481401434558609

theorem tailTrace_2550361 : CollatzResearch.WordTrace tailWord_2550361 prefixEnd_2550361 1309561035481401434558609 := by
  unfold tailWord_2550361
  simp only [CollatzResearch.WordTrace]
  refine ⟨93019307513485138826650937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62012871675656759217767291 93019307513485138826650937)
  ·
    refine ⟨69764480635113854119988203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93019307513485138826650937 69764480635113854119988203)
    ·
      refine ⟨104646720952670781179982305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69764480635113854119988203 104646720952670781179982305)
      ·
        refine ⟨78485040714503085884986729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104646720952670781179982305 78485040714503085884986729)
        ·
          refine ⟨58863780535877314413740047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78485040714503085884986729 58863780535877314413740047)
          ·
            refine ⟨88295670803815971620610071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58863780535877314413740047 88295670803815971620610071)
            ·
              refine ⟨132443506205723957430915107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88295670803815971620610071 132443506205723957430915107)
              ·
                refine ⟨198665259308585936146372661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132443506205723957430915107 198665259308585936146372661)
                ·
                  refine ⟨18624868060179931513722437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198665259308585936146372661 18624868060179931513722437)
                  ·
                    refine ⟨3492162761283737158822957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18624868060179931513722437 3492162761283737158822957)
                    ·
                      refine ⟨1309561035481401434558609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492162761283737158822957 1309561035481401434558609)
                      ·
                        rfl

theorem cell23_2550361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_2550361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550361 prefixEnd_2550361 := by exact prefixLift 2550361
  have htrace : WordTrace (prefixWord ++ tailWord_2550361) baseStart_2550361 baseEnd_2550361 := by
    simpa [prefixWord, tailWord_2550361, baseEnd_2550361] using wordTrace_append hprefix tailTrace_2550361
  have hstable : (prefixWord ++ tailWord_2550361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550361).length < 2 ^ (prefixWord ++ tailWord_2550361).sum := by decide
  have hdescent : baseEnd_2550361 < baseStart_2550361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550378 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2550378 : Nat := 118140960795 + 2550378 * 2 ^ 59
def prefixEnd_2550378 : Nat := 4983230072969 + 3 ^ 40 * 2550378 * 2
def baseEnd_2550378 : Nat := 1309569764652527868046031

theorem tailTrace_2550378 : CollatzResearch.WordTrace tailWord_2550378 prefixEnd_2550378 1309569764652527868046031 := by
  unfold tailWord_2550378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23254981888605887682504947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62013285036282367153346525 23254981888605887682504947)
  ·
    refine ⟨34882472832908831523757421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23254981888605887682504947 34882472832908831523757421)
    ·
      refine ⟨13080927312340811821409033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34882472832908831523757421 13080927312340811821409033)
      ·
        refine ⟨9810695484255608866056775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13080927312340811821409033 9810695484255608866056775)
        ·
          refine ⟨14716043226383413299085163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9810695484255608866056775 14716043226383413299085163)
          ·
            refine ⟨22074064839575119948627745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14716043226383413299085163 22074064839575119948627745)
            ·
              refine ⟨16555548629681339961470809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22074064839575119948627745 16555548629681339961470809)
              ·
                refine ⟨12416661472261004971103107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16555548629681339961470809 12416661472261004971103107)
                ·
                  refine ⟨18624992208391507456654661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12416661472261004971103107 18624992208391507456654661)
                  ·
                    refine ⟨3492186039073407648122749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18624992208391507456654661 3492186039073407648122749)
                    ·
                      refine ⟨1309569764652527868046031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492186039073407648122749 1309569764652527868046031)
                      ·
                        rfl

theorem cell23_2550378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2550378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550378 prefixEnd_2550378 := by exact prefixLift 2550378
  have htrace : WordTrace (prefixWord ++ tailWord_2550378) baseStart_2550378 baseEnd_2550378 := by
    simpa [prefixWord, tailWord_2550378, baseEnd_2550378] using wordTrace_append hprefix tailTrace_2550378
  have hstable : (prefixWord ++ tailWord_2550378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550378).length < 2 ^ (prefixWord ++ tailWord_2550378).sum := by decide
  have hdescent : baseEnd_2550378 < baseStart_2550378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550411 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 5, 5]
def baseStart_2550411 : Nat := 118140960795 + 2550411 * 2 ^ 59
def prefixEnd_2550411 : Nat := 4983230072969 + 3 ^ 40 * 2550411 * 2
def baseEnd_2550411 : Nat := 436528903171375412977793

theorem tailTrace_2550411 : CollatzResearch.WordTrace tailWord_2550411 prefixEnd_2550411 436528903171375412977793 := by
  unfold tailWord_2550411
  simp only [CollatzResearch.WordTrace]
  refine ⟨93021131163303997365971087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62014087442202664910647391 93021131163303997365971087)
  ·
    refine ⟨139531696744955996048956631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93021131163303997365971087 139531696744955996048956631)
    ·
      refine ⟨209297545117433994073434947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139531696744955996048956631 209297545117433994073434947)
      ·
        refine ⟨313946317676150991110152421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209297545117433994073434947 313946317676150991110152421)
        ·
          refine ⟨58864934564278310833153579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313946317676150991110152421 58864934564278310833153579)
          ·
            refine ⟨88297401846417466249730369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58864934564278310833153579 88297401846417466249730369)
            ·
              refine ⟨66223051384813099687297777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88297401846417466249730369 66223051384813099687297777)
              ·
                refine ⟨49667288538609824765473333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66223051384813099687297777 49667288538609824765473333)
                ·
                  refine ⟨4656308300494671071763125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49667288538609824765473333 4656308300494671071763125)
                  ·
                    refine ⟨436528903171375412977793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4656308300494671071763125 436528903171375412977793)
                    ·
                      rfl

theorem cell23_2550411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 5].length) (baseStart_2550411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550411 prefixEnd_2550411 := by exact prefixLift 2550411
  have htrace : WordTrace (prefixWord ++ tailWord_2550411) baseStart_2550411 baseEnd_2550411 := by
    simpa [prefixWord, tailWord_2550411, baseEnd_2550411] using wordTrace_append hprefix tailTrace_2550411
  have hstable : (prefixWord ++ tailWord_2550411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550411).length < 2 ^ (prefixWord ++ tailWord_2550411).sum := by decide
  have hdescent : baseEnd_2550411 < baseStart_2550411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550418 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2550418 : Nat := 118140960795 + 2550418 * 2 ^ 59
def prefixEnd_2550418 : Nat := 4983230072969 + 3 ^ 40 * 2550418 * 2
def baseEnd_2550418 : Nat := 1309590303878707711545847

theorem tailTrace_2550418 : CollatzResearch.WordTrace tailWord_2550418 prefixEnd_2550418 1309590303878707711545847 := by
  unfold tailWord_2550418
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255346618569659390368977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62014257649519091707650605 23255346618569659390368977)
  ·
    refine ⟨17441509963927244542776733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23255346618569659390368977 17441509963927244542776733)
    ·
      refine ⟨6540566236472716703541275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17441509963927244542776733 6540566236472716703541275)
      ·
        refine ⟨9810849354709075055311913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540566236472716703541275 9810849354709075055311913)
        ·
          refine ⟨7358137016031806291483935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9810849354709075055311913 7358137016031806291483935)
          ·
            refine ⟨11037205524047709437225903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358137016031806291483935 11037205524047709437225903)
            ·
              refine ⟨16555808286071564155838855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037205524047709437225903 16555808286071564155838855)
              ·
                refine ⟨24833712429107346233758283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16555808286071564155838855 24833712429107346233758283)
                ·
                  refine ⟨37250568643661019350637425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24833712429107346233758283 37250568643661019350637425)
                  ·
                    refine ⟨27937926482745764512978069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37250568643661019350637425 27937926482745764512978069)
                    ·
                      refine ⟨1309590303878707711545847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27937926482745764512978069 1309590303878707711545847)
                      ·
                        rfl

theorem cell23_2550418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2550418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550418 prefixEnd_2550418 := by exact prefixLift 2550418
  have htrace : WordTrace (prefixWord ++ tailWord_2550418) baseStart_2550418 baseEnd_2550418 := by
    simpa [prefixWord, tailWord_2550418, baseEnd_2550418] using wordTrace_append hprefix tailTrace_2550418
  have hstable : (prefixWord ++ tailWord_2550418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550418).length < 2 ^ (prefixWord ++ tailWord_2550418).sum := by decide
  have hdescent : baseEnd_2550418 < baseStart_2550418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550425 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 3]
def baseStart_2550425 : Nat := 118140960795 + 2550425 * 2 ^ 59
def prefixEnd_2550425 : Nat := 4983230072969 + 3 ^ 40 * 2550425 * 2
def baseEnd_2550425 : Nat := 1309593898243289184158315

theorem tailTrace_2550425 : CollatzResearch.WordTrace tailWord_2550425 prefixEnd_2550425 1309593898243289184158315 := by
  unfold tailWord_2550425
  simp only [CollatzResearch.WordTrace]
  refine ⟨93021641785253277756980729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62014427856835518504653819 93021641785253277756980729)
  ·
    refine ⟨69766231338939958317735547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93021641785253277756980729 69766231338939958317735547)
    ·
      refine ⟨104649347008409937476603321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69766231338939958317735547 104649347008409937476603321)
      ·
        refine ⟨78487010256307453107452491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104649347008409937476603321 78487010256307453107452491)
        ·
          refine ⟨117730515384461179661178737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78487010256307453107452491 117730515384461179661178737)
          ·
            refine ⟨88297886538345884745884053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117730515384461179661178737 88297886538345884745884053)
            ·
              refine ⟨4138963431484963347463315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88297886538345884745884053 4138963431484963347463315)
              ·
                refine ⟨6208445147227445021194973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138963431484963347463315 6208445147227445021194973)
                ·
                  refine ⟨2328166930210291882948115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6208445147227445021194973 2328166930210291882948115)
                  ·
                    refine ⟨3492250395315437824422173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328166930210291882948115 3492250395315437824422173)
                    ·
                      refine ⟨1309593898243289184158315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492250395315437824422173 1309593898243289184158315)
                      ·
                        rfl

theorem cell23_2550425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_2550425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550425 prefixEnd_2550425 := by exact prefixLift 2550425
  have htrace : WordTrace (prefixWord ++ tailWord_2550425) baseStart_2550425 baseEnd_2550425 := by
    simpa [prefixWord, tailWord_2550425, baseEnd_2550425] using wordTrace_append hprefix tailTrace_2550425
  have hstable : (prefixWord ++ tailWord_2550425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550425).length < 2 ^ (prefixWord ++ tailWord_2550425).sum := by decide
  have hdescent : baseEnd_2550425 < baseStart_2550425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550445 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2550445 : Nat := 118140960795 + 2550445 * 2 ^ 59
def prefixEnd_2550445 : Nat := 4983230072969 + 3 ^ 40 * 2550445 * 2
def baseEnd_2550445 : Nat := 436534722618793035302741

theorem tailTrace_2550445 : CollatzResearch.WordTrace tailWord_2550445 prefixEnd_2550445 436534722618793035302741 := by
  unfold tailWord_2550445
  simp only [CollatzResearch.WordTrace]
  refine ⟨93022371245180821172708789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62014914163453880781805859 93022371245180821172708789)
  ·
    refine ⟨8720847304235701984941449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93022371245180821172708789 8720847304235701984941449)
    ·
      refine ⟨6540635478176776488706087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8720847304235701984941449 6540635478176776488706087)
      ·
        refine ⟨9810953217265164733059131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540635478176776488706087 9810953217265164733059131)
        ·
          refine ⟨14716429825897747099588697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9810953217265164733059131 14716429825897747099588697)
          ·
            refine ⟨11037322369423310324691523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14716429825897747099588697 11037322369423310324691523)
            ·
              refine ⟨16555983554134965487037285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037322369423310324691523 16555983554134965487037285)
              ·
                refine ⟨3104246916400306028819491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16555983554134965487037285 3104246916400306028819491)
                ·
                  refine ⟨4656370374600459043229237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104246916400306028819491 4656370374600459043229237)
                  ·
                    refine ⟨436534722618793035302741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4656370374600459043229237 436534722618793035302741)
                    ·
                      rfl

theorem cell23_2550445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2550445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550445 prefixEnd_2550445 := by exact prefixLift 2550445
  have htrace : WordTrace (prefixWord ++ tailWord_2550445) baseStart_2550445 baseEnd_2550445 := by
    simpa [prefixWord, tailWord_2550445, baseEnd_2550445] using wordTrace_append hprefix tailTrace_2550445
  have hstable : (prefixWord ++ tailWord_2550445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550445).length < 2 ^ (prefixWord ++ tailWord_2550445).sum := by decide
  have hdescent : baseEnd_2550445 < baseStart_2550445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550448 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2]
def baseStart_2550448 : Nat := 118140960795 + 2550448 * 2 ^ 59
def prefixEnd_2550448 : Nat := 4983230072969 + 3 ^ 40 * 2550448 * 2
def baseEnd_2550448 : Nat := 1309605708298342594170709

theorem tailTrace_2550448 : CollatzResearch.WordTrace tailWord_2550448 prefixEnd_2550448 1309605708298342594170709 := by
  unfold tailWord_2550448
  simp only [CollatzResearch.WordTrace]
  refine ⟨46511240332084976342533999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62014987109446635123378665 46511240332084976342533999)
  ·
    refine ⟨69766860498127464513800999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46511240332084976342533999 69766860498127464513800999)
    ·
      refine ⟨104650290747191196770701499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69766860498127464513800999 104650290747191196770701499)
      ·
        refine ⟨156975436120786795156052249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104650290747191196770701499 156975436120786795156052249)
        ·
          refine ⟨117731577090590096367039187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156975436120786795156052249 117731577090590096367039187)
          ·
            refine ⟨176597365635885144550558781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117731577090590096367039187 176597365635885144550558781)
            ·
              refine ⟨66224012113456929206459543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176597365635885144550558781 66224012113456929206459543)
              ·
                refine ⟨99336018170185393809689315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66224012113456929206459543 99336018170185393809689315)
                ·
                  refine ⟨149004027255278090714533973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99336018170185393809689315 149004027255278090714533973)
                  ·
                    refine ⟨1746140944397790125560945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 149004027255278090714533973 1746140944397790125560945)
                    ·
                      refine ⟨1309605708298342594170709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746140944397790125560945 1309605708298342594170709)
                      ·
                        rfl

theorem cell23_2550448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2].length) (baseStart_2550448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550448 prefixEnd_2550448 := by exact prefixLift 2550448
  have htrace : WordTrace (prefixWord ++ tailWord_2550448) baseStart_2550448 baseEnd_2550448 := by
    simpa [prefixWord, tailWord_2550448, baseEnd_2550448] using wordTrace_append hprefix tailTrace_2550448
  have hstable : (prefixWord ++ tailWord_2550448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550448).length < 2 ^ (prefixWord ++ tailWord_2550448).sum := by decide
  have hdescent : baseEnd_2550448 < baseStart_2550448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550458 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_2550458 : Nat := 118140960795 + 2550458 * 2 ^ 59
def prefixEnd_2550458 : Nat := 4983230072969 + 3 ^ 40 * 2550458 * 2
def baseEnd_2550458 : Nat := 436536947701629185015221

theorem tailTrace_2550458 : CollatzResearch.WordTrace tailWord_2550458 prefixEnd_2550458 436536947701629185015221 := by
  unfold tailWord_2550458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255711348533431098233007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62015230262755816261954685 23255711348533431098233007)
  ·
    refine ⟨34883567022800146647349511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23255711348533431098233007 34883567022800146647349511)
    ·
      refine ⟨52325350534200219971024267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34883567022800146647349511 52325350534200219971024267)
      ·
        refine ⟨78488025801300329956536401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52325350534200219971024267 78488025801300329956536401)
        ·
          refine ⟨58866019350975247467402301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78488025801300329956536401 58866019350975247467402301)
          ·
            refine ⟨22074757256615717800275863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58866019350975247467402301 22074757256615717800275863)
            ·
              refine ⟨33112135884923576700413795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22074757256615717800275863 33112135884923576700413795)
              ·
                refine ⟨49668203827385365050620693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33112135884923576700413795 49668203827385365050620693)
                ·
                  refine ⟨2328197054408688986747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49668203827385365050620693 2328197054408688986747845)
                  ·
                    refine ⟨436536947701629185015221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2328197054408688986747845 436536947701629185015221)
                    ·
                      rfl

theorem cell23_2550458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_2550458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550458 prefixEnd_2550458 := by exact prefixLift 2550458
  have htrace : WordTrace (prefixWord ++ tailWord_2550458) baseStart_2550458 baseEnd_2550458 := by
    simpa [prefixWord, tailWord_2550458, baseEnd_2550458] using wordTrace_append hprefix tailTrace_2550458
  have hstable : (prefixWord ++ tailWord_2550458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550458).length < 2 ^ (prefixWord ++ tailWord_2550458).sum := by decide
  have hdescent : baseEnd_2550458 < baseStart_2550458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550476 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2550476 : Nat := 118140960795 + 2550476 * 2 ^ 59
def prefixEnd_2550476 : Nat := 4983230072969 + 3 ^ 40 * 2550476 * 2
def baseEnd_2550476 : Nat := 1309620085756668484620581

theorem tailTrace_2550476 : CollatzResearch.WordTrace tailWord_2550476 prefixEnd_2550476 1309620085756668484620581 := by
  unfold tailWord_2550476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46511750954034256733543641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62015667938712342311391521 46511750954034256733543641)
  ·
    refine ⟨34883813215525692550157731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46511750954034256733543641 34883813215525692550157731)
    ·
      refine ⟨52325719823288538825236597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34883813215525692550157731 52325719823288538825236597)
      ·
        refine ⟨4905536233433300514865931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52325719823288538825236597 4905536233433300514865931)
        ·
          refine ⟨7358304350149950772298897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905536233433300514865931 7358304350149950772298897)
          ·
            refine ⟨5518728262612463079224173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358304350149950772298897 5518728262612463079224173)
            ·
              refine ⟨2069523098479673654709065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5518728262612463079224173 2069523098479673654709065)
              ·
                refine ⟨1552142323859755241031799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069523098479673654709065 1552142323859755241031799)
                ·
                  refine ⟨2328213485789632861547699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552142323859755241031799 2328213485789632861547699)
                  ·
                    refine ⟨3492320228684449292321549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328213485789632861547699 3492320228684449292321549)
                    ·
                      refine ⟨1309620085756668484620581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492320228684449292321549 1309620085756668484620581)
                      ·
                        rfl

theorem cell23_2550476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2550476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550476 prefixEnd_2550476 := by exact prefixLift 2550476
  have htrace : WordTrace (prefixWord ++ tailWord_2550476) baseStart_2550476 baseEnd_2550476 := by
    simpa [prefixWord, tailWord_2550476, baseEnd_2550476] using wordTrace_append hprefix tailTrace_2550476
  have hstable : (prefixWord ++ tailWord_2550476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550476).length < 2 ^ (prefixWord ++ tailWord_2550476).sum := by decide
  have hdescent : baseEnd_2550476 < baseStart_2550476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550478 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2550478 : Nat := 118140960795 + 2550478 * 2 ^ 59
def prefixEnd_2550478 : Nat := 4983230072969 + 3 ^ 40 * 2550478 * 2
def baseEnd_2550478 : Nat := 1309621112717977476795571

theorem tailTrace_2550478 : CollatzResearch.WordTrace tailWord_2550478 prefixEnd_2550478 1309621112717977476795571 := by
  unfold tailWord_2550478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627946856757658476082511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62015716569374178539106725 11627946856757658476082511)
  ·
    refine ⟨17441920285136487714123767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11627946856757658476082511 17441920285136487714123767)
    ·
      refine ⟨26162880427704731571185651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17441920285136487714123767 26162880427704731571185651)
      ·
        refine ⟨39244320641557097356778477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26162880427704731571185651 39244320641557097356778477)
        ·
          refine ⟨14716620240583911508791929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39244320641557097356778477 14716620240583911508791929)
          ·
            refine ⟨11037465180437933631593947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14716620240583911508791929 11037465180437933631593947)
            ·
              refine ⟨16556197770656900447390921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037465180437933631593947 16556197770656900447390921)
              ·
                refine ⟨12417148327992675335543191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16556197770656900447390921 12417148327992675335543191)
                ·
                  refine ⟨18625722491989013003314787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12417148327992675335543191 18625722491989013003314787)
                  ·
                    refine ⟨27938583737983519504972181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18625722491989013003314787 27938583737983519504972181)
                    ·
                      refine ⟨1309621112717977476795571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27938583737983519504972181 1309621112717977476795571)
                      ·
                        rfl

theorem cell23_2550478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2550478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550478 prefixEnd_2550478 := by exact prefixLift 2550478
  have htrace : WordTrace (prefixWord ++ tailWord_2550478) baseStart_2550478 baseEnd_2550478 := by
    simpa [prefixWord, tailWord_2550478, baseEnd_2550478] using wordTrace_append hprefix tailTrace_2550478
  have hstable : (prefixWord ++ tailWord_2550478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550478).length < 2 ^ (prefixWord ++ tailWord_2550478).sum := by decide
  have hdescent : baseEnd_2550478 < baseStart_2550478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550488 : List Nat := [2, 1, 2, 2, 3, 3, 2, 8]
def baseStart_2550488 : Nat := 118140960795 + 2550488 * 2 ^ 59
def prefixEnd_2550488 : Nat := 4983230072969 + 3 ^ 40 * 2550488 * 2
def baseEnd_2550488 : Nat := 48504675834241571765575

theorem tailTrace_2550488 : CollatzResearch.WordTrace tailWord_2550488 prefixEnd_2550488 48504675834241571765575 := by
  unfold tailWord_2550488
  simp only [CollatzResearch.WordTrace]
  refine ⟨46511969792012519758262059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62015959722683359677682745 46511969792012519758262059)
  ·
    refine ⟨69767954688018779637393089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46511969792012519758262059 69767954688018779637393089)
    ·
      refine ⟨52325966016014084728044817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69767954688018779637393089 52325966016014084728044817)
      ·
        refine ⟨39244474512010563546033613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52325966016014084728044817 39244474512010563546033613)
        ·
          refine ⟨14716677942003961329762605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39244474512010563546033613 14716677942003961329762605)
          ·
            refine ⟨5518754228251485498660977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14716677942003961329762605 5518754228251485498660977)
            ·
              refine ⟨4139065671188614123995733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5518754228251485498660977 4139065671188614123995733)
              ·
                refine ⟨48504675834241571765575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4139065671188614123995733 48504675834241571765575)
                ·
                  rfl

theorem cell23_2550488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 8].length) (baseStart_2550488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550488 prefixEnd_2550488 := by exact prefixLift 2550488
  have htrace : WordTrace (prefixWord ++ tailWord_2550488) baseStart_2550488 baseEnd_2550488 := by
    simpa [prefixWord, tailWord_2550488, baseEnd_2550488] using wordTrace_append hprefix tailTrace_2550488
  have hstable : (prefixWord ++ tailWord_2550488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550488).length < 2 ^ (prefixWord ++ tailWord_2550488).sum := by decide
  have hdescent : baseEnd_2550488 < baseStart_2550488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550538 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2550538 : Nat := 118140960795 + 2550538 * 2 ^ 59
def prefixEnd_2550538 : Nat := 4983230072969 + 3 ^ 40 * 2550538 * 2
def baseEnd_2550538 : Nat := 1309651921557247242045295

theorem tailTrace_2550538 : CollatzResearch.WordTrace tailWord_2550538 prefixEnd_2550538 1309651921557247242045295 := by
  unfold tailWord_2550538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256440808460974513961067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62017175489229265370562845 23256440808460974513961067)
  ·
    refine ⟨34884661212691461770941601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256440808460974513961067 34884661212691461770941601)
    ·
      refine ⟨26163495909518596328206201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34884661212691461770941601 26163495909518596328206201)
      ·
        refine ⟨19622621932138947246154651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26163495909518596328206201 19622621932138947246154651)
        ·
          refine ⟨29433932898208420869231977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19622621932138947246154651 29433932898208420869231977)
          ·
            refine ⟨22075449673656315651923983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29433932898208420869231977 22075449673656315651923983)
            ·
              refine ⟨33113174510484473477885975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22075449673656315651923983 33113174510484473477885975)
              ·
                refine ⟨49669761765726710216828963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33113174510484473477885975 49669761765726710216828963)
                ·
                  refine ⟨74504642648590065325243445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49669761765726710216828963 74504642648590065325243445)
                  ·
                    refine ⟨6984810248305318624241573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74504642648590065325243445 6984810248305318624241573)
                    ·
                      refine ⟨1309651921557247242045295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6984810248305318624241573 1309651921557247242045295)
                      ·
                        rfl

theorem cell23_2550538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2550538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550538 prefixEnd_2550538 := by exact prefixLift 2550538
  have htrace : WordTrace (prefixWord ++ tailWord_2550538) baseStart_2550538 baseEnd_2550538 := by
    simpa [prefixWord, tailWord_2550538, baseEnd_2550538] using wordTrace_append hprefix tailTrace_2550538
  have hstable : (prefixWord ++ tailWord_2550538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550538).length < 2 ^ (prefixWord ++ tailWord_2550538).sum := by decide
  have hdescent : baseEnd_2550538 < baseStart_2550538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550572 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_2550572 : Nat := 118140960795 + 2550572 * 2 ^ 59
def prefixEnd_2550572 : Nat := 4983230072969 + 3 ^ 40 * 2550572 * 2
def baseEnd_2550572 : Nat := 1309669379899500109020139

theorem tailTrace_2550572 : CollatzResearch.WordTrace tailWord_2550572 prefixEnd_2550572 1309669379899500109020139 := by
  unfold tailWord_2550572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46513501657860360931290985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62018002210480481241721313 46513501657860360931290985)
  ·
    refine ⟨34885126243395270698468239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46513501657860360931290985 34885126243395270698468239)
    ·
      refine ⟨52327689365092906047702359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34885126243395270698468239 52327689365092906047702359)
      ·
        refine ⟨78491534047639359071553539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52327689365092906047702359 78491534047639359071553539)
        ·
          refine ⟨117737301071459038607330309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78491534047639359071553539 117737301071459038607330309)
          ·
            refine ⟨22075743950898569738874433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117737301071459038607330309 22075743950898569738874433)
            ·
              refine ⟨16556807963173927304155825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22075743950898569738874433 16556807963173927304155825)
              ·
                refine ⟨12417605972380445478116869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16556807963173927304155825 12417605972380445478116869)
                ·
                  refine ⟨2328301119821333527146913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12417605972380445478116869 2328301119821333527146913)
                  ·
                    refine ⟨1746225839866000145360185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328301119821333527146913 1746225839866000145360185)
                    ·
                      refine ⟨1309669379899500109020139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746225839866000145360185 1309669379899500109020139)
                      ·
                        rfl

theorem cell23_2550572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_2550572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550572 prefixEnd_2550572 := by exact prefixLift 2550572
  have htrace : WordTrace (prefixWord ++ tailWord_2550572) baseStart_2550572 baseEnd_2550572 := by
    simpa [prefixWord, tailWord_2550572, baseEnd_2550572] using wordTrace_append hprefix tailTrace_2550572
  have hstable : (prefixWord ++ tailWord_2550572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550572).length < 2 ^ (prefixWord ++ tailWord_2550572).sum := by decide
  have hdescent : baseEnd_2550572 < baseStart_2550572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550578 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_2550578 : Nat := 118140960795 + 2550578 * 2 ^ 59
def prefixEnd_2550578 : Nat := 4983230072969 + 3 ^ 40 * 2550578 * 2
def baseEnd_2550578 : Nat := 145519162309269676171679

theorem tailTrace_2550578 : CollatzResearch.WordTrace tailWord_2550578 prefixEnd_2550578 145519162309269676171679 := by
  unfold tailWord_2550578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256805538424746221825097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62018148102465989924866925 23256805538424746221825097)
  ·
    refine ⟨17442604153818559666368823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23256805538424746221825097 17442604153818559666368823)
    ·
      refine ⟨26163906230727839499553235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17442604153818559666368823 26163906230727839499553235)
      ·
        refine ⟨39245859346091759249329853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26163906230727839499553235 39245859346091759249329853)
        ·
          refine ⟨14717197254784409718498695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39245859346091759249329853 14717197254784409718498695)
          ·
            refine ⟨22075795882176614577748043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14717197254784409718498695 22075795882176614577748043)
            ·
              refine ⟨33113693823264921866622065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22075795882176614577748043 33113693823264921866622065)
              ·
                refine ⟨24835270367448691399966549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33113693823264921866622065 24835270367448691399966549)
                ·
                  refine ⟨145519162309269676171679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24835270367448691399966549 145519162309269676171679)
                  ·
                    rfl

theorem cell23_2550578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_2550578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550578 prefixEnd_2550578 := by exact prefixLift 2550578
  have htrace : WordTrace (prefixWord ++ tailWord_2550578) baseStart_2550578 baseEnd_2550578 := by
    simpa [prefixWord, tailWord_2550578, baseEnd_2550578] using wordTrace_append hprefix tailTrace_2550578
  have hstable : (prefixWord ++ tailWord_2550578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550578).length < 2 ^ (prefixWord ++ tailWord_2550578).sum := by decide
  have hdescent : baseEnd_2550578 < baseStart_2550578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550595 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 5]
def baseStart_2550595 : Nat := 118140960795 + 2550595 * 2 ^ 59
def prefixEnd_2550595 : Nat := 4983230072969 + 3 ^ 40 * 2550595 * 2
def baseEnd_2550595 : Nat := 145520132217172613225837

theorem tailTrace_2550595 : CollatzResearch.WordTrace tailWord_2550595 prefixEnd_2550595 145520132217172613225837 := by
  unfold tailWord_2550595
  simp only [CollatzResearch.WordTrace]
  refine ⟨93027842194637396790669239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62018561463091597860446159 93027842194637396790669239)
  ·
    refine ⟨139541763291956095186003859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93027842194637396790669239 139541763291956095186003859)
    ·
      refine ⟨209312644937934142779005789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139541763291956095186003859 209312644937934142779005789)
      ·
        refine ⟨78492241851725303542127171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209312644937934142779005789 78492241851725303542127171)
        ·
          refine ⟨117738362777587955313190757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78492241851725303542127171 117738362777587955313190757)
          ·
            refine ⟨22075943020797741621223267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117738362777587955313190757 22075943020797741621223267)
            ·
              refine ⟨33113914531196612431834901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22075943020797741621223267 33113914531196612431834901)
              ·
                refine ⟨1552214743649841207742261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33113914531196612431834901 1552214743649841207742261)
                ·
                  refine ⟨145520132217172613225837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552214743649841207742261 145520132217172613225837)
                  ·
                    rfl

theorem cell23_2550595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 5].length) (baseStart_2550595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550595 prefixEnd_2550595 := by exact prefixLift 2550595
  have htrace : WordTrace (prefixWord ++ tailWord_2550595) baseStart_2550595 baseEnd_2550595 := by
    simpa [prefixWord, tailWord_2550595, baseEnd_2550595] using wordTrace_append hprefix tailTrace_2550595
  have hstable : (prefixWord ++ tailWord_2550595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550595).length < 2 ^ (prefixWord ++ tailWord_2550595).sum := by decide
  have hdescent : baseEnd_2550595 < baseStart_2550595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550608 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_2550608 : Nat := 118140960795 + 2550608 * 2 ^ 59
def prefixEnd_2550608 : Nat := 4983230072969 + 3 ^ 40 * 2550608 * 2
def baseEnd_2550608 : Nat := 436562621734353989389991

theorem tailTrace_2550608 : CollatzResearch.WordTrace tailWord_2550608 prefixEnd_2550608 436562621734353989389991 := by
  unfold tailWord_2550608
  simp only [CollatzResearch.WordTrace]
  refine ⟨46514158171795150005446239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62018877562393533340594985 46514158171795150005446239)
  ·
    refine ⟨69771237257692725008169359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46514158171795150005446239 69771237257692725008169359)
    ·
      refine ⟨104656855886539087512254039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69771237257692725008169359 104656855886539087512254039)
      ·
        refine ⟨156985283829808631268381059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104656855886539087512254039 156985283829808631268381059)
        ·
          refine ⟨235477925744712946902571589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156985283829808631268381059 235477925744712946902571589)
          ·
            refine ⟨44152111077133677544232173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235477925744712946902571589 44152111077133677544232173)
            ·
              refine ⟨16557041653925129079087065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44152111077133677544232173 16557041653925129079087065)
              ·
                refine ⟨12417781240443846809315299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16557041653925129079087065 12417781240443846809315299)
                ·
                  refine ⟨18626671860665770213972949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12417781240443846809315299 18626671860665770213972949)
                  ·
                    refine ⟨436562621734353989389991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18626671860665770213972949 436562621734353989389991)
                    ·
                      rfl

theorem cell23_2550608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_2550608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550608 prefixEnd_2550608 := by exact prefixLift 2550608
  have htrace : WordTrace (prefixWord ++ tailWord_2550608) baseStart_2550608 baseEnd_2550608 := by
    simpa [prefixWord, tailWord_2550608, baseEnd_2550608] using wordTrace_append hprefix tailTrace_2550608
  have hstable : (prefixWord ++ tailWord_2550608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550608).length < 2 ^ (prefixWord ++ tailWord_2550608).sum := by decide
  have hdescent : baseEnd_2550608 < baseStart_2550608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550646 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2550646 : Nat := 118140960795 + 2550646 * 2 ^ 59
def prefixEnd_2550646 : Nat := 4983230072969 + 3 ^ 40 * 2550646 * 2
def baseEnd_2550646 : Nat := 145523041940881424388311

theorem tailTrace_2550646 : CollatzResearch.WordTrace tailWord_2550646 prefixEnd_2550646 145523041940881424388311 := by
  unfold tailWord_2550646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814356394840789531298487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62019801544968421667183861 5814356394840789531298487)
  ·
    refine ⟨8721534592261184296947731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5814356394840789531298487 8721534592261184296947731)
    ·
      refine ⟨13082301888391776445421597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8721534592261184296947731 13082301888391776445421597)
      ·
        refine ⟨4905863208146916167033099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13082301888391776445421597 4905863208146916167033099)
        ·
          refine ⟨7358794812220374250549649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905863208146916167033099 7358794812220374250549649)
          ·
            refine ⟨5519096109165280687912237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358794812220374250549649 5519096109165280687912237)
            ·
              refine ⟨2069661040936980257967089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5519096109165280687912237 2069661040936980257967089)
              ·
                refine ⟨1552245780702735193475317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069661040936980257967089 1552245780702735193475317)
                ·
                  refine ⟨145523041940881424388311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552245780702735193475317 145523041940881424388311)
                  ·
                    rfl

theorem cell23_2550646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2550646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550646 prefixEnd_2550646 := by exact prefixLift 2550646
  have htrace : WordTrace (prefixWord ++ tailWord_2550646) baseStart_2550646 baseEnd_2550646 := by
    simpa [prefixWord, tailWord_2550646, baseEnd_2550646] using wordTrace_append hprefix tailTrace_2550646
  have hstable : (prefixWord ++ tailWord_2550646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550646).length < 2 ^ (prefixWord ++ tailWord_2550646).sum := by decide
  have hdescent : baseEnd_2550646 < baseStart_2550646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550648 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2550648 : Nat := 118140960795 + 2550648 * 2 ^ 59
def prefixEnd_2550648 : Nat := 4983230072969 + 3 ^ 40 * 2550648 * 2
def baseEnd_2550648 : Nat := 1309708404429241811669789

theorem tailTrace_2550648 : CollatzResearch.WordTrace tailWord_2550648 prefixEnd_2550648 1309708404429241811669789 := by
  unfold tailWord_2550648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46514887631722693421174299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62019850175630257894899065 46514887631722693421174299)
  ·
    refine ⟨69772331447584040131761449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46514887631722693421174299 69772331447584040131761449)
    ·
      refine ⟨52329248585688030098821087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69772331447584040131761449 52329248585688030098821087)
      ·
        refine ⟨78493872878532045148231631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52329248585688030098821087 78493872878532045148231631)
        ·
          refine ⟨117740809317798067722347447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78493872878532045148231631 117740809317798067722347447)
          ·
            refine ⟨176611213976697101583521171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117740809317798067722347447 176611213976697101583521171)
            ·
              refine ⟨264916820965045652375281757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176611213976697101583521171 264916820965045652375281757)
              ·
                refine ⟨99343807861892119640730659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264916820965045652375281757 99343807861892119640730659)
                ·
                  refine ⟨149015711792838179461095989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99343807861892119640730659 149015711792838179461095989)
                  ·
                    refine ⟨13970222980578579324477749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149015711792838179461095989 13970222980578579324477749)
                    ·
                      refine ⟨1309708404429241811669789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13970222980578579324477749 1309708404429241811669789)
                      ·
                        rfl

theorem cell23_2550648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2550648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550648 prefixEnd_2550648 := by exact prefixLift 2550648
  have htrace : WordTrace (prefixWord ++ tailWord_2550648) baseStart_2550648 baseEnd_2550648 := by
    simpa [prefixWord, tailWord_2550648, baseEnd_2550648] using wordTrace_append hprefix tailTrace_2550648
  have hstable : (prefixWord ++ tailWord_2550648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550648).length < 2 ^ (prefixWord ++ tailWord_2550648).sum := by decide
  have hdescent : baseEnd_2550648 < baseStart_2550648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550732 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_2550732 : Nat := 118140960795 + 2550732 * 2 ^ 59
def prefixEnd_2550732 : Nat := 4983230072969 + 3 ^ 40 * 2550732 * 2
def baseEnd_2550732 : Nat := 436583845601406494339801

theorem tailTrace_2550732 : CollatzResearch.WordTrace tailWord_2550732 prefixEnd_2550732 436583845601406494339801 := by
  unfold tailWord_2550732
  simp only [CollatzResearch.WordTrace]
  refine ⟨46516419497570534594203225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62021892663427379458937633 46516419497570534594203225)
  ·
    refine ⟨34887314623177900945652419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46516419497570534594203225 34887314623177900945652419)
    ·
      refine ⟨52330971934766851418478629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34887314623177900945652419 52330971934766851418478629)
      ·
        refine ⟨9812057237768784640964743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52330971934766851418478629 9812057237768784640964743)
        ·
          refine ⟨14718085856653176961447115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9812057237768784640964743 14718085856653176961447115)
          ·
            refine ⟨22077128784979765442170673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718085856653176961447115 22077128784979765442170673)
            ·
              refine ⟨16557846588734824081628005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22077128784979765442170673 16557846588734824081628005)
              ·
                refine ⟨3104596235387779515305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16557846588734824081628005 3104596235387779515305251)
                ·
                  refine ⟨4656894353081669272957877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104596235387779515305251 4656894353081669272957877)
                  ·
                    refine ⟨436583845601406494339801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4656894353081669272957877 436583845601406494339801)
                    ·
                      rfl

theorem cell23_2550732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_2550732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550732 prefixEnd_2550732 := by exact prefixLift 2550732
  have htrace : WordTrace (prefixWord ++ tailWord_2550732) baseStart_2550732 baseEnd_2550732 := by
    simpa [prefixWord, tailWord_2550732, baseEnd_2550732] using wordTrace_append hprefix tailTrace_2550732
  have hstable : (prefixWord ++ tailWord_2550732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550732).length < 2 ^ (prefixWord ++ tailWord_2550732).sum := by decide
  have hdescent : baseEnd_2550732 < baseStart_2550732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550733 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2550733 : Nat := 118140960795 + 2550733 * 2 ^ 59
def prefixEnd_2550733 : Nat := 4983230072969 + 3 ^ 40 * 2550733 * 2
def baseEnd_2550733 : Nat := 1309752050284873979106899

theorem tailTrace_2550733 : CollatzResearch.WordTrace tailWord_2550733 prefixEnd_2550733 1309752050284873979106899 := by
  unfold tailWord_2550733
  simp only [CollatzResearch.WordTrace]
  refine ⟨93032875468137446359192853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62021916978758297572795235 93032875468137446359192853)
  ·
    refine ⟨4360916037568942798087165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93032875468137446359192853 4360916037568942798087165)
    ·
      refine ⟨1635343514088353549282687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4360916037568942798087165 1635343514088353549282687)
      ·
        refine ⟨2453015271132530323924031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635343514088353549282687 2453015271132530323924031)
        ·
          refine ⟨3679522906698795485886047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2453015271132530323924031 3679522906698795485886047)
          ·
            refine ⟨5519284360048193228829071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679522906698795485886047 5519284360048193228829071)
            ·
              refine ⟨8278926540072289843243607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519284360048193228829071 8278926540072289843243607)
              ·
                refine ⟨12418389810108434764865411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8278926540072289843243607 12418389810108434764865411)
                ·
                  refine ⟨18627584715162652147298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12418389810108434764865411 18627584715162652147298117)
                  ·
                    refine ⟨3492672134092997277618397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18627584715162652147298117 3492672134092997277618397)
                    ·
                      refine ⟨1309752050284873979106899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492672134092997277618397 1309752050284873979106899)
                      ·
                        rfl

theorem cell23_2550733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2550733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550733 prefixEnd_2550733 := by exact prefixLift 2550733
  have htrace : WordTrace (prefixWord ++ tailWord_2550733) baseStart_2550733 baseEnd_2550733 := by
    simpa [prefixWord, tailWord_2550733, baseEnd_2550733] using wordTrace_append hprefix tailTrace_2550733
  have hstable : (prefixWord ++ tailWord_2550733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550733).length < 2 ^ (prefixWord ++ tailWord_2550733).sum := by decide
  have hdescent : baseEnd_2550733 < baseStart_2550733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550746 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3]
def baseStart_2550746 : Nat := 118140960795 + 2550746 * 2 ^ 59
def prefixEnd_2550746 : Nat := 4983230072969 + 3 ^ 40 * 2550746 * 2
def baseEnd_2550746 : Nat := 1309758725533382428244339

theorem tailTrace_2550746 : CollatzResearch.WordTrace tailWord_2550746 prefixEnd_2550746 1309758725533382428244339 := by
  unfold tailWord_2550746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258337404272587394854023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62022233078060233052944061 23258337404272587394854023)
  ·
    refine ⟨34887506106408881092281035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23258337404272587394854023 34887506106408881092281035)
    ·
      refine ⟨52331259159613321638421553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34887506106408881092281035 52331259159613321638421553)
      ·
        refine ⟨39248444369709991228816165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52331259159613321638421553 39248444369709991228816165)
        ·
          refine ⟨7359083319320623355403031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39248444369709991228816165 7359083319320623355403031)
          ·
            refine ⟨11038624978980935033104547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7359083319320623355403031 11038624978980935033104547)
            ·
              refine ⟨16557937468471402549656821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11038624978980935033104547 16557937468471402549656821)
              ·
                refine ⟨1552306637669193989030327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16557937468471402549656821 1552306637669193989030327)
                ·
                  refine ⟨2328459956503790983545491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552306637669193989030327 2328459956503790983545491)
                  ·
                    refine ⟨3492689934755686475318237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328459956503790983545491 3492689934755686475318237)
                    ·
                      refine ⟨1309758725533382428244339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492689934755686475318237 1309758725533382428244339)
                      ·
                        rfl

theorem cell23_2550746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_2550746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550746 prefixEnd_2550746 := by exact prefixLift 2550746
  have htrace : WordTrace (prefixWord ++ tailWord_2550746) baseStart_2550746 baseEnd_2550746 := by
    simpa [prefixWord, tailWord_2550746, baseEnd_2550746] using wordTrace_append hprefix tailTrace_2550746
  have hstable : (prefixWord ++ tailWord_2550746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550746).length < 2 ^ (prefixWord ++ tailWord_2550746).sum := by decide
  have hdescent : baseEnd_2550746 < baseStart_2550746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550749 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2550749 : Nat := 118140960795 + 2550749 * 2 ^ 59
def prefixEnd_2550749 : Nat := 4983230072969 + 3 ^ 40 * 2550749 * 2
def baseEnd_2550749 : Nat := 436586755325115305502275

theorem tailTrace_2550749 : CollatzResearch.WordTrace tailWord_2550749 prefixEnd_2550749 436586755325115305502275 := by
  unfold tailWord_2550749
  simp only [CollatzResearch.WordTrace]
  refine ⟨93033459036079481091775301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62022306024052987394516867 93033459036079481091775301)
  ·
    refine ⟨17443773569264902704707869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93033459036079481091775301 17443773569264902704707869)
    ·
      refine ⟨6541415088474338514265451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17443773569264902704707869 6541415088474338514265451)
      ·
        refine ⟨9812122632711507771398177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6541415088474338514265451 9812122632711507771398177)
        ·
          refine ⟨7359091974533630828548633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9812122632711507771398177 7359091974533630828548633)
          ·
            refine ⟨5519318980900223121411475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7359091974533630828548633 5519318980900223121411475)
            ·
              refine ⟨8278978471350334682117213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519318980900223121411475 8278978471350334682117213)
              ·
                refine ⟨3104616926756375505793955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8278978471350334682117213 3104616926756375505793955)
                ·
                  refine ⟨4656925390134563258690933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104616926756375505793955 4656925390134563258690933)
                  ·
                    refine ⟨436586755325115305502275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4656925390134563258690933 436586755325115305502275)
                    ·
                      rfl

theorem cell23_2550749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2550749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550749 prefixEnd_2550749 := by exact prefixLift 2550749
  have htrace : WordTrace (prefixWord ++ tailWord_2550749) baseStart_2550749 baseEnd_2550749 := by
    simpa [prefixWord, tailWord_2550749, baseEnd_2550749] using wordTrace_append hprefix tailTrace_2550749
  have hstable : (prefixWord ++ tailWord_2550749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550749).length < 2 ^ (prefixWord ++ tailWord_2550749).sum := by decide
  have hdescent : baseEnd_2550749 < baseStart_2550749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550789 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_2550789 : Nat := 118140960795 + 2550789 * 2 ^ 59
def prefixEnd_2550789 : Nat := 4983230072969 + 3 ^ 40 * 2550789 * 2
def baseEnd_2550789 : Nat := 1309780805201525760006641

theorem tailTrace_2550789 : CollatzResearch.WordTrace tailWord_2550789 prefixEnd_2550789 1309780805201525760006641 := by
  unfold tailWord_2550789
  simp only [CollatzResearch.WordTrace]
  refine ⟨93034917955934567923231421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62023278637289711948820947 93034917955934567923231421)
  ·
    refine ⟨34888094233475462971211783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93034917955934567923231421 34888094233475462971211783)
    ·
      refine ⟨52332141350213194456817675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34888094233475462971211783 52332141350213194456817675)
      ·
        refine ⟨78498212025319791685226513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52332141350213194456817675 78498212025319791685226513)
        ·
          refine ⟨58873659018989843763919885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78498212025319791685226513 58873659018989843763919885)
          ·
            refine ⟨22077622132121191411469957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58873659018989843763919885 22077622132121191411469957)
            ·
              refine ⟨4139554149772723389650617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22077622132121191411469957 4139554149772723389650617)
              ·
                refine ⟨3104665612329542542237963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4139554149772723389650617 3104665612329542542237963)
                ·
                  refine ⟨4656998418494313813356945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104665612329542542237963 4656998418494313813356945)
                  ·
                    refine ⟨3492748813870735360017709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4656998418494313813356945 3492748813870735360017709)
                    ·
                      refine ⟨1309780805201525760006641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492748813870735360017709 1309780805201525760006641)
                      ·
                        rfl

theorem cell23_2550789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_2550789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550789 prefixEnd_2550789 := by exact prefixLift 2550789
  have htrace : WordTrace (prefixWord ++ tailWord_2550789) baseStart_2550789 baseEnd_2550789 := by
    simpa [prefixWord, tailWord_2550789, baseEnd_2550789] using wordTrace_append hprefix tailTrace_2550789
  have hstable : (prefixWord ++ tailWord_2550789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550789).length < 2 ^ (prefixWord ++ tailWord_2550789).sum := by decide
  have hdescent : baseEnd_2550789 < baseStart_2550789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550792 : List Nat := [2, 1, 3, 2, 1, 3, 4, 7]
def baseStart_2550792 : Nat := 118140960795 + 2550792 * 2 ^ 59
def prefixEnd_2550792 : Nat := 4983230072969 + 3 ^ 40 * 2550792 * 2
def baseEnd_2550792 : Nat := 48510457246055157343301

theorem tailTrace_2550792 : CollatzResearch.WordTrace tailWord_2550792 prefixEnd_2550792 48510457246055157343301 := by
  unfold tailWord_2550792
  simp only [CollatzResearch.WordTrace]
  refine ⟨46517513687461849717795315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62023351583282466290393753 46517513687461849717795315)
  ·
    refine ⟨69776270531192774576692973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46517513687461849717795315 69776270531192774576692973)
    ·
      refine ⟨26166101449197290466259865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69776270531192774576692973 26166101449197290466259865)
      ·
        refine ⟨19624576086897967849694899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26166101449197290466259865 19624576086897967849694899)
        ·
          refine ⟨29436864130346951774542349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19624576086897967849694899 29436864130346951774542349)
          ·
            refine ⟨11038824048880106915453381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29436864130346951774542349 11038824048880106915453381)
            ·
              refine ⟨2069779509165020046647509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11038824048880106915453381 2069779509165020046647509)
              ·
                refine ⟨48510457246055157343301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2069779509165020046647509 48510457246055157343301)
                ·
                  rfl

theorem cell23_2550792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 7].length) (baseStart_2550792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550792 prefixEnd_2550792 := by exact prefixLift 2550792
  have htrace : WordTrace (prefixWord ++ tailWord_2550792) baseStart_2550792 baseEnd_2550792 := by
    simpa [prefixWord, tailWord_2550792, baseEnd_2550792] using wordTrace_append hprefix tailTrace_2550792
  have hstable : (prefixWord ++ tailWord_2550792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550792).length < 2 ^ (prefixWord ++ tailWord_2550792).sum := by decide
  have hdescent : baseEnd_2550792 < baseStart_2550792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550819 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 3]
def baseStart_2550819 : Nat := 118140960795 + 2550819 * 2 ^ 59
def prefixEnd_2550819 : Nat := 4983230072969 + 3 ^ 40 * 2550819 * 2
def baseEnd_2550819 : Nat := 1309796209621160642631503

theorem tailTrace_2550819 : CollatzResearch.WordTrace tailWord_2550819 prefixEnd_2550819 1309796209621160642631503 := by
  unfold tailWord_2550819
  simp only [CollatzResearch.WordTrace]
  refine ⟨93036012145825883046823511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62024008097217255364549007 93036012145825883046823511)
  ·
    refine ⟨139554018218738824570235267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93036012145825883046823511 139554018218738824570235267)
    ·
      refine ⟨209331027328108236855352901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139554018218738824570235267 209331027328108236855352901)
      ·
        refine ⟨39249567624020294410378669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209331027328108236855352901 39249567624020294410378669)
        ·
          refine ⟨14718587859007610403892001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39249567624020294410378669 14718587859007610403892001)
          ·
            refine ⟨11038940894255707802919001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14718587859007610403892001 11038940894255707802919001)
            ·
              refine ⟨8279205670691780852189251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11038940894255707802919001 8279205670691780852189251)
              ·
                refine ⟨12418808506037671278283877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279205670691780852189251 12418808506037671278283877)
                ·
                  refine ⟨2328526594882063364678227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12418808506037671278283877 2328526594882063364678227)
                  ·
                    refine ⟨3492789892323095047017341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328526594882063364678227 3492789892323095047017341)
                    ·
                      refine ⟨1309796209621160642631503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492789892323095047017341 1309796209621160642631503)
                      ·
                        rfl

theorem cell23_2550819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_2550819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550819 prefixEnd_2550819 := by exact prefixLift 2550819
  have htrace : WordTrace (prefixWord ++ tailWord_2550819) baseStart_2550819 baseEnd_2550819 := by
    simpa [prefixWord, tailWord_2550819, baseEnd_2550819] using wordTrace_append hprefix tailTrace_2550819
  have hstable : (prefixWord ++ tailWord_2550819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550819).length < 2 ^ (prefixWord ++ tailWord_2550819).sum := by decide
  have hdescent : baseEnd_2550819 < baseStart_2550819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550835 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 8]
def baseStart_2550835 : Nat := 118140960795 + 2550835 * 2 ^ 59
def prefixEnd_2550835 : Nat := 4983230072969 + 3 ^ 40 * 2550835 * 2
def baseEnd_2550835 : Nat := 436601475103877526677143

theorem tailTrace_2550835 : CollatzResearch.WordTrace tailWord_2550835 prefixEnd_2550835 436601475103877526677143 := by
  unfold tailWord_2550835
  simp only [CollatzResearch.WordTrace]
  refine ⟨93036595713767917779405959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62024397142511945186270639 93036595713767917779405959)
  ·
    refine ⟨139554893570651876669108939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93036595713767917779405959 139554893570651876669108939)
    ·
      refine ⟨209332340355977815003663409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139554893570651876669108939 209332340355977815003663409)
      ·
        refine ⟨156999255266983361252747557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209332340355977815003663409 156999255266983361252747557)
        ·
          refine ⟨29437360362559380234890167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156999255266983361252747557 29437360362559380234890167)
          ·
            refine ⟨44156040543839070352335251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29437360362559380234890167 44156040543839070352335251)
            ·
              refine ⟨66234060815758605528502877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44156040543839070352335251 66234060815758605528502877)
              ·
                refine ⟨24837772805909477073188579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66234060815758605528502877 24837772805909477073188579)
                ·
                  refine ⟨37256659208864215609782869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24837772805909477073188579 37256659208864215609782869)
                  ·
                    refine ⟨436601475103877526677143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37256659208864215609782869 436601475103877526677143)
                    ·
                      rfl

theorem cell23_2550835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_2550835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550835 prefixEnd_2550835 := by exact prefixLift 2550835
  have htrace : WordTrace (prefixWord ++ tailWord_2550835) baseStart_2550835 baseEnd_2550835 := by
    simpa [prefixWord, tailWord_2550835, baseEnd_2550835] using wordTrace_append hprefix tailTrace_2550835
  have hstable : (prefixWord ++ tailWord_2550835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550835).length < 2 ^ (prefixWord ++ tailWord_2550835).sum := by decide
  have hdescent : baseEnd_2550835 < baseStart_2550835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550862 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2550862 : Nat := 118140960795 + 2550862 * 2 ^ 59
def prefixEnd_2550862 : Nat := 4983230072969 + 3 ^ 40 * 2550862 * 2
def baseEnd_2550862 : Nat := 1309818289289303974393805

theorem tailTrace_2550862 : CollatzResearch.WordTrace tailWord_2550862 prefixEnd_2550862 1309818289289303974393805 := by
  unfold tailWord_2550862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11629697560583762673829855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62025053656446734260425893 11629697560583762673829855)
  ·
    refine ⟨17444546340875644010744783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11629697560583762673829855 17444546340875644010744783)
    ·
      refine ⟨26166819511313466016117175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17444546340875644010744783 26166819511313466016117175)
      ·
        refine ⟨39250229266970199024175763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26166819511313466016117175 39250229266970199024175763)
        ·
          refine ⟨58875343900455298536263645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39250229266970199024175763 58875343900455298536263645)
          ·
            refine ⟨22078253962670736951098867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58875343900455298536263645 22078253962670736951098867)
            ·
              refine ⟨33117380944006105426648301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22078253962670736951098867 33117380944006105426648301)
              ·
                refine ⟨12419017854002289534993113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33117380944006105426648301 12419017854002289534993113)
                ·
                  refine ⟨9314263390501717151244835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12419017854002289534993113 9314263390501717151244835)
                  ·
                    refine ⟨13971395085752575726867253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9314263390501717151244835 13971395085752575726867253)
                    ·
                      refine ⟨1309818289289303974393805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13971395085752575726867253 1309818289289303974393805)
                      ·
                        rfl

theorem cell23_2550862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2550862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550862 prefixEnd_2550862 := by exact prefixLift 2550862
  have htrace : WordTrace (prefixWord ++ tailWord_2550862) baseStart_2550862 baseEnd_2550862 := by
    simpa [prefixWord, tailWord_2550862, baseEnd_2550862] using wordTrace_append hprefix tailTrace_2550862
  have hstable : (prefixWord ++ tailWord_2550862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550862).length < 2 ^ (prefixWord ++ tailWord_2550862).sum := by decide
  have hdescent : baseEnd_2550862 < baseStart_2550862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550872 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2550872 : Nat := 118140960795 + 2550872 * 2 ^ 59
def prefixEnd_2550872 : Nat := 4983230072969 + 3 ^ 40 * 2550872 * 2
def baseEnd_2550872 : Nat := 1309823424095848935268759

theorem tailTrace_2550872 : CollatzResearch.WordTrace tailWord_2550872 prefixEnd_2550872 1309823424095848935268759 := by
  unfold tailWord_2550872
  simp only [CollatzResearch.WordTrace]
  refine ⟨46518972607316936549251435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62025296809755915399001913 46518972607316936549251435)
  ·
    refine ⟨69778458910975404823877153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46518972607316936549251435 69778458910975404823877153)
    ·
      refine ⟨52333844183231553617907865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69778458910975404823877153 52333844183231553617907865)
      ·
        refine ⟨39250383137423665213430899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52333844183231553617907865 39250383137423665213430899)
        ·
          refine ⟨58875574706135497820146349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39250383137423665213430899 58875574706135497820146349)
          ·
            refine ⟨22078340514800811682554881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58875574706135497820146349 22078340514800811682554881)
            ·
              refine ⟨16558755386100608761916161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22078340514800811682554881 16558755386100608761916161)
              ·
                refine ⟨12419066539575456571437121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16558755386100608761916161 12419066539575456571437121)
                ·
                  refine ⟨9314299904681592428577841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12419066539575456571437121 9314299904681592428577841)
                  ·
                    refine ⟨6985724928511194321433381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9314299904681592428577841 6985724928511194321433381)
                    ·
                      refine ⟨1309823424095848935268759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6985724928511194321433381 1309823424095848935268759)
                      ·
                        rfl

theorem cell23_2550872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2550872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550872 prefixEnd_2550872 := by exact prefixLift 2550872
  have htrace : WordTrace (prefixWord ++ tailWord_2550872) baseStart_2550872 baseEnd_2550872 := by
    simpa [prefixWord, tailWord_2550872, baseEnd_2550872] using wordTrace_append hprefix tailTrace_2550872
  have hstable : (prefixWord ++ tailWord_2550872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550872).length < 2 ^ (prefixWord ++ tailWord_2550872).sum := by decide
  have hdescent : baseEnd_2550872 < baseStart_2550872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550893 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2550893 : Nat := 118140960795 + 2550893 * 2 ^ 59
def prefixEnd_2550893 : Nat := 4983230072969 + 3 ^ 40 * 2550893 * 2
def baseEnd_2550893 : Nat := 1309834207189593353106163

theorem tailTrace_2550893 : CollatzResearch.WordTrace tailWord_2550893 prefixEnd_2550893 1309834207189593353106163 := by
  unfold tailWord_2550893
  simp only [CollatzResearch.WordTrace]
  refine ⟨93038711147557793685017333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62025807431705195790011555 93038711147557793685017333)
  ·
    refine ⟨8722379170083543157970375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93038711147557793685017333 8722379170083543157970375)
    ·
      refine ⟨13083568755125314736955563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8722379170083543157970375 13083568755125314736955563)
      ·
        refine ⟨19625353132687972105433345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13083568755125314736955563 19625353132687972105433345)
        ·
          refine ⟨14719014849515979079075009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19625353132687972105433345 14719014849515979079075009)
          ·
            refine ⟨11039261137136984309306257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14719014849515979079075009 11039261137136984309306257)
            ·
              refine ⟨8279445852852738231979693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11039261137136984309306257 8279445852852738231979693)
              ·
                refine ⟨3104792194819776836992385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8279445852852738231979693 3104792194819776836992385)
                ·
                  refine ⟨2328594146114832627744289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3104792194819776836992385 2328594146114832627744289)
                  ·
                    refine ⟨1746445609586124470808217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328594146114832627744289 1746445609586124470808217)
                    ·
                      refine ⟨1309834207189593353106163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746445609586124470808217 1309834207189593353106163)
                      ·
                        rfl

theorem cell23_2550893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2550893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550893 prefixEnd_2550893 := by exact prefixLift 2550893
  have htrace : WordTrace (prefixWord ++ tailWord_2550893) baseStart_2550893 baseEnd_2550893 := by
    simpa [prefixWord, tailWord_2550893, baseEnd_2550893] using wordTrace_append hprefix tailTrace_2550893
  have hstable : (prefixWord ++ tailWord_2550893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550893).length < 2 ^ (prefixWord ++ tailWord_2550893).sum := by decide
  have hdescent : baseEnd_2550893 < baseStart_2550893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550916 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 5]
def baseStart_2550916 : Nat := 118140960795 + 2550916 * 2 ^ 59
def prefixEnd_2550916 : Nat := 4983230072969 + 3 ^ 40 * 2550916 * 2
def baseEnd_2550916 : Nat := 145538446360516307013173

theorem tailTrace_2550916 : CollatzResearch.WordTrace tailWord_2550916 prefixEnd_2550916 145538446360516307013173 := by
  unfold tailWord_2550916
  simp only [CollatzResearch.WordTrace]
  refine ⟨46519775013237234306552301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62026366684316312408736401 46519775013237234306552301)
  ·
    refine ⟨17444915629963962864957113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46519775013237234306552301 17444915629963962864957113)
    ·
      refine ⟨13083686722472972148717835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17444915629963962864957113 13083686722472972148717835)
      ·
        refine ⟨19625530083709458223076753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13083686722472972148717835 19625530083709458223076753)
        ·
          refine ⟨14719147562782093667307565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19625530083709458223076753 14719147562782093667307565)
          ·
            refine ⟨5519680336043285125240337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14719147562782093667307565 5519680336043285125240337)
            ·
              refine ⟨4139760252032463843930253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5519680336043285125240337 4139760252032463843930253)
              ·
                refine ⟨1552410094512173941473845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4139760252032463843930253 1552410094512173941473845)
                ·
                  refine ⟨145538446360516307013173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552410094512173941473845 145538446360516307013173)
                  ·
                    rfl

theorem cell23_2550916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_2550916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550916 prefixEnd_2550916 := by exact prefixLift 2550916
  have htrace : WordTrace (prefixWord ++ tailWord_2550916) baseStart_2550916 baseEnd_2550916 := by
    simpa [prefixWord, tailWord_2550916, baseEnd_2550916] using wordTrace_append hprefix tailTrace_2550916
  have hstable : (prefixWord ++ tailWord_2550916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550916).length < 2 ^ (prefixWord ++ tailWord_2550916).sum := by decide
  have hdescent : baseEnd_2550916 < baseStart_2550916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550959 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 3, 4]
def baseStart_2550959 : Nat := 118140960795 + 2550959 * 2 ^ 59
def prefixEnd_2550959 : Nat := 4983230072969 + 3 ^ 40 * 2550959 * 2
def baseEnd_2550959 : Nat := 436622698970930031626953

theorem tailTrace_2550959 : CollatzResearch.WordTrace tailWord_2550959 prefixEnd_2550959 436622698970930031626953 := by
  unfold tailWord_2550959
  simp only [CollatzResearch.WordTrace]
  refine ⟨93041118365318686956919931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62027412243545791304613287 93041118365318686956919931)
  ·
    refine ⟨139561677547978030435379897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93041118365318686956919931 139561677547978030435379897)
    ·
      refine ⟨104671258160983522826534923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139561677547978030435379897 104671258160983522826534923)
      ·
        refine ⟨157006887241475284239802385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104671258160983522826534923 157006887241475284239802385)
        ·
          refine ⟨117755165431106463179851789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157006887241475284239802385 117755165431106463179851789)
          ·
            refine ⟨44158187036664923692444421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117755165431106463179851789 44158187036664923692444421)
            ·
              refine ⟨8279660069374673192333329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44158187036664923692444421 8279660069374673192333329)
              ·
                refine ⟨6209745052031004894249997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8279660069374673192333329 6209745052031004894249997)
                ·
                  refine ⟨2328654394511626835343749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6209745052031004894249997 2328654394511626835343749)
                  ·
                    refine ⟨436622698970930031626953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2328654394511626835343749 436622698970930031626953)
                    ·
                      rfl

theorem cell23_2550959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_2550959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550959 prefixEnd_2550959 := by exact prefixLift 2550959
  have htrace : WordTrace (prefixWord ++ tailWord_2550959) baseStart_2550959 baseEnd_2550959 := by
    simpa [prefixWord, tailWord_2550959, baseEnd_2550959] using wordTrace_append hprefix tailTrace_2550959
  have hstable : (prefixWord ++ tailWord_2550959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550959).length < 2 ^ (prefixWord ++ tailWord_2550959).sum := by decide
  have hdescent : baseEnd_2550959 < baseStart_2550959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550969 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2550969 : Nat := 118140960795 + 2550969 * 2 ^ 59
def prefixEnd_2550969 : Nat := 4983230072969 + 3 ^ 40 * 2550969 * 2
def baseEnd_2550969 : Nat := 1309873231719335055755813

theorem tailTrace_2550969 : CollatzResearch.WordTrace tailWord_2550969 prefixEnd_2550969 1309873231719335055755813 := by
  unfold tailWord_2550969
  simp only [CollatzResearch.WordTrace]
  refine ⟨93041483095282458664783961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62027655396854972443189307 93041483095282458664783961)
  ·
    refine ⟨69781112321461843998587971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93041483095282458664783961 69781112321461843998587971)
    ·
      refine ⟨104671668482192765997881957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69781112321461843998587971 104671668482192765997881957)
      ·
        refine ⟨19625937840411143624602867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104671668482192765997881957 19625937840411143624602867)
        ·
          refine ⟨29438906760616715436904301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625937840411143624602867 29438906760616715436904301)
          ·
            refine ⟨11039590035231268288839113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29438906760616715436904301 11039590035231268288839113)
            ·
              refine ⟨8279692526423451216629335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11039590035231268288839113 8279692526423451216629335)
              ·
                refine ⟨12419538789635176824944003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279692526423451216629335 12419538789635176824944003)
                ·
                  refine ⟨18629308184452765237416005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12419538789635176824944003 18629308184452765237416005)
                  ·
                    refine ⟨3492995284584893482015501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18629308184452765237416005 3492995284584893482015501)
                    ·
                      refine ⟨1309873231719335055755813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3492995284584893482015501 1309873231719335055755813)
                      ·
                        rfl

theorem cell23_2550969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2550969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550969 prefixEnd_2550969 := by exact prefixLift 2550969
  have htrace : WordTrace (prefixWord ++ tailWord_2550969) baseStart_2550969 baseEnd_2550969 := by
    simpa [prefixWord, tailWord_2550969, baseEnd_2550969] using wordTrace_append hprefix tailTrace_2550969
  have hstable : (prefixWord ++ tailWord_2550969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550969).length < 2 ^ (prefixWord ++ tailWord_2550969).sum := by decide
  have hdescent : baseEnd_2550969 < baseStart_2550969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550986 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_2550986 : Nat := 118140960795 + 2550986 * 2 ^ 59
def prefixEnd_2550986 : Nat := 4983230072969 + 3 ^ 40 * 2550986 * 2
def baseEnd_2550986 : Nat := 1309881960890461489243235

theorem tailTrace_2550986 : CollatzResearch.WordTrace tailWord_2550986 prefixEnd_2550986 1309881960890461489243235 := by
  unfold tailWord_2550986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260525784055217642038203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62028068757480580378768541 23260525784055217642038203)
  ·
    refine ⟨34890788676082826463057305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23260525784055217642038203 34890788676082826463057305)
    ·
      refine ⟨26168091507062119847292979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34890788676082826463057305 26168091507062119847292979)
      ·
        refine ⟨39252137260593179770939469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26168091507062119847292979 39252137260593179770939469)
        ·
          refine ⟨14719551472722442414102301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39252137260593179770939469 14719551472722442414102301)
          ·
            refine ⟨5519831802270915905288363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14719551472722442414102301 5519831802270915905288363)
            ·
              refine ⟨8279747703406373857932545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519831802270915905288363 8279747703406373857932545)
              ·
                refine ⟨6209810777554780393449409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8279747703406373857932545 6209810777554780393449409)
                ·
                  refine ⟨4657358083166085295087057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6209810777554780393449409 4657358083166085295087057)
                  ·
                    refine ⟨3493018562374563971315293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657358083166085295087057 3493018562374563971315293)
                    ·
                      refine ⟨1309881960890461489243235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493018562374563971315293 1309881960890461489243235)
                      ·
                        rfl

theorem cell23_2550986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_2550986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2550986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2550986 prefixEnd_2550986 := by exact prefixLift 2550986
  have htrace : WordTrace (prefixWord ++ tailWord_2550986) baseStart_2550986 baseEnd_2550986 := by
    simpa [prefixWord, tailWord_2550986, baseEnd_2550986] using wordTrace_append hprefix tailTrace_2550986
  have hstable : (prefixWord ++ tailWord_2550986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550986).length < 2 ^ (prefixWord ++ tailWord_2550986).sum := by decide
  have hdescent : baseEnd_2550986 < baseStart_2550986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551002 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_2551002 : Nat := 118140960795 + 2551002 * 2 ^ 59
def prefixEnd_2551002 : Nat := 4983230072969 + 3 ^ 40 * 2551002 * 2
def baseEnd_2551002 : Nat := 436630058860311142214387

theorem tailTrace_2551002 : CollatzResearch.WordTrace tailWord_2551002 prefixEnd_2551002 436630058860311142214387 := by
  unfold tailWord_2551002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260671676040726325183815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62028457802775270200490173 23260671676040726325183815)
  ·
    refine ⟨34891007514061089487775723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23260671676040726325183815 34891007514061089487775723)
    ·
      refine ⟨52336511271091634231663585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34891007514061089487775723 52336511271091634231663585)
      ·
        refine ⟨39252383453318725673747689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52336511271091634231663585 39252383453318725673747689)
        ·
          refine ⟨29439287589989044255310767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39252383453318725673747689 29439287589989044255310767)
          ·
            refine ⟨44158931384983566382966151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29439287589989044255310767 44158931384983566382966151)
            ·
              refine ⟨66238397077475349574449227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44158931384983566382966151 66238397077475349574449227)
              ·
                refine ⟨99357595616213024361673841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66238397077475349574449227 99357595616213024361673841)
                ·
                  refine ⟨74518196712159768271255381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99357595616213024361673841 74518196712159768271255381)
                  ·
                    refine ⟨436630058860311142214387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74518196712159768271255381 436630058860311142214387)
                    ·
                      rfl

theorem cell23_2551002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_2551002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551002 prefixEnd_2551002 := by exact prefixLift 2551002
  have htrace : WordTrace (prefixWord ++ tailWord_2551002) baseStart_2551002 baseEnd_2551002 := by
    simpa [prefixWord, tailWord_2551002, baseEnd_2551002] using wordTrace_append hprefix tailTrace_2551002
  have hstable : (prefixWord ++ tailWord_2551002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551002).length < 2 ^ (prefixWord ++ tailWord_2551002).sum := by decide
  have hdescent : baseEnd_2551002 < baseStart_2551002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551016 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2551016 : Nat := 118140960795 + 2551016 * 2 ^ 59
def prefixEnd_2551016 : Nat := 4983230072969 + 3 ^ 40 * 2551016 * 2
def baseEnd_2551016 : Nat := 1309897365310096371868097

theorem tailTrace_2551016 : CollatzResearch.WordTrace tailWord_2551016 prefixEnd_2551016 1309897365310096371868097 := by
  unfold tailWord_2551016
  simp only [CollatzResearch.WordTrace]
  refine ⟨46521598663056092845872451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62028798217408123794496601 46521598663056092845872451)
  ·
    refine ⟨69782397994584139268808677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46521598663056092845872451 69782397994584139268808677)
    ·
      refine ⟨13084199623984526112901627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69782397994584139268808677 13084199623984526112901627)
      ·
        refine ⟨19626299435976789169352441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13084199623984526112901627 19626299435976789169352441)
        ·
          refine ⟨14719724576982591877014331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19626299435976789169352441 14719724576982591877014331)
          ·
            refine ⟨22079586865473887815521497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14719724576982591877014331 22079586865473887815521497)
            ·
              refine ⟨16559690149105415861641123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22079586865473887815521497 16559690149105415861641123)
              ·
                refine ⟨24839535223658123792461685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16559690149105415861641123 24839535223658123792461685)
                ·
                  refine ⟨2328706427217949105543283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24839535223658123792461685 2328706427217949105543283)
                  ·
                    refine ⟨3493059640826923658314925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328706427217949105543283 3493059640826923658314925)
                    ·
                      refine ⟨1309897365310096371868097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493059640826923658314925 1309897365310096371868097)
                      ·
                        rfl

theorem cell23_2551016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2551016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551016 prefixEnd_2551016 := by exact prefixLift 2551016
  have htrace : WordTrace (prefixWord ++ tailWord_2551016) baseStart_2551016 baseEnd_2551016 := by
    simpa [prefixWord, tailWord_2551016, baseEnd_2551016] using wordTrace_append hprefix tailTrace_2551016
  have hstable : (prefixWord ++ tailWord_2551016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551016).length < 2 ^ (prefixWord ++ tailWord_2551016).sum := by decide
  have hdescent : baseEnd_2551016 < baseStart_2551016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551019 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 3, 5]
def baseStart_2551019 : Nat := 118140960795 + 2551019 * 2 ^ 59
def prefixEnd_2551019 : Nat := 4983230072969 + 3 ^ 40 * 2551019 * 2
def baseEnd_2551019 : Nat := 436632968584019953376861

theorem tailTrace_2551019 : CollatzResearch.WordTrace tailWord_2551019 prefixEnd_2551019 436632968584019953376861 := by
  unfold tailWord_2551019
  simp only [CollatzResearch.WordTrace]
  refine ⟨93043306745101317204104111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62028871163400878136069407 93043306745101317204104111)
  ·
    refine ⟨139564960117651975806156167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93043306745101317204104111 139564960117651975806156167)
    ·
      refine ⟨209347440176477963709234251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139564960117651975806156167 209347440176477963709234251)
      ·
        refine ⟨314021160264716945563851377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209347440176477963709234251 314021160264716945563851377)
        ·
          refine ⟨235515870198537709172888533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314021160264716945563851377 235515870198537709172888533)
          ·
            refine ⟨5519903207778227558739575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 235515870198537709172888533 5519903207778227558739575)
            ·
              refine ⟨8279854811667341338109363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519903207778227558739575 8279854811667341338109363)
              ·
                refine ⟨12419782217501012007164045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279854811667341338109363 12419782217501012007164045)
                ·
                  refine ⟨4657418331562879502686517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12419782217501012007164045 4657418331562879502686517)
                  ·
                    refine ⟨436632968584019953376861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4657418331562879502686517 436632968584019953376861)
                    ·
                      rfl

theorem cell23_2551019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 5].length) (baseStart_2551019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551019 prefixEnd_2551019 := by exact prefixLift 2551019
  have htrace : WordTrace (prefixWord ++ tailWord_2551019) baseStart_2551019 baseEnd_2551019 := by
    simpa [prefixWord, tailWord_2551019, baseEnd_2551019] using wordTrace_append hprefix tailTrace_2551019
  have hstable : (prefixWord ++ tailWord_2551019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551019).length < 2 ^ (prefixWord ++ tailWord_2551019).sum := by decide
  have hdescent : baseEnd_2551019 < baseStart_2551019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551033 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 1, 1, 3]
def baseStart_2551033 : Nat := 118140960795 + 2551033 * 2 ^ 59
def prefixEnd_2551033 : Nat := 4983230072969 + 3 ^ 40 * 2551033 * 2
def baseEnd_2551033 : Nat := 1309906094481222805355519

theorem tailTrace_2551033 : CollatzResearch.WordTrace tailWord_2551033 prefixEnd_2551033 1309906094481222805355519 := by
  unfold tailWord_2551033
  simp only [CollatzResearch.WordTrace]
  refine ⟨93043817367050597595113753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62029211578033731730075835 93043817367050597595113753)
  ·
    refine ⟨69782863025287948196335315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93043817367050597595113753 69782863025287948196335315)
    ·
      refine ⟨104674294537931922294502973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69782863025287948196335315 104674294537931922294502973)
      ·
        refine ⟨39252860451724470860438615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104674294537931922294502973 39252860451724470860438615)
        ·
          refine ⟨58879290677586706290657923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39252860451724470860438615 58879290677586706290657923)
          ·
            refine ⟨88318936016380059435986885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58879290677586706290657923 88318936016380059435986885)
            ·
              refine ⟨16559800503071261144247541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88318936016380059435986885 16559800503071261144247541)
              ·
                refine ⟨1552481297162930732273207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16559800503071261144247541 1552481297162930732273207)
                ·
                  refine ⟨2328721945744396098409811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552481297162930732273207 2328721945744396098409811)
                  ·
                    refine ⟨3493082918616594147614717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328721945744396098409811 3493082918616594147614717)
                    ·
                      refine ⟨1309906094481222805355519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493082918616594147614717 1309906094481222805355519)
                      ·
                        rfl

theorem cell23_2551033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_2551033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551033 prefixEnd_2551033 := by exact prefixLift 2551033
  have htrace : WordTrace (prefixWord ++ tailWord_2551033) baseStart_2551033 baseEnd_2551033 := by
    simpa [prefixWord, tailWord_2551033, baseEnd_2551033] using wordTrace_append hprefix tailTrace_2551033
  have hstable : (prefixWord ++ tailWord_2551033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551033).length < 2 ^ (prefixWord ++ tailWord_2551033).sum := by decide
  have hdescent : baseEnd_2551033 < baseStart_2551033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551066 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_2551066 : Nat := 118140960795 + 2551066 * 2 ^ 59
def prefixEnd_2551066 : Nat := 4983230072969 + 3 ^ 40 * 2551066 * 2
def baseEnd_2551066 : Nat := 436641013114273725414289

theorem tailTrace_2551066 : CollatzResearch.WordTrace tailWord_2551066 prefixEnd_2551066 436641013114273725414289 := by
  unfold tailWord_2551066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261255243982761057766263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62030013983954029487376701 23261255243982761057766263)
  ·
    refine ⟨34891882865974141586649395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23261255243982761057766263 34891882865974141586649395)
    ·
      refine ⟨52337824298961212379974093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34891882865974141586649395 52337824298961212379974093)
      ·
        refine ⟨19626684112110454642490285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52337824298961212379974093 19626684112110454642490285)
        ·
          refine ⟨7360006542041420490933857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19626684112110454642490285 7360006542041420490933857)
          ·
            refine ⟨5520004906531065368200393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7360006542041420490933857 5520004906531065368200393)
            ·
              refine ⟨4140003679898299026150295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520004906531065368200393 4140003679898299026150295)
              ·
                refine ⟨6210005519847448539225443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140003679898299026150295 6210005519847448539225443)
                ·
                  refine ⟨9315008279771172808838165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210005519847448539225443 9315008279771172808838165)
                  ·
                    refine ⟨436641013114273725414289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9315008279771172808838165 436641013114273725414289)
                    ·
                      rfl

theorem cell23_2551066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_2551066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551066 prefixEnd_2551066 := by exact prefixLift 2551066
  have htrace : WordTrace (prefixWord ++ tailWord_2551066) baseStart_2551066 baseEnd_2551066 := by
    simpa [prefixWord, tailWord_2551066, baseEnd_2551066] using wordTrace_append hprefix tailTrace_2551066
  have hstable : (prefixWord ++ tailWord_2551066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551066).length < 2 ^ (prefixWord ++ tailWord_2551066).sum := by decide
  have hdescent : baseEnd_2551066 < baseStart_2551066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551076 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2551076 : Nat := 118140960795 + 2551076 * 2 ^ 59
def prefixEnd_2551076 : Nat := 4983230072969 + 3 ^ 40 * 2551076 * 2
def baseEnd_2551076 : Nat := 1309928174149366137117821

theorem tailTrace_2551076 : CollatzResearch.WordTrace tailWord_2551076 prefixEnd_2551076 1309928174149366137117821 := by
  unfold tailWord_2551076
  simp only [CollatzResearch.WordTrace]
  refine ⟨46522692852947407969464541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62030257137263210625952721 46522692852947407969464541)
  ·
    refine ⟨17446009819855277988549203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46522692852947407969464541 17446009819855277988549203)
    ·
      refine ⟨26169014729782916982823805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446009819855277988549203 26169014729782916982823805)
      ·
        refine ⟨9813380523668593868558927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26169014729782916982823805 9813380523668593868558927)
        ·
          refine ⟨14720070785502890802838391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813380523668593868558927 14720070785502890802838391)
          ·
            refine ⟨22080106178254336204257587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14720070785502890802838391 22080106178254336204257587)
            ·
              refine ⟨33120159267381504306386381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22080106178254336204257587 33120159267381504306386381)
              ·
                refine ⟨12420059725268064114894893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33120159267381504306386381 12420059725268064114894893)
                ·
                  refine ⟨4657522396975524043085585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12420059725268064114894893 4657522396975524043085585)
                  ·
                    refine ⟨3493141797731643032314189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657522396975524043085585 3493141797731643032314189)
                    ·
                      refine ⟨1309928174149366137117821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493141797731643032314189 1309928174149366137117821)
                      ·
                        rfl

theorem cell23_2551076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2551076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551076 prefixEnd_2551076 := by exact prefixLift 2551076
  have htrace : WordTrace (prefixWord ++ tailWord_2551076) baseStart_2551076 baseEnd_2551076 := by
    simpa [prefixWord, tailWord_2551076, baseEnd_2551076] using wordTrace_append hprefix tailTrace_2551076
  have hstable : (prefixWord ++ tailWord_2551076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551076).length < 2 ^ (prefixWord ++ tailWord_2551076).sum := by decide
  have hdescent : baseEnd_2551076 < baseStart_2551076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551090 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_2551090 : Nat := 118140960795 + 2551090 * 2 ^ 59
def prefixEnd_2551090 : Nat := 4983230072969 + 3 ^ 40 * 2551090 * 2
def baseEnd_2551090 : Nat := 1309935362878529082342757

theorem tailTrace_2551090 : CollatzResearch.WordTrace tailWord_2551090 prefixEnd_2551090 1309935362878529082342757 := by
  unfold tailWord_2551090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261474081961024082484681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62030597551896064219959149 23261474081961024082484681)
  ·
    refine ⟨17446105561470768061863511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23261474081961024082484681 17446105561470768061863511)
    ·
      refine ⟨26169158342206152092795267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446105561470768061863511 26169158342206152092795267)
      ·
        refine ⟨39253737513309228139192901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26169158342206152092795267 39253737513309228139192901)
        ·
          refine ⟨7360075783745480276098669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39253737513309228139192901 7360075783745480276098669)
          ·
            refine ⟨2760028418904555103537001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7360075783745480276098669 2760028418904555103537001)
            ·
              refine ⟨2070021314178416327652751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760028418904555103537001 2070021314178416327652751)
              ·
                refine ⟨3105031971267624491479127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070021314178416327652751 3105031971267624491479127)
                ·
                  refine ⟨4657547956901436737218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105031971267624491479127 4657547956901436737218691)
                  ·
                    refine ⟨6986321935352155105828037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4657547956901436737218691 6986321935352155105828037)
                    ·
                      refine ⟨1309935362878529082342757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6986321935352155105828037 1309935362878529082342757)
                      ·
                        rfl

theorem cell23_2551090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_2551090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551090 prefixEnd_2551090 := by exact prefixLift 2551090
  have htrace : WordTrace (prefixWord ++ tailWord_2551090) baseStart_2551090 baseEnd_2551090 := by
    simpa [prefixWord, tailWord_2551090, baseEnd_2551090] using wordTrace_append hprefix tailTrace_2551090
  have hstable : (prefixWord ++ tailWord_2551090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551090).length < 2 ^ (prefixWord ++ tailWord_2551090).sum := by decide
  have hdescent : baseEnd_2551090 < baseStart_2551090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551093 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2551093 : Nat := 118140960795 + 2551093 * 2 ^ 59
def prefixEnd_2551093 : Nat := 4983230072969 + 3 ^ 40 * 2551093 * 2
def baseEnd_2551093 : Nat := 1309936903320492570605243

theorem tailTrace_2551093 : CollatzResearch.WordTrace tailWord_2551093 prefixEnd_2551093 1309936903320492570605243 := by
  unfold tailWord_2551093
  simp only [CollatzResearch.WordTrace]
  refine ⟨93046005746833227842297933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62030670497888818561531955 93046005746833227842297933)
  ·
    refine ⟨34892252155062460440861725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93046005746833227842297933 34892252155062460440861725)
    ·
      refine ⟨13084594558148422665323147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34892252155062460440861725 13084594558148422665323147)
      ·
        refine ⟨19626891837222633997984721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13084594558148422665323147 19626891837222633997984721)
        ·
          refine ⟨14720168877916975498488541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19626891837222633997984721 14720168877916975498488541)
          ·
            refine ⟨5520063329218865811933203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14720168877916975498488541 5520063329218865811933203)
            ·
              refine ⟨8280094993828298717899805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520063329218865811933203 8280094993828298717899805)
              ·
                refine ⟨3105035622685612019212427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8280094993828298717899805 3105035622685612019212427)
                ·
                  refine ⟨4657553434028418028818641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105035622685612019212427 4657553434028418028818641)
                  ·
                    refine ⟨3493165075521313521613981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657553434028418028818641 3493165075521313521613981)
                    ·
                      refine ⟨1309936903320492570605243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493165075521313521613981 1309936903320492570605243)
                      ·
                        rfl

theorem cell23_2551093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2551093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551093 prefixEnd_2551093 := by exact prefixLift 2551093
  have htrace : WordTrace (prefixWord ++ tailWord_2551093) baseStart_2551093 baseEnd_2551093 := by
    simpa [prefixWord, tailWord_2551093, baseEnd_2551093] using wordTrace_append hprefix tailTrace_2551093
  have hstable : (prefixWord ++ tailWord_2551093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551093).length < 2 ^ (prefixWord ++ tailWord_2551093).sum := by decide
  have hdescent : baseEnd_2551093 < baseStart_2551093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551117 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2551117 : Nat := 118140960795 + 2551117 * 2 ^ 59
def prefixEnd_2551117 : Nat := 4983230072969 + 3 ^ 40 * 2551117 * 2
def baseEnd_2551117 : Nat := 436649742285400158901711

theorem tailTrace_2551117 : CollatzResearch.WordTrace tailWord_2551117 prefixEnd_2551117 436649742285400158901711 := by
  unfold tailWord_2551117
  simp only [CollatzResearch.WordTrace]
  refine ⟨93046881098746279941171605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62031254065830853294114403 93046881098746279941171605)
  ·
    refine ⟨4361572551503731872242419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93046881098746279941171605 4361572551503731872242419)
    ·
      refine ⟨6542358827255597808363629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4361572551503731872242419 6542358827255597808363629)
      ·
        refine ⟨2453384560220849178136361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6542358827255597808363629 2453384560220849178136361)
        ·
          refine ⟨1840038420165636883602271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453384560220849178136361 1840038420165636883602271)
          ·
            refine ⟨2760057630248455325403407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840038420165636883602271 2760057630248455325403407)
            ·
              refine ⟨4140086445372682988105111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760057630248455325403407 4140086445372682988105111)
              ·
                refine ⟨6210129668059024482157667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140086445372682988105111 6210129668059024482157667)
                ·
                  refine ⟨9315194502088536723236501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210129668059024482157667 9315194502088536723236501)
                  ·
                    refine ⟨436649742285400158901711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9315194502088536723236501 436649742285400158901711)
                    ·
                      rfl

theorem cell23_2551117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2551117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551117 prefixEnd_2551117 := by exact prefixLift 2551117
  have htrace : WordTrace (prefixWord ++ tailWord_2551117) baseStart_2551117 baseEnd_2551117 := by
    simpa [prefixWord, tailWord_2551117, baseEnd_2551117] using wordTrace_append hprefix tailTrace_2551117
  have hstable : (prefixWord ++ tailWord_2551117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551117).length < 2 ^ (prefixWord ++ tailWord_2551117).sum := by decide
  have hdescent : baseEnd_2551117 < baseStart_2551117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551129 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2551129 : Nat := 118140960795 + 2551129 * 2 ^ 59
def prefixEnd_2551129 : Nat := 4983230072969 + 3 ^ 40 * 2551129 * 2
def baseEnd_2551129 : Nat := 1309955388624054429755077

theorem tailTrace_2551129 : CollatzResearch.WordTrace tailWord_2551129 prefixEnd_2551129 1309955388624054429755077 := by
  unfold tailWord_2551129
  simp only [CollatzResearch.WordTrace]
  refine ⟨93047318774702805990608441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62031545849801870660405627 93047318774702805990608441)
  ·
    refine ⟨69785489081027104492956331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93047318774702805990608441 69785489081027104492956331)
    ·
      refine ⟨104678233621540656739434497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69785489081027104492956331 104678233621540656739434497)
      ·
        refine ⟨78508675216155492554575873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104678233621540656739434497 78508675216155492554575873)
        ·
          refine ⟨58881506412116619415931905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78508675216155492554575873 58881506412116619415931905)
          ·
            refine ⟨44161129809087464561948929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58881506412116619415931905 44161129809087464561948929)
            ·
              refine ⟨33120847356815598421461697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44161129809087464561948929 33120847356815598421461697)
              ·
                refine ⟨24840635517611698816096273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33120847356815598421461697 24840635517611698816096273)
                ·
                  refine ⟨18630476638208774112072205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24840635517611698816096273 18630476638208774112072205)
                  ·
                    refine ⟨6986428739328290292027077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18630476638208774112072205 6986428739328290292027077)
                    ·
                      refine ⟨1309955388624054429755077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6986428739328290292027077 1309955388624054429755077)
                      ·
                        rfl

theorem cell23_2551129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2551129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551129 prefixEnd_2551129 := by exact prefixLift 2551129
  have htrace : WordTrace (prefixWord ++ tailWord_2551129) baseStart_2551129 baseEnd_2551129 := by
    simpa [prefixWord, tailWord_2551129, baseEnd_2551129] using wordTrace_append hprefix tailTrace_2551129
  have hstable : (prefixWord ++ tailWord_2551129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551129).length < 2 ^ (prefixWord ++ tailWord_2551129).sum := by decide
  have hdescent : baseEnd_2551129 < baseStart_2551129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551163 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 4, 2, 2]
def baseStart_2551163 : Nat := 118140960795 + 2551163 * 2 ^ 59
def prefixEnd_2551163 : Nat := 4983230072969 + 3 ^ 40 * 2551163 * 2
def baseEnd_2551163 : Nat := 1309972846966307296729921

theorem tailTrace_2551163 : CollatzResearch.WordTrace tailWord_2551163 prefixEnd_2551163 1309972846966307296729921 := by
  unfold tailWord_2551163
  simp only [CollatzResearch.WordTrace]
  refine ⟨93048558856579629797346143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62032372571053086531564095 93048558856579629797346143)
  ·
    refine ⟨139572838284869444696019215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93048558856579629797346143 139572838284869444696019215)
    ·
      refine ⟨209359257427304167044028823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139572838284869444696019215 209359257427304167044028823)
      ·
        refine ⟨314038886140956250566043235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209359257427304167044028823 314038886140956250566043235)
        ·
          refine ⟨471058329211434375849064853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314038886140956250566043235 471058329211434375849064853)
          ·
            refine ⟨22080859181785986367924915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 471058329211434375849064853 22080859181785986367924915)
            ·
              refine ⟨33121288772678979551887373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22080859181785986367924915 33121288772678979551887373)
              ·
                refine ⟨12420483289754617331957765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33121288772678979551887373 12420483289754617331957765)
                ·
                  refine ⟨2328840616828990749742081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12420483289754617331957765 2328840616828990749742081)
                  ·
                    refine ⟨1746630462621743062306561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328840616828990749742081 1746630462621743062306561)
                    ·
                      refine ⟨1309972846966307296729921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746630462621743062306561 1309972846966307296729921)
                      ·
                        rfl

theorem cell23_2551163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2, 2].length) (baseStart_2551163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551163 prefixEnd_2551163 := by exact prefixLift 2551163
  have htrace : WordTrace (prefixWord ++ tailWord_2551163) baseStart_2551163 baseEnd_2551163 := by
    simpa [prefixWord, tailWord_2551163, baseEnd_2551163] using wordTrace_append hprefix tailTrace_2551163
  have hstable : (prefixWord ++ tailWord_2551163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551163).length < 2 ^ (prefixWord ++ tailWord_2551163).sum := by decide
  have hdescent : baseEnd_2551163 < baseStart_2551163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551180 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_2551180 : Nat := 118140960795 + 2551180 * 2 ^ 59
def prefixEnd_2551180 : Nat := 4983230072969 + 3 ^ 40 * 2551180 * 2
def baseEnd_2551180 : Nat := 1309981576137433730217343

theorem tailTrace_2551180 : CollatzResearch.WordTrace tailWord_2551180 prefixEnd_2551180 1309981576137433730217343 := by
  unfold tailWord_2551180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46524589448759020850357497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62032785931678694467143329 46524589448759020850357497)
  ·
    refine ⟨34893442086569265637768123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46524589448759020850357497 34893442086569265637768123)
    ·
      refine ⟨52340163129853898456652185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34893442086569265637768123 52340163129853898456652185)
      ·
        refine ⟨39255122347390423842489139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52340163129853898456652185 39255122347390423842489139)
        ·
          refine ⟨58882683521085635763733709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39255122347390423842489139 58882683521085635763733709)
          ·
            refine ⟨22081006320407113411400141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58882683521085635763733709 22081006320407113411400141)
            ·
              refine ⟨8280377370152667529275053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22081006320407113411400141 8280377370152667529275053)
              ·
                refine ⟨3105141513807250323478145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8280377370152667529275053 3105141513807250323478145)
                ·
                  refine ⟨2328856135355437742608609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3105141513807250323478145 2328856135355437742608609)
                  ·
                    refine ⟨1746642101516578306956457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328856135355437742608609 1746642101516578306956457)
                    ·
                      refine ⟨1309981576137433730217343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746642101516578306956457 1309981576137433730217343)
                      ·
                        rfl

theorem cell23_2551180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_2551180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551180 prefixEnd_2551180 := by exact prefixLift 2551180
  have htrace : WordTrace (prefixWord ++ tailWord_2551180) baseStart_2551180 baseEnd_2551180 := by
    simpa [prefixWord, tailWord_2551180, baseEnd_2551180] using wordTrace_append hprefix tailTrace_2551180
  have hstable : (prefixWord ++ tailWord_2551180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551180).length < 2 ^ (prefixWord ++ tailWord_2551180).sum := by decide
  have hdescent : baseEnd_2551180 < baseStart_2551180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551253 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2551253 : Nat := 118140960795 + 2551253 * 2 ^ 59
def prefixEnd_2551253 : Nat := 4983230072969 + 3 ^ 40 * 2551253 * 2
def baseEnd_2551253 : Nat := 1310019060225211944604507

theorem tailTrace_2551253 : CollatzResearch.WordTrace tailWord_2551253 prefixEnd_2551253 1310019060225211944604507 := by
  unfold tailWord_2551253
  simp only [CollatzResearch.WordTrace]
  refine ⟨93051841426253575168122413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62034560950835716778748275 93051841426253575168122413)
  ·
    refine ⟨34894440534845090688045905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93051841426253575168122413 34894440534845090688045905)
    ·
      refine ⟨26170830401133818016034429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34894440534845090688045905 26170830401133818016034429)
      ·
        refine ⟨9814061400425181756012911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26170830401133818016034429 9814061400425181756012911)
        ·
          refine ⟨14721092100637772634019367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814061400425181756012911 14721092100637772634019367)
          ·
            refine ⟨22081638150956658951029051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14721092100637772634019367 22081638150956658951029051)
            ·
              refine ⟨33122457226434988426543577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22081638150956658951029051 33122457226434988426543577)
              ·
                refine ⟨24841842919826241319907683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33122457226434988426543577 24841842919826241319907683)
                ·
                  refine ⟨37262764379739361979861525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24841842919826241319907683 37262764379739361979861525)
                  ·
                    refine ⟨1746692080300282592806009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37262764379739361979861525 1746692080300282592806009)
                    ·
                      refine ⟨1310019060225211944604507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746692080300282592806009 1310019060225211944604507)
                      ·
                        rfl

theorem cell23_2551253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2551253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551253 prefixEnd_2551253 := by exact prefixLift 2551253
  have htrace : WordTrace (prefixWord ++ tailWord_2551253) baseStart_2551253 baseEnd_2551253 := by
    simpa [prefixWord, tailWord_2551253, baseEnd_2551253] using wordTrace_append hprefix tailTrace_2551253
  have hstable : (prefixWord ++ tailWord_2551253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551253).length < 2 ^ (prefixWord ++ tailWord_2551253).sum := by decide
  have hdescent : baseEnd_2551253 < baseStart_2551253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551259 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 14]
def baseStart_2551259 : Nat := 118140960795 + 2551259 * 2 ^ 59
def prefixEnd_2551259 : Nat := 4983230072969 + 3 ^ 40 * 2551259 * 2
def baseEnd_2551259 : Nat := 145558015678793213458831

theorem tailTrace_2551259 : CollatzResearch.WordTrace tailWord_2551259 prefixEnd_2551259 145558015678793213458831 := by
  unfold tailWord_2551259
  simp only [CollatzResearch.WordTrace]
  refine ⟨93052060264231838192840831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62034706842821225461893887 93052060264231838192840831)
  ·
    refine ⟨139578090396347757289261247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93052060264231838192840831 139578090396347757289261247)
    ·
      refine ⟨209367135594521635933891871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139578090396347757289261247 209367135594521635933891871)
      ·
        refine ⟨314050703391782453900837807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209367135594521635933891871 314050703391782453900837807)
        ·
          refine ⟨471076055087673680851256711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314050703391782453900837807 471076055087673680851256711)
          ·
            refine ⟨706614082631510521276885067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471076055087673680851256711 706614082631510521276885067)
            ·
              refine ⟨1059921123947265781915327601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706614082631510521276885067 1059921123947265781915327601)
              ·
                refine ⟨794940842960449336436495701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059921123947265781915327601 794940842960449336436495701)
                ·
                  refine ⟨145558015678793213458831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 794940842960449336436495701 145558015678793213458831)
                  ·
                    rfl

theorem cell23_2551259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 14].length) (baseStart_2551259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551259 prefixEnd_2551259 := by exact prefixLift 2551259
  have htrace : WordTrace (prefixWord ++ tailWord_2551259) baseStart_2551259 baseEnd_2551259 := by
    simpa [prefixWord, tailWord_2551259, baseEnd_2551259] using wordTrace_append hprefix tailTrace_2551259
  have hstable : (prefixWord ++ tailWord_2551259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551259).length < 2 ^ (prefixWord ++ tailWord_2551259).sum := by decide
  have hdescent : baseEnd_2551259 < baseStart_2551259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551276 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 6]
def baseStart_2551276 : Nat := 118140960795 + 2551276 * 2 ^ 59
def prefixEnd_2551276 : Nat := 4983230072969 + 3 ^ 40 * 2551276 * 2
def baseEnd_2551276 : Nat := 145558985586696150512989

theorem tailTrace_2551276 : CollatzResearch.WordTrace tailWord_2551276 prefixEnd_2551276 145558985586696150512989 := by
  unfold tailWord_2551276
  simp only [CollatzResearch.WordTrace]
  refine ⟨46526340152585125048104841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62035120203446833397473121 46526340152585125048104841)
  ·
    refine ⟨34894755114438843786078631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46526340152585125048104841 34894755114438843786078631)
    ·
      refine ⟨52342132671658265679117947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894755114438843786078631 52342132671658265679117947)
      ·
        refine ⟨78513199007487398518676921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52342132671658265679117947 78513199007487398518676921)
        ·
          refine ⟨58884899255615548889007691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78513199007487398518676921 58884899255615548889007691)
          ·
            refine ⟨88327348883423323333511537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58884899255615548889007691 88327348883423323333511537)
            ·
              refine ⟨66245511662567492500133653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88327348883423323333511537 66245511662567492500133653)
              ·
                refine ⟨3105258359182851210943765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66245511662567492500133653 3105258359182851210943765)
                ·
                  refine ⟨145558985586696150512989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3105258359182851210943765 145558985586696150512989)
                  ·
                    rfl

theorem cell23_2551276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_2551276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551276 prefixEnd_2551276 := by exact prefixLift 2551276
  have htrace : WordTrace (prefixWord ++ tailWord_2551276) baseStart_2551276 baseEnd_2551276 := by
    simpa [prefixWord, tailWord_2551276, baseEnd_2551276] using wordTrace_append hprefix tailTrace_2551276
  have hstable : (prefixWord ++ tailWord_2551276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551276).length < 2 ^ (prefixWord ++ tailWord_2551276).sum := by decide
  have hdescent : baseEnd_2551276 < baseStart_2551276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551280 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 1, 4]
def baseStart_2551280 : Nat := 118140960795 + 2551280 * 2 ^ 59
def prefixEnd_2551280 : Nat := 4983230072969 + 3 ^ 40 * 2551280 * 2
def baseEnd_2551280 : Nat := 436677641400961112988961

theorem tailTrace_2551280 : CollatzResearch.WordTrace tailWord_2551280 prefixEnd_2551280 436677641400961112988961 := by
  unfold tailWord_2551280
  simp only [CollatzResearch.WordTrace]
  refine ⟨46526413098577879389677647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62035217464770505852903529 46526413098577879389677647)
  ·
    refine ⟨69789619647866819084516471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46526413098577879389677647 69789619647866819084516471)
    ·
      refine ⟨104684429471800228626774707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69789619647866819084516471 104684429471800228626774707)
      ·
        refine ⟨157026644207700342940162061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104684429471800228626774707 157026644207700342940162061)
        ·
          refine ⟨58884991577887628602560773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157026644207700342940162061 58884991577887628602560773)
          ·
            refine ⟨11040935920853930362980145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58884991577887628602560773 11040935920853930362980145)
            ·
              refine ⟨8280701940640447772235109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11040935920853930362980145 8280701940640447772235109)
              ·
                refine ⟨1552631613870083957294083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8280701940640447772235109 1552631613870083957294083)
                ·
                  refine ⟨2328947420805125935941125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552631613870083957294083 2328947420805125935941125)
                  ·
                    refine ⟨436677641400961112988961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2328947420805125935941125 436677641400961112988961)
                    ·
                      rfl

theorem cell23_2551280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 4].length) (baseStart_2551280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551280 prefixEnd_2551280 := by exact prefixLift 2551280
  have htrace : WordTrace (prefixWord ++ tailWord_2551280) baseStart_2551280 baseEnd_2551280 := by
    simpa [prefixWord, tailWord_2551280, baseEnd_2551280] using wordTrace_append hprefix tailTrace_2551280
  have hstable : (prefixWord ++ tailWord_2551280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551280).length < 2 ^ (prefixWord ++ tailWord_2551280).sum := by decide
  have hdescent : baseEnd_2551280 < baseStart_2551280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551313 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_2551313 : Nat := 118140960795 + 2551313 * 2 ^ 59
def prefixEnd_2551313 : Nat := 4983230072969 + 3 ^ 40 * 2551313 * 2
def baseEnd_2551313 : Nat := 1310049869064481709854231

theorem tailTrace_2551313 : CollatzResearch.WordTrace tailWord_2551313 prefixEnd_2551313 1310049869064481709854231 := by
  unfold tailWord_2551313
  simp only [CollatzResearch.WordTrace]
  refine ⟨93054029806036205415306593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62036019870690803610204395 93054029806036205415306593)
  ·
    refine ⟨69790522354527154061479945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93054029806036205415306593 69790522354527154061479945)
    ·
      refine ⟨52342891765895365546109959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69790522354527154061479945 52342891765895365546109959)
      ·
        refine ⟨78514337648843048319164939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52342891765895365546109959 78514337648843048319164939)
        ·
          refine ⟨117771506473264572478747409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78514337648843048319164939 117771506473264572478747409)
          ·
            refine ⟨88328629854948429359060557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117771506473264572478747409 88328629854948429359060557)
            ·
              refine ⟨33123236195605661009647709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88328629854948429359060557 33123236195605661009647709)
              ·
                refine ⟨12421213573352122878617891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33123236195605661009647709 12421213573352122878617891)
                ·
                  refine ⟨18631820360028184317926837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12421213573352122878617891 18631820360028184317926837)
                  ·
                    refine ⟨1746733158752642279805641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18631820360028184317926837 1746733158752642279805641)
                    ·
                      refine ⟨1310049869064481709854231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746733158752642279805641 1310049869064481709854231)
                      ·
                        rfl

theorem cell23_2551313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_2551313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551313 prefixEnd_2551313 := by exact prefixLift 2551313
  have htrace : WordTrace (prefixWord ++ tailWord_2551313) baseStart_2551313 baseEnd_2551313 := by
    simpa [prefixWord, tailWord_2551313, baseEnd_2551313] using wordTrace_append hprefix tailTrace_2551313
  have hstable : (prefixWord ++ tailWord_2551313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551313).length < 2 ^ (prefixWord ++ tailWord_2551313).sum := by decide
  have hdescent : baseEnd_2551313 < baseStart_2551313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551330 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_2551330 : Nat := 118140960795 + 2551330 * 2 ^ 59
def prefixEnd_2551330 : Nat := 4983230072969 + 3 ^ 40 * 2551330 * 2
def baseEnd_2551330 : Nat := 1310058598235608143341653

theorem tailTrace_2551330 : CollatzResearch.WordTrace tailWord_2551330 prefixEnd_2551330 1310058598235608143341653 := by
  unfold tailWord_2551330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23263662461743654329668861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62036433231316411545783629 23263662461743654329668861)
  ·
    refine ⟨8723873423153870373625823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23263662461743654329668861 8723873423153870373625823)
    ·
      refine ⟨13085810134730805560438735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8723873423153870373625823 13085810134730805560438735)
      ·
        refine ⟨19628715202096208340658103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13085810134730805560438735 19628715202096208340658103)
        ·
          refine ⟨29443072803144312510987155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19628715202096208340658103 29443072803144312510987155)
          ·
            refine ⟨44164609204716468766480733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29443072803144312510987155 44164609204716468766480733)
            ·
              refine ⟨16561728451768675787430275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44164609204716468766480733 16561728451768675787430275)
              ·
                refine ⟨24842592677653013681145413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16561728451768675787430275 24842592677653013681145413)
                ·
                  refine ⟨4657986127059940065214765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24842592677653013681145413 4657986127059940065214765)
                  ·
                    refine ⟨1746744797647477524455537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4657986127059940065214765 1746744797647477524455537)
                    ·
                      refine ⟨1310058598235608143341653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746744797647477524455537 1310058598235608143341653)
                      ·
                        rfl

theorem cell23_2551330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_2551330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551330 prefixEnd_2551330 := by exact prefixLift 2551330
  have htrace : WordTrace (prefixWord ++ tailWord_2551330) baseStart_2551330 baseEnd_2551330 := by
    simpa [prefixWord, tailWord_2551330, baseEnd_2551330] using wordTrace_append hprefix tailTrace_2551330
  have hstable : (prefixWord ++ tailWord_2551330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551330).length < 2 ^ (prefixWord ++ tailWord_2551330).sum := by decide
  have hdescent : baseEnd_2551330 < baseStart_2551330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551357 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2551357 : Nat := 118140960795 + 2551357 * 2 ^ 59
def prefixEnd_2551357 : Nat := 4983230072969 + 3 ^ 40 * 2551357 * 2
def baseEnd_2551357 : Nat := 436690820737759845901343

theorem tailTrace_2551357 : CollatzResearch.WordTrace tailWord_2551357 prefixEnd_2551357 436690820737759845901343 := by
  unfold tailWord_2551357
  simp only [CollatzResearch.WordTrace]
  refine ⟨93055634617876800929908325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62037089745251200619938883 93055634617876800929908325)
  ·
    refine ⟨17447931490851900174357811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93055634617876800929908325 17447931490851900174357811)
    ·
      refine ⟨26171897236277850261536717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17447931490851900174357811 26171897236277850261536717)
      ·
        refine ⟨9814461463604193848076269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26171897236277850261536717 9814461463604193848076269)
        ·
          refine ⟨3680423048851572693028601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9814461463604193848076269 3680423048851572693028601)
          ·
            refine ⟨2760317286638679519771451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3680423048851572693028601 2760317286638679519771451)
            ·
              refine ⟨4140475929958019279657177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760317286638679519771451 4140475929958019279657177)
              ·
                refine ⟨3105356947468514459742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140475929958019279657177 3105356947468514459742883)
                ·
                  refine ⟨4658035421202771689614325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105356947468514459742883 4658035421202771689614325)
                  ·
                    refine ⟨436690820737759845901343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4658035421202771689614325 436690820737759845901343)
                    ·
                      rfl

theorem cell23_2551357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2551357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551357 prefixEnd_2551357 := by exact prefixLift 2551357
  have htrace : WordTrace (prefixWord ++ tailWord_2551357) baseStart_2551357 baseEnd_2551357 := by
    simpa [prefixWord, tailWord_2551357, baseEnd_2551357] using wordTrace_append hprefix tailTrace_2551357
  have hstable : (prefixWord ++ tailWord_2551357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551357).length < 2 ^ (prefixWord ++ tailWord_2551357).sum := by decide
  have hdescent : baseEnd_2551357 < baseStart_2551357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551360 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2]
def baseStart_2551360 : Nat := 118140960795 + 2551360 * 2 ^ 59
def prefixEnd_2551360 : Nat := 4983230072969 + 3 ^ 40 * 2551360 * 2
def baseEnd_2551360 : Nat := 1310074002655243025966515

theorem tailTrace_2551360 : CollatzResearch.WordTrace tailWord_2551360 prefixEnd_2551360 1310074002655243025966515 := by
  unfold tailWord_2551360
  simp only [CollatzResearch.WordTrace]
  refine ⟨46527872018432966221133767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62037162691243954961511689 46527872018432966221133767)
  ·
    refine ⟨69791808027649449331700651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46527872018432966221133767 69791808027649449331700651)
    ·
      refine ⟨104687712041474173997550977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69791808027649449331700651 104687712041474173997550977)
      ·
        refine ⟨78515784031105630498163233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104687712041474173997550977 78515784031105630498163233)
        ·
          refine ⟨58886838023329222873622425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78515784031105630498163233 58886838023329222873622425)
          ·
            refine ⟨44165128517496917155216819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58886838023329222873622425 44165128517496917155216819)
            ·
              refine ⟨66247692776245375732825229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44165128517496917155216819 66247692776245375732825229)
              ·
                refine ⟨24842884791092015899809461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66247692776245375732825229 24842884791092015899809461)
                ·
                  refine ⟨2329020449164876490607137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24842884791092015899809461 2329020449164876490607137)
                  ·
                    refine ⟨1746765336873657367955353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329020449164876490607137 1746765336873657367955353)
                    ·
                      refine ⟨1310074002655243025966515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746765336873657367955353 1310074002655243025966515)
                      ·
                        rfl

theorem cell23_2551360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_2551360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551360 prefixEnd_2551360 := by exact prefixLift 2551360
  have htrace : WordTrace (prefixWord ++ tailWord_2551360) baseStart_2551360 baseEnd_2551360 := by
    simpa [prefixWord, tailWord_2551360, baseEnd_2551360] using wordTrace_append hprefix tailTrace_2551360
  have hstable : (prefixWord ++ tailWord_2551360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551360).length < 2 ^ (prefixWord ++ tailWord_2551360).sum := by decide
  have hdescent : baseEnd_2551360 < baseStart_2551360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551393 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_2551393 : Nat := 118140960795 + 2551393 * 2 ^ 59
def prefixEnd_2551393 : Nat := 4983230072969 + 3 ^ 40 * 2551393 * 2
def baseEnd_2551393 : Nat := 1310090947516841396853863

theorem tailTrace_2551393 : CollatzResearch.WordTrace tailWord_2551393 prefixEnd_2551393 1310090947516841396853863 := by
  unfold tailWord_2551393
  simp only [CollatzResearch.WordTrace]
  refine ⟨93056947645746379078218833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62037965097164252718812555 93056947645746379078218833)
  ·
    refine ⟨69792710734309784308664125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93056947645746379078218833 69792710734309784308664125)
    ·
      refine ⟨26172266525366169115749047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69792710734309784308664125 26172266525366169115749047)
      ·
        refine ⟨39258399788049253673623571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26172266525366169115749047 39258399788049253673623571)
        ·
          refine ⟨58887599682073880510435357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39258399788049253673623571 58887599682073880510435357)
          ·
            refine ⟨22082849880777705191413259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58887599682073880510435357 22082849880777705191413259)
            ·
              refine ⟨33124274821166557787119889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22082849880777705191413259 33124274821166557787119889)
              ·
                refine ⟨24843206115874918340339917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33124274821166557787119889 24843206115874918340339917)
                ·
                  refine ⟨9316202293453094377627469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24843206115874918340339917 9316202293453094377627469)
                  ·
                    refine ⟨3493575860044910391610301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9316202293453094377627469 3493575860044910391610301)
                    ·
                      refine ⟨1310090947516841396853863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493575860044910391610301 1310090947516841396853863)
                      ·
                        rfl

theorem cell23_2551393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_2551393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551393 prefixEnd_2551393 := by exact prefixLift 2551393
  have htrace : WordTrace (prefixWord ++ tailWord_2551393) baseStart_2551393 baseEnd_2551393 := by
    simpa [prefixWord, tailWord_2551393, baseEnd_2551393] using wordTrace_append hprefix tailTrace_2551393
  have hstable : (prefixWord ++ tailWord_2551393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551393).length < 2 ^ (prefixWord ++ tailWord_2551393).sum := by decide
  have hdescent : baseEnd_2551393 < baseStart_2551393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551400 : List Nat := [2, 1, 4, 3, 1, 3, 1, 8]
def baseStart_2551400 : Nat := 118140960795 + 2551400 * 2 ^ 59
def prefixEnd_2551400 : Nat := 4983230072969 + 3 ^ 40 * 2551400 * 2
def baseEnd_2551400 : Nat := 48522020069682328498753

theorem tailTrace_2551400 : CollatzResearch.WordTrace tailWord_2551400 prefixEnd_2551400 48522020069682328498753 := by
  unfold tailWord_2551400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46528601478360509636861827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62038135304480679515815769 46528601478360509636861827)
  ·
    refine ⟨69792902217540764455292741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46528601478360509636861827 69792902217540764455292741)
    ·
      refine ⟨13086169165788893335367389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69792902217540764455292741 13086169165788893335367389)
      ·
        refine ⟨4907313437170835000762771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13086169165788893335367389 4907313437170835000762771)
        ·
          refine ⟨7360970155756252501144157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907313437170835000762771 7360970155756252501144157)
          ·
            refine ⟨2760363808408594687929059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7360970155756252501144157 2760363808408594687929059)
            ·
              refine ⟨4140545712612892031893589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760363808408594687929059 4140545712612892031893589)
              ·
                refine ⟨48522020069682328498753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4140545712612892031893589 48522020069682328498753)
                ·
                  rfl

theorem cell23_2551400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 8].length) (baseStart_2551400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551400 prefixEnd_2551400 := by exact prefixLift 2551400
  have htrace : WordTrace (prefixWord ++ tailWord_2551400) baseStart_2551400 baseEnd_2551400 := by
    simpa [prefixWord, tailWord_2551400, baseEnd_2551400] using wordTrace_append hprefix tailTrace_2551400
  have hstable : (prefixWord ++ tailWord_2551400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551400).length < 2 ^ (prefixWord ++ tailWord_2551400).sum := by decide
  have hdescent : baseEnd_2551400 < baseStart_2551400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551410 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2551410 : Nat := 118140960795 + 2551410 * 2 ^ 59
def prefixEnd_2551410 : Nat := 4983230072969 + 3 ^ 40 * 2551410 * 2
def baseEnd_2551410 : Nat := 1310099676687967830341285

theorem tailTrace_2551410 : CollatzResearch.WordTrace tailWord_2551410 prefixEnd_2551410 1310099676687967830341285 := by
  unfold tailWord_2551410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23264391921671197745396921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62038378457789860654391789 23264391921671197745396921)
  ·
    refine ⟨17448293941253398309047691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23264391921671197745396921 17448293941253398309047691)
    ·
      refine ⟨26172440911880097463571537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17448293941253398309047691 26172440911880097463571537)
      ·
        refine ⟨19629330683910073097678653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26172440911880097463571537 19629330683910073097678653)
        ·
          refine ⟨7360999006466277411629495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19629330683910073097678653 7360999006466277411629495)
          ·
            refine ⟨11041498509699416117444243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360999006466277411629495 11041498509699416117444243)
            ·
              refine ⟨16562247764549124176166365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11041498509699416117444243 16562247764549124176166365)
              ·
                refine ⟨6210842911705921566062387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16562247764549124176166365 6210842911705921566062387)
                ·
                  refine ⟨9316264367558882349093581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210842911705921566062387 9316264367558882349093581)
                  ·
                    refine ⟨3493599137834580880910093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9316264367558882349093581 3493599137834580880910093)
                    ·
                      refine ⟨1310099676687967830341285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493599137834580880910093 1310099676687967830341285)
                      ·
                        rfl

theorem cell23_2551410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2551410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551410 prefixEnd_2551410 := by exact prefixLift 2551410
  have htrace : WordTrace (prefixWord ++ tailWord_2551410) baseStart_2551410 baseEnd_2551410 := by
    simpa [prefixWord, tailWord_2551410, baseEnd_2551410] using wordTrace_append hprefix tailTrace_2551410
  have hstable : (prefixWord ++ tailWord_2551410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551410).length < 2 ^ (prefixWord ++ tailWord_2551410).sum := by decide
  have hdescent : baseEnd_2551410 < baseStart_2551410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2551416 : Nat := 118140960795 + 2551416 * 2 ^ 59
def prefixEnd_2551416 : Nat := 4983230072969 + 3 ^ 40 * 2551416 * 2
def baseEnd_2551416 : Nat := 1310102757571894806866257

theorem tailTrace_2551416 : CollatzResearch.WordTrace tailWord_2551416 prefixEnd_2551416 1310102757571894806866257 := by
  unfold tailWord_2551416
  simp only [CollatzResearch.WordTrace]
  refine ⟨46528893262331527003153051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62038524349775369337537401 46528893262331527003153051)
  ·
    refine ⟨69793339893497290504729577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46528893262331527003153051 69793339893497290504729577)
    ·
      refine ⟨52345004920122967878547183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69793339893497290504729577 52345004920122967878547183)
      ·
        refine ⟨78517507380184451817820775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52345004920122967878547183 78517507380184451817820775)
        ·
          refine ⟨117776261070276677726731163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78517507380184451817820775 117776261070276677726731163)
          ·
            refine ⟨176664391605415016590096745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117776261070276677726731163 176664391605415016590096745)
            ·
              refine ⟨132498293704061262442572559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176664391605415016590096745 132498293704061262442572559)
              ·
                refine ⟨198747440556091893663858839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132498293704061262442572559 198747440556091893663858839)
                ·
                  refine ⟨298121160834137840495788259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198747440556091893663858839 298121160834137840495788259)
                  ·
                    refine ⟨447181741251206760743682389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 298121160834137840495788259 447181741251206760743682389)
                    ·
                      refine ⟨1310102757571894806866257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 447181741251206760743682389 1310102757571894806866257)
                      ·
                        rfl

theorem cell23_2551416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2551416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551416 prefixEnd_2551416 := by exact prefixLift 2551416
  have htrace : WordTrace (prefixWord ++ tailWord_2551416) baseStart_2551416 baseEnd_2551416 := by
    simpa [prefixWord, tailWord_2551416, baseEnd_2551416] using wordTrace_append hprefix tailTrace_2551416
  have hstable : (prefixWord ++ tailWord_2551416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551416).length < 2 ^ (prefixWord ++ tailWord_2551416).sum := by decide
  have hdescent : baseEnd_2551416 < baseStart_2551416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551444 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2551444 : Nat := 118140960795 + 2551444 * 2 ^ 59
def prefixEnd_2551444 : Nat := 4983230072969 + 3 ^ 40 * 2551444 * 2
def baseEnd_2551444 : Nat := 1310117135030220697316129

theorem tailTrace_2551444 : CollatzResearch.WordTrace tailWord_2551444 prefixEnd_2551444 1310117135030220697316129 := by
  unfold tailWord_2551444
  simp only [CollatzResearch.WordTrace]
  refine ⟨46529403884280807394162693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62039205179041076525550257 46529403884280807394162693)
  ·
    refine ⟨8724263228302651386405505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46529403884280807394162693 8724263228302651386405505)
    ·
      refine ⟨6543197421226988539804129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8724263228302651386405505 6543197421226988539804129)
      ·
        refine ⟨4907398065920241404853097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6543197421226988539804129 4907398065920241404853097)
        ·
          refine ⟨3680548549440181053639823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4907398065920241404853097 3680548549440181053639823)
          ·
            refine ⟨5520822824160271580459735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680548549440181053639823 5520822824160271580459735)
            ·
              refine ⟨8281234236240407370689603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520822824160271580459735 8281234236240407370689603)
              ·
                refine ⟨12421851354360611056034405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281234236240407370689603 12421851354360611056034405)
                ·
                  refine ⟨2329097128942614573006451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12421851354360611056034405 2329097128942614573006451)
                  ·
                    refine ⟨3493645693413921859509677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329097128942614573006451 3493645693413921859509677)
                    ·
                      refine ⟨1310117135030220697316129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493645693413921859509677 1310117135030220697316129)
                      ·
                        rfl

theorem cell23_2551444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2551444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551444 prefixEnd_2551444 := by exact prefixLift 2551444
  have htrace : WordTrace (prefixWord ++ tailWord_2551444) baseStart_2551444 baseEnd_2551444 := by
    simpa [prefixWord, tailWord_2551444, baseEnd_2551444] using wordTrace_append hprefix tailTrace_2551444
  have hstable : (prefixWord ++ tailWord_2551444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551444).length < 2 ^ (prefixWord ++ tailWord_2551444).sum := by decide
  have hdescent : baseEnd_2551444 < baseStart_2551444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551453 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2551453 : Nat := 118140960795 + 2551453 * 2 ^ 59
def prefixEnd_2551453 : Nat := 4983230072969 + 3 ^ 40 * 2551453 * 2
def baseEnd_2551453 : Nat := 1310121756356111162103587

theorem tailTrace_2551453 : CollatzResearch.WordTrace tailWord_2551453 prefixEnd_2551453 1310121756356111162103587 := by
  unfold tailWord_2551453
  simp only [CollatzResearch.WordTrace]
  refine ⟨93059136025529009325403013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62039424017019339550268675 93059136025529009325403013)
  ·
    refine ⟨17448588004786689248513065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93059136025529009325403013 17448588004786689248513065)
    ·
      refine ⟨13086441003590016936384799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17448588004786689248513065 13086441003590016936384799)
      ·
        refine ⟨19629661505385025404577199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086441003590016936384799 19629661505385025404577199)
        ·
          refine ⟨29444492258077538106865799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19629661505385025404577199 29444492258077538106865799)
          ·
            refine ⟨44166738387116307160298699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29444492258077538106865799 44166738387116307160298699)
            ·
              refine ⟨66250107580674460740448049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44166738387116307160298699 66250107580674460740448049)
              ·
                refine ⟨49687580685505845555336037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66250107580674460740448049 49687580685505845555336037)
                ·
                  refine ⟨9316421378532346041625507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49687580685505845555336037 9316421378532346041625507)
                  ·
                    refine ⟨13974632067798519062438261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9316421378532346041625507 13974632067798519062438261)
                    ·
                      refine ⟨1310121756356111162103587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13974632067798519062438261 1310121756356111162103587)
                      ·
                        rfl

theorem cell23_2551453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2551453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551453 prefixEnd_2551453 := by exact prefixLift 2551453
  have htrace : WordTrace (prefixWord ++ tailWord_2551453) baseStart_2551453 baseEnd_2551453 := by
    simpa [prefixWord, tailWord_2551453, baseEnd_2551453] using wordTrace_append hprefix tailTrace_2551453
  have hstable : (prefixWord ++ tailWord_2551453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551453).length < 2 ^ (prefixWord ++ tailWord_2551453).sum := by decide
  have hdescent : baseEnd_2551453 < baseStart_2551453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551483 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3]
def baseStart_2551483 : Nat := 118140960795 + 2551483 * 2 ^ 59
def prefixEnd_2551483 : Nat := 4983230072969 + 3 ^ 40 * 2551483 * 2
def baseEnd_2551483 : Nat := 1310137160775746044728449

theorem tailTrace_2551483 : CollatzResearch.WordTrace tailWord_2551483 prefixEnd_2551483 1310137160775746044728449 := by
  unfold tailWord_2551483
  simp only [CollatzResearch.WordTrace]
  refine ⟨93060230215420324448995103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62040153476946882965996735 93060230215420324448995103)
  ·
    refine ⟨139590345323130486673492655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93060230215420324448995103 139590345323130486673492655)
    ·
      refine ⟨209385517984695730010238983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139590345323130486673492655 209385517984695730010238983)
      ·
        refine ⟨314078276977043595015358475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209385517984695730010238983 314078276977043595015358475)
        ·
          refine ⟨471117415465565392523037713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314078276977043595015358475 471117415465565392523037713)
          ·
            refine ⟨353338061599174044392278285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471117415465565392523037713 353338061599174044392278285)
            ·
              refine ⟨132501773099690266647104357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353338061599174044392278285 132501773099690266647104357)
              ·
                refine ⟨24844082456191924996332067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132501773099690266647104357 24844082456191924996332067)
                ·
                  refine ⟨37266123684287887494498101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24844082456191924996332067 37266123684287887494498101)
                  ·
                    refine ⟨3493699095401989452609197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37266123684287887494498101 3493699095401989452609197)
                    ·
                      refine ⟨1310137160775746044728449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493699095401989452609197 1310137160775746044728449)
                      ·
                        rfl

theorem cell23_2551483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3].length) (baseStart_2551483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551483 prefixEnd_2551483 := by exact prefixLift 2551483
  have htrace : WordTrace (prefixWord ++ tailWord_2551483) baseStart_2551483 baseEnd_2551483 := by
    simpa [prefixWord, tailWord_2551483, baseEnd_2551483] using wordTrace_append hprefix tailTrace_2551483
  have hstable : (prefixWord ++ tailWord_2551483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551483).length < 2 ^ (prefixWord ++ tailWord_2551483).sum := by decide
  have hdescent : baseEnd_2551483 < baseStart_2551483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551501 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2551501 : Nat := 118140960795 + 2551501 * 2 ^ 59
def prefixEnd_2551501 : Nat := 4983230072969 + 3 ^ 40 * 2551501 * 2
def baseEnd_2551501 : Nat := 1310146403427526974303367

theorem tailTrace_2551501 : CollatzResearch.WordTrace tailWord_2551501 prefixEnd_2551501 1310146403427526974303367 := by
  unfold tailWord_2551501
  simp only [CollatzResearch.WordTrace]
  refine ⟨93060886729355113523150357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62040591152903409015433571 93060886729355113523150357)
  ·
    refine ⟨4362229065438520946397673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93060886729355113523150357 4362229065438520946397673)
    ·
      refine ⟨3271671799078890709798255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4362229065438520946397673 3271671799078890709798255)
      ·
        refine ⟨4907507698618336064697383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271671799078890709798255 4907507698618336064697383)
        ·
          refine ⟨7361261547927504097046075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907507698618336064697383 7361261547927504097046075)
          ·
            refine ⟨11041892321891256145569113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361261547927504097046075 11041892321891256145569113)
            ·
              refine ⟨8281419241418442109176835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11041892321891256145569113 8281419241418442109176835)
              ·
                refine ⟨12422128862127663163765253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281419241418442109176835 12422128862127663163765253)
                ·
                  refine ⟨2329149161648936843205985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12422128862127663163765253 2329149161648936843205985)
                  ·
                    refine ⟨1746861871236702632404489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329149161648936843205985 1746861871236702632404489)
                    ·
                      refine ⟨1310146403427526974303367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1746861871236702632404489 1310146403427526974303367)
                      ·
                        rfl

theorem cell23_2551501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2551501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551501 prefixEnd_2551501 := by exact prefixLift 2551501
  have htrace : WordTrace (prefixWord ++ tailWord_2551501) baseStart_2551501 baseEnd_2551501 := by
    simpa [prefixWord, tailWord_2551501, baseEnd_2551501] using wordTrace_append hprefix tailTrace_2551501
  have hstable : (prefixWord ++ tailWord_2551501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551501).length < 2 ^ (prefixWord ++ tailWord_2551501).sum := by decide
  have hdescent : baseEnd_2551501 < baseStart_2551501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551513 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2551513 : Nat := 118140960795 + 2551513 * 2 ^ 59
def prefixEnd_2551513 : Nat := 4983230072969 + 3 ^ 40 * 2551513 * 2
def baseEnd_2551513 : Nat := 1310152565195380927353311

theorem tailTrace_2551513 : CollatzResearch.WordTrace tailWord_2551513 prefixEnd_2551513 1310152565195380927353311 := by
  unfold tailWord_2551513
  simp only [CollatzResearch.WordTrace]
  refine ⟨93061324405311639572587193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62040882936874426381724795 93061324405311639572587193)
  ·
    refine ⟨69795993303983729679440395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93061324405311639572587193 69795993303983729679440395)
    ·
      refine ⟨104693989955975594519160593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69795993303983729679440395 104693989955975594519160593)
      ·
        refine ⟨78520492466981695889370445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104693989955975594519160593 78520492466981695889370445)
        ·
          refine ⟨29445184675118135958513917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78520492466981695889370445 29445184675118135958513917)
          ·
            refine ⟨11041944253169300984442719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29445184675118135958513917 11041944253169300984442719)
            ·
              refine ⟨16562916379753951476664079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11041944253169300984442719 16562916379753951476664079)
              ·
                refine ⟨24844374569630927214996119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16562916379753951476664079 24844374569630927214996119)
                ·
                  refine ⟨37266561854446390822494179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24844374569630927214996119 37266561854446390822494179)
                  ·
                    refine ⟨55899842781669586233741269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37266561854446390822494179 55899842781669586233741269)
                    ·
                      refine ⟨1310152565195380927353311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55899842781669586233741269 1310152565195380927353311)
                      ·
                        rfl

theorem cell23_2551513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2551513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551513 prefixEnd_2551513 := by exact prefixLift 2551513
  have htrace : WordTrace (prefixWord ++ tailWord_2551513) baseStart_2551513 baseEnd_2551513 := by
    simpa [prefixWord, tailWord_2551513, baseEnd_2551513] using wordTrace_append hprefix tailTrace_2551513
  have hstable : (prefixWord ++ tailWord_2551513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551513).length < 2 ^ (prefixWord ++ tailWord_2551513).sum := by decide
  have hdescent : baseEnd_2551513 < baseStart_2551513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551563 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 8]
def baseStart_2551563 : Nat := 118140960795 + 2551563 * 2 ^ 59
def prefixEnd_2551563 : Nat := 4983230072969 + 3 ^ 40 * 2551563 * 2
def baseEnd_2551563 : Nat := 145575359914233970192009

theorem tailTrace_2551563 : CollatzResearch.WordTrace tailWord_2551563 prefixEnd_2551563 145575359914233970192009 := by
  unfold tailWord_2551563
  simp only [CollatzResearch.WordTrace]
  refine ⟨93063148055130498111907343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62042098703420332074604895 93063148055130498111907343)
  ·
    refine ⟨139594722082695747167861015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93063148055130498111907343 139594722082695747167861015)
    ·
      refine ⟨209392083124043620751791523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139594722082695747167861015 209392083124043620751791523)
      ·
        refine ⟨314088124686065431127687285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209392083124043620751791523 314088124686065431127687285)
        ·
          refine ⟨29445761689318634168220683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 314088124686065431127687285 29445761689318634168220683)
          ·
            refine ⟨44168642533977951252331025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29445761689318634168220683 44168642533977951252331025)
            ·
              refine ⟨33126481900483463439248269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44168642533977951252331025 33126481900483463439248269)
              ·
                refine ⟨12422430712681298789718101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33126481900483463439248269 12422430712681298789718101)
                ·
                  refine ⟨145575359914233970192009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12422430712681298789718101 145575359914233970192009)
                  ·
                    rfl

theorem cell23_2551563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 8].length) (baseStart_2551563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551563 prefixEnd_2551563 := by exact prefixLift 2551563
  have htrace : WordTrace (prefixWord ++ tailWord_2551563) baseStart_2551563 baseEnd_2551563 := by
    simpa [prefixWord, tailWord_2551563, baseEnd_2551563] using wordTrace_append hprefix tailTrace_2551563
  have hstable : (prefixWord ++ tailWord_2551563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551563).length < 2 ^ (prefixWord ++ tailWord_2551563).sum := by decide
  have hdescent : baseEnd_2551563 < baseStart_2551563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551580 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 6]
def baseStart_2551580 : Nat := 118140960795 + 2551580 * 2 ^ 59
def prefixEnd_2551580 : Nat := 4983230072969 + 3 ^ 40 * 2551580 * 2
def baseEnd_2551580 : Nat := 145576329822136907246167

theorem tailTrace_2551580 : CollatzResearch.WordTrace tailWord_2551580 prefixEnd_2551580 145576329822136907246167 := by
  unfold tailWord_2551580
  simp only [CollatzResearch.WordTrace]
  refine ⟨46531884048034455007638097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62042512064045940010184129 46531884048034455007638097)
  ·
    refine ⟨34898913036025841255728573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46531884048034455007638097 34898913036025841255728573)
    ·
      refine ⟨13087092388509690470898215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34898913036025841255728573 13087092388509690470898215)
      ·
        refine ⟨19630638582764535706347323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13087092388509690470898215 19630638582764535706347323)
        ·
          refine ⟨29445957874146803559520985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19630638582764535706347323 29445957874146803559520985)
          ·
            refine ⟨22084468405610102669640739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29445957874146803559520985 22084468405610102669640739)
            ·
              refine ⟨33126702608415154004461109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22084468405610102669640739 33126702608415154004461109)
              ·
                refine ⟨3105628369538920687918229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33126702608415154004461109 3105628369538920687918229)
                ·
                  refine ⟨145576329822136907246167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3105628369538920687918229 145576329822136907246167)
                  ·
                    rfl

theorem cell23_2551580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_2551580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551580 prefixEnd_2551580 := by exact prefixLift 2551580
  have htrace : WordTrace (prefixWord ++ tailWord_2551580) baseStart_2551580 baseEnd_2551580 := by
    simpa [prefixWord, tailWord_2551580, baseEnd_2551580] using wordTrace_append hprefix tailTrace_2551580
  have hstable : (prefixWord ++ tailWord_2551580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551580).length < 2 ^ (prefixWord ++ tailWord_2551580).sum := by decide
  have hdescent : baseEnd_2551580 < baseStart_2551580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551614 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_2551614 : Nat := 118140960795 + 2551614 * 2 ^ 59
def prefixEnd_2551614 : Nat := 4983230072969 + 3 ^ 40 * 2551614 * 2
def baseEnd_2551614 : Nat := 145578269637942781354483

theorem tailTrace_2551614 : CollatzResearch.WordTrace tailWord_2551614 prefixEnd_2551614 145578269637942781354483 := by
  unfold tailWord_2551614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633126022243216727751737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62043338785297155881342597 11633126022243216727751737)
  ·
    refine ⟨8724844516682412545813803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11633126022243216727751737 8724844516682412545813803)
    ·
      refine ⟨13087266775023618818720705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724844516682412545813803 13087266775023618818720705)
      ·
        refine ⟨9815450081267714114040529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13087266775023618818720705 9815450081267714114040529)
        ·
          refine ⟨7361587560950785585530397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9815450081267714114040529 7361587560950785585530397)
          ·
            refine ⟨2760595335356544594573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7361587560950785585530397 2760595335356544594573899)
            ·
              refine ⟨4140893003034816891860849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760595335356544594573899 4140893003034816891860849)
              ·
                refine ⟨3105669752276112668895637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140893003034816891860849 3105669752276112668895637)
                ·
                  refine ⟨145578269637942781354483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3105669752276112668895637 145578269637942781354483)
                  ·
                    rfl

theorem cell23_2551614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_2551614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551614 prefixEnd_2551614 := by exact prefixLift 2551614
  have htrace : WordTrace (prefixWord ++ tailWord_2551614) baseStart_2551614 baseEnd_2551614 := by
    simpa [prefixWord, tailWord_2551614, baseEnd_2551614] using wordTrace_append hprefix tailTrace_2551614
  have hstable : (prefixWord ++ tailWord_2551614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551614).length < 2 ^ (prefixWord ++ tailWord_2551614).sum := by decide
  have hdescent : baseEnd_2551614 < baseStart_2551614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551624 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2551624 : Nat := 118140960795 + 2551624 * 2 ^ 59
def prefixEnd_2551624 : Nat := 4983230072969 + 3 ^ 40 * 2551624 * 2
def baseEnd_2551624 : Nat := 1310209561548029993065301

theorem tailTrace_2551624 : CollatzResearch.WordTrace tailWord_2551624 prefixEnd_2551624 1310209561548029993065301 := by
  unfold tailWord_2551624
  simp only [CollatzResearch.WordTrace]
  refine ⟨46532686453954752764938963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62043581938606337019918617 46532686453954752764938963)
  ·
    refine ⟨69799029680932129147408445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46532686453954752764938963 69799029680932129147408445)
    ·
      refine ⟨26174636130349548430278167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69799029680932129147408445 26174636130349548430278167)
      ·
        refine ⟨39261954195524322645417251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26174636130349548430278167 39261954195524322645417251)
        ·
          refine ⟨58892931293286483968125877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39261954195524322645417251 58892931293286483968125877)
          ·
            refine ⟨5521212308745607872011801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58892931293286483968125877 5521212308745607872011801)
            ·
              refine ⟨4140909231559205904008851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521212308745607872011801 4140909231559205904008851)
              ·
                refine ⟨6211363847338808856013277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140909231559205904008851 6211363847338808856013277)
                ·
                  refine ⟨2329261442752053321004979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6211363847338808856013277 2329261442752053321004979)
                  ·
                    refine ⟨3493892164128079981507469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329261442752053321004979 3493892164128079981507469)
                    ·
                      refine ⟨1310209561548029993065301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3493892164128079981507469 1310209561548029993065301)
                      ·
                        rfl

theorem cell23_2551624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2551624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551624 prefixEnd_2551624 := by exact prefixLift 2551624
  have htrace : WordTrace (prefixWord ++ tailWord_2551624) baseStart_2551624 baseEnd_2551624 := by
    simpa [prefixWord, tailWord_2551624, baseEnd_2551624] using wordTrace_append hprefix tailTrace_2551624
  have hstable : (prefixWord ++ tailWord_2551624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551624).length < 2 ^ (prefixWord ++ tailWord_2551624).sum := by decide
  have hdescent : baseEnd_2551624 < baseStart_2551624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551647 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_2551647 : Nat := 118140960795 + 2551647 * 2 ^ 59
def prefixEnd_2551647 : Nat := 4983230072969 + 3 ^ 40 * 2551647 * 2
def baseEnd_2551647 : Nat := 1310221371603083403077695

theorem tailTrace_2551647 : CollatzResearch.WordTrace tailWord_2551647 prefixEnd_2551647 1310221371603083403077695 := by
  unfold tailWord_2551647
  simp only [CollatzResearch.WordTrace]
  refine ⟨93066211786826180457965195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62044141191217453638643463 93066211786826180457965195)
  ·
    refine ⟨139599317680239270686947793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93066211786826180457965195 139599317680239270686947793)
    ·
      refine ⟨104699488260179453015210845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139599317680239270686947793 104699488260179453015210845)
      ·
        refine ⟨39262308097567294880704067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104699488260179453015210845 39262308097567294880704067)
        ·
          refine ⟨58893462146350942321056101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39262308097567294880704067 58893462146350942321056101)
          ·
            refine ⟨11042524152440801685198019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58893462146350942321056101 11042524152440801685198019)
            ·
              refine ⟨16563786228661202527797029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11042524152440801685198019 16563786228661202527797029)
              ·
                refine ⟨3105709917873975473961943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16563786228661202527797029 3105709917873975473961943)
                ·
                  refine ⟨4658564876810963210942915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105709917873975473961943 4658564876810963210942915)
                  ·
                    refine ⟨6987847315216444816414373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4658564876810963210942915 6987847315216444816414373)
                    ·
                      refine ⟨1310221371603083403077695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6987847315216444816414373 1310221371603083403077695)
                      ·
                        rfl

theorem cell23_2551647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_2551647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551647 prefixEnd_2551647 := by exact prefixLift 2551647
  have htrace : WordTrace (prefixWord ++ tailWord_2551647) baseStart_2551647 baseEnd_2551647 := by
    simpa [prefixWord, tailWord_2551647, baseEnd_2551647] using wordTrace_append hprefix tailTrace_2551647
  have hstable : (prefixWord ++ tailWord_2551647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551647).length < 2 ^ (prefixWord ++ tailWord_2551647).sum := by decide
  have hdescent : baseEnd_2551647 < baseStart_2551647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551687 : List Nat := [1, 1, 4, 2, 4, 1, 2, 8]
def baseStart_2551687 : Nat := 118140960795 + 2551687 * 2 ^ 59
def prefixEnd_2551687 : Nat := 4983230072969 + 3 ^ 40 * 2551687 * 2
def baseEnd_2551687 : Nat := 48527478178861601725093

theorem tailTrace_2551687 : CollatzResearch.WordTrace tailWord_2551687 prefixEnd_2551687 48527478178861601725093 := by
  unfold tailWord_2551687
  simp only [CollatzResearch.WordTrace]
  refine ⟨93067670706681267289421315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62045113804454178192947543 93067670706681267289421315)
  ·
    refine ⟨139601506060021900934131973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93067670706681267289421315 139601506060021900934131973)
    ·
      refine ⟨26175282386254106425149745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139601506060021900934131973 26175282386254106425149745)
      ·
        refine ⟨19631461789690579818862309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26175282386254106425149745 19631461789690579818862309)
        ·
          refine ⟨3680899085566983716036683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19631461789690579818862309 3680899085566983716036683)
          ·
            refine ⟨5521348628350475574055025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680899085566983716036683 5521348628350475574055025)
            ·
              refine ⟨4141011471262856680541269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521348628350475574055025 4141011471262856680541269)
              ·
                refine ⟨48527478178861601725093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4141011471262856680541269 48527478178861601725093)
                ·
                  rfl

theorem cell23_2551687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 8].length) (baseStart_2551687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551687 prefixEnd_2551687 := by exact prefixLift 2551687
  have htrace : WordTrace (prefixWord ++ tailWord_2551687) baseStart_2551687 baseEnd_2551687 := by
    simpa [prefixWord, tailWord_2551687, baseEnd_2551687] using wordTrace_append hprefix tailTrace_2551687
  have hstable : (prefixWord ++ tailWord_2551687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551687).length < 2 ^ (prefixWord ++ tailWord_2551687).sum := by decide
  have hdescent : baseEnd_2551687 < baseStart_2551687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551726 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2551726 : Nat := 118140960795 + 2551726 * 2 ^ 59
def prefixEnd_2551726 : Nat := 4983230072969 + 3 ^ 40 * 2551726 * 2
def baseEnd_2551726 : Nat := 1310261936574788593989833

theorem tailTrace_2551726 : CollatzResearch.WordTrace tailWord_2551726 prefixEnd_2551726 1310261936574788593989833 := by
  unfold tailWord_2551726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633636644192497118761379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62046062102359984633394021 11633636644192497118761379)
  ·
    refine ⟨17450454966288745678142069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11633636644192497118761379 17450454966288745678142069)
    ·
      refine ⟨1635980153089569907325819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17450454966288745678142069 1635980153089569907325819)
      ·
        refine ⟨2453970229634354860988729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635980153089569907325819 2453970229634354860988729)
        ·
          refine ⟨1840477672225766145741547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453970229634354860988729 1840477672225766145741547)
          ·
            refine ⟨2760716508338649218612321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840477672225766145741547 2760716508338649218612321)
            ·
              refine ⟨2070537381253986913959241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760716508338649218612321 2070537381253986913959241)
              ·
                refine ⟨1552903035940490185469431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070537381253986913959241 1552903035940490185469431)
                ·
                  refine ⟨2329354553910735278204147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552903035940490185469431 2329354553910735278204147)
                  ·
                    refine ⟨3494031830866102917306221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329354553910735278204147 3494031830866102917306221)
                    ·
                      refine ⟨1310261936574788593989833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494031830866102917306221 1310261936574788593989833)
                      ·
                        rfl

theorem cell23_2551726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2551726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551726 prefixEnd_2551726 := by exact prefixLift 2551726
  have htrace : WordTrace (prefixWord ++ tailWord_2551726) baseStart_2551726 baseEnd_2551726 := by
    simpa [prefixWord, tailWord_2551726, baseEnd_2551726] using wordTrace_append hprefix tailTrace_2551726
  have hstable : (prefixWord ++ tailWord_2551726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551726).length < 2 ^ (prefixWord ++ tailWord_2551726).sum := by decide
  have hdescent : baseEnd_2551726 < baseStart_2551726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551730 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_2551730 : Nat := 118140960795 + 2551730 * 2 ^ 59
def prefixEnd_2551730 : Nat := 4983230072969 + 3 ^ 40 * 2551730 * 2
def baseEnd_2551730 : Nat := 436754663499135526113271

theorem tailTrace_2551730 : CollatzResearch.WordTrace tailWord_2551730 prefixEnd_2551730 436754663499135526113271 := by
  unfold tailWord_2551730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23267309761381371408309161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62046159363683657088824429 23267309761381371408309161)
  ·
    refine ⟨17450482321036028556231871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23267309761381371408309161 17450482321036028556231871)
    ·
      refine ⟨26175723481554042834347807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17450482321036028556231871 26175723481554042834347807)
      ·
        refine ⟨39263585222331064251521711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26175723481554042834347807 39263585222331064251521711)
        ·
          refine ⟨58895377833496596377282567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39263585222331064251521711 58895377833496596377282567)
          ·
            refine ⟨88343066750244894565923851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58895377833496596377282567 88343066750244894565923851)
            ·
              refine ⟨132514600125367341848885777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88343066750244894565923851 132514600125367341848885777)
              ·
                refine ⟨99385950094025506386664333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132514600125367341848885777 99385950094025506386664333)
                ·
                  refine ⟨37269731285259564894999125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99385950094025506386664333 37269731285259564894999125)
                  ·
                    refine ⟨436754663499135526113271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37269731285259564894999125 436754663499135526113271)
                    ·
                      rfl

theorem cell23_2551730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_2551730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551730 prefixEnd_2551730 := by exact prefixLift 2551730
  have htrace : WordTrace (prefixWord ++ tailWord_2551730) baseStart_2551730 baseEnd_2551730 := by
    simpa [prefixWord, tailWord_2551730, baseEnd_2551730] using wordTrace_append hprefix tailTrace_2551730
  have hstable : (prefixWord ++ tailWord_2551730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551730).length < 2 ^ (prefixWord ++ tailWord_2551730).sum := by decide
  have hdescent : baseEnd_2551730 < baseStart_2551730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551732 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2551732 : Nat := 118140960795 + 2551732 * 2 ^ 59
def prefixEnd_2551732 : Nat := 4983230072969 + 3 ^ 40 * 2551732 * 2
def baseEnd_2551732 : Nat := 1310265017458715570514805

theorem tailTrace_2551732 : CollatzResearch.WordTrace tailWord_2551732 prefixEnd_2551732 1310265017458715570514805 := by
  unfold tailWord_2551732
  simp only [CollatzResearch.WordTrace]
  refine ⟨46534655995759119987404725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62046207994345493316539633 46534655995759119987404725)
  ·
    refine ⟨4362623999602417498819193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46534655995759119987404725 4362623999602417498819193)
    ·
      refine ⟨3271967999701813124114395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4362623999602417498819193 3271967999701813124114395)
      ·
        refine ⟨4907951999552719686171593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271967999701813124114395 4907951999552719686171593)
        ·
          refine ⟨3680963999664539764628695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4907951999552719686171593 3680963999664539764628695)
          ·
            refine ⟨5521445999496809646943043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680963999664539764628695 5521445999496809646943043)
            ·
              refine ⟨8282168999245214470414565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5521445999496809646943043 8282168999245214470414565)
              ·
                refine ⟨1552906687358477713202731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8282168999245214470414565 1552906687358477713202731)
                ·
                  refine ⟨2329360031037716569804097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552906687358477713202731 2329360031037716569804097)
                  ·
                    refine ⟨1747020023278287427353073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329360031037716569804097 1747020023278287427353073)
                    ·
                      refine ⟨1310265017458715570514805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747020023278287427353073 1310265017458715570514805)
                      ·
                        rfl

theorem cell23_2551732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2551732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551732 prefixEnd_2551732 := by exact prefixLift 2551732
  have htrace : WordTrace (prefixWord ++ tailWord_2551732) baseStart_2551732 baseEnd_2551732 := by
    simpa [prefixWord, tailWord_2551732, baseEnd_2551732] using wordTrace_append hprefix tailTrace_2551732
  have hstable : (prefixWord ++ tailWord_2551732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551732).length < 2 ^ (prefixWord ++ tailWord_2551732).sum := by decide
  have hdescent : baseEnd_2551732 < baseStart_2551732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551754 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_2551754 : Nat := 118140960795 + 2551754 * 2 ^ 59
def prefixEnd_2551754 : Nat := 4983230072969 + 3 ^ 40 * 2551754 * 2
def baseEnd_2551754 : Nat := 1310276314033114484439703

theorem tailTrace_2551754 : CollatzResearch.WordTrace tailWord_2551754 prefixEnd_2551754 1310276314033114484439703 := by
  unfold tailWord_2551754
  simp only [CollatzResearch.WordTrace]
  refine ⟨23267528599359634433027579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62046742931625691821406877 23267528599359634433027579)
  ·
    refine ⟨34901292899039451649541369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23267528599359634433027579 34901292899039451649541369)
    ·
      refine ⟨26175969674279588737156027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34901292899039451649541369 26175969674279588737156027)
      ·
        refine ⟨39263954511419383105734041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26175969674279588737156027 39263954511419383105734041)
        ·
          refine ⟨29447965883564537329300531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39263954511419383105734041 29447965883564537329300531)
          ·
            refine ⟨44171948825346805993950797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29447965883564537329300531 44171948825346805993950797)
            ·
              refine ⟨16564480809505052247731549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44171948825346805993950797 16564480809505052247731549)
              ·
                refine ⟨6211680303564394592899331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16564480809505052247731549 6211680303564394592899331)
                ·
                  refine ⟨9317520455346591889348997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6211680303564394592899331 9317520455346591889348997)
                  ·
                    refine ⟨1747035085377485979252937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9317520455346591889348997 1747035085377485979252937)
                    ·
                      refine ⟨1310276314033114484439703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747035085377485979252937 1310276314033114484439703)
                      ·
                        rfl

theorem cell23_2551754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_2551754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551754 prefixEnd_2551754 := by exact prefixLift 2551754
  have htrace : WordTrace (prefixWord ++ tailWord_2551754) baseStart_2551754 baseEnd_2551754 := by
    simpa [prefixWord, tailWord_2551754, baseEnd_2551754] using wordTrace_append hprefix tailTrace_2551754
  have hstable : (prefixWord ++ tailWord_2551754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551754).length < 2 ^ (prefixWord ++ tailWord_2551754).sum := by decide
  have hdescent : baseEnd_2551754 < baseStart_2551754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551760 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 9]
def baseStart_2551760 : Nat := 118140960795 + 2551760 * 2 ^ 59
def prefixEnd_2551760 : Nat := 4983230072969 + 3 ^ 40 * 2551760 * 2
def baseEnd_2551760 : Nat := 145586599435226828996075

theorem tailTrace_2551760 : CollatzResearch.WordTrace tailWord_2551760 prefixEnd_2551760 145586599435226828996075 := by
  unfold tailWord_2551760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46535166617708400378414367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62046888823611200504552489 46535166617708400378414367)
  ·
    refine ⟨69802749926562600567621551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46535166617708400378414367 69802749926562600567621551)
    ·
      refine ⟨104704124889843900851432327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69802749926562600567621551 104704124889843900851432327)
      ·
        refine ⟨157056187334765851277148491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104704124889843900851432327 157056187334765851277148491)
        ·
          refine ⟨235584281002148776915722737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157056187334765851277148491 235584281002148776915722737)
          ·
            refine ⟨176688210751611582686792053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235584281002148776915722737 176688210751611582686792053)
            ·
              refine ⟨16564519757963585876886755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176688210751611582686792053 16564519757963585876886755)
              ·
                refine ⟨24846779636945378815330133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16564519757963585876886755 24846779636945378815330133)
                ·
                  refine ⟨145586599435226828996075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24846779636945378815330133 145586599435226828996075)
                  ·
                    rfl

theorem cell23_2551760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_2551760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551760 prefixEnd_2551760 := by exact prefixLift 2551760
  have htrace : WordTrace (prefixWord ++ tailWord_2551760) baseStart_2551760 baseEnd_2551760 := by
    simpa [prefixWord, tailWord_2551760, baseEnd_2551760] using wordTrace_append hprefix tailTrace_2551760
  have hstable : (prefixWord ++ tailWord_2551760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551760).length < 2 ^ (prefixWord ++ tailWord_2551760).sum := by decide
  have hdescent : baseEnd_2551760 < baseStart_2551760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551827 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_2551827 : Nat := 118140960795 + 2551827 * 2 ^ 59
def prefixEnd_2551827 : Nat := 4983230072969 + 3 ^ 40 * 2551827 * 2
def baseEnd_2551827 : Nat := 1310313798120892698826867

theorem tailTrace_2551827 : CollatzResearch.WordTrace tailWord_2551827 prefixEnd_2551827 1310313798120892698826867 := by
  unfold tailWord_2551827
  simp only [CollatzResearch.WordTrace]
  refine ⟨93072776926174071199517735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62048517950782714133011823 93072776926174071199517735)
  ·
    refine ⟨139609165389261106799276603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93072776926174071199517735 139609165389261106799276603)
    ·
      refine ⟨209413748083891660198914905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139609165389261106799276603 209413748083891660198914905)
      ·
        refine ⟨157060311062918745149186179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209413748083891660198914905 157060311062918745149186179)
        ·
          refine ⟨235590466594378117723779269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157060311062918745149186179 235590466594378117723779269)
          ·
            refine ⟨44173212486445897073208613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235590466594378117723779269 44173212486445897073208613)
            ·
              refine ⟨8282477341208605701226615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44173212486445897073208613 8282477341208605701226615)
              ·
                refine ⟨12423716011812908551839923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8282477341208605701226615 12423716011812908551839923)
                ·
                  refine ⟨18635574017719362827759885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12423716011812908551839923 18635574017719362827759885)
                  ·
                    refine ⟨6988340256644761060409957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18635574017719362827759885 6988340256644761060409957)
                    ·
                      refine ⟨1310313798120892698826867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6988340256644761060409957 1310313798120892698826867)
                      ·
                        rfl

theorem cell23_2551827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_2551827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551827 prefixEnd_2551827 := by exact prefixLift 2551827
  have htrace : WordTrace (prefixWord ++ tailWord_2551827) baseStart_2551827 baseEnd_2551827 := by
    simpa [prefixWord, tailWord_2551827, baseEnd_2551827] using wordTrace_append hprefix tailTrace_2551827
  have hstable : (prefixWord ++ tailWord_2551827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551827).length < 2 ^ (prefixWord ++ tailWord_2551827).sum := by decide
  have hdescent : baseEnd_2551827 < baseStart_2551827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551867 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 6]
def baseStart_2551867 : Nat := 118140960795 + 2551867 * 2 ^ 59
def prefixEnd_2551867 : Nat := 4983230072969 + 3 ^ 40 * 2551867 * 2
def baseEnd_2551867 : Nat := 145592704149674726925187

theorem tailTrace_2551867 : CollatzResearch.WordTrace tailWord_2551867 prefixEnd_2551867 145592704149674726925187 := by
  unfold tailWord_2551867
  simp only [CollatzResearch.WordTrace]
  refine ⟨93074235846029158030973855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62049490564019438687315903 93074235846029158030973855)
  ·
    refine ⟨139611353769043737046460783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93074235846029158030973855 139611353769043737046460783)
    ·
      refine ⟨209417030653565605569691175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139611353769043737046460783 209417030653565605569691175)
      ·
        refine ⟨314125545980348408354536763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209417030653565605569691175 314125545980348408354536763)
        ·
          refine ⟨471188318970522612531805145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314125545980348408354536763 471188318970522612531805145)
          ·
            refine ⟨353391239227891959398853859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471188318970522612531805145 353391239227891959398853859)
            ·
              refine ⟨530086858841837939098280789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353391239227891959398853859 530086858841837939098280789)
              ·
                refine ⟨3105977688526394174403989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 530086858841837939098280789 3105977688526394174403989)
                ·
                  refine ⟨145592704149674726925187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3105977688526394174403989 145592704149674726925187)
                  ·
                    rfl

theorem cell23_2551867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 6].length) (baseStart_2551867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551867 prefixEnd_2551867 := by exact prefixLift 2551867
  have htrace : WordTrace (prefixWord ++ tailWord_2551867) baseStart_2551867 baseEnd_2551867 := by
    simpa [prefixWord, tailWord_2551867, baseEnd_2551867] using wordTrace_append hprefix tailTrace_2551867
  have hstable : (prefixWord ++ tailWord_2551867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551867).length < 2 ^ (prefixWord ++ tailWord_2551867).sum := by decide
  have hdescent : baseEnd_2551867 < baseStart_2551867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551878 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2551878 : Nat := 118140960795 + 2551878 * 2 ^ 59
def prefixEnd_2551878 : Nat := 4983230072969 + 3 ^ 40 * 2551878 * 2
def baseEnd_2551878 : Nat := 1310339985634271999289133

theorem tailTrace_2551878 : CollatzResearch.WordTrace tailWord_2551878 prefixEnd_2551878 1310339985634271999289133 := by
  unfold tailWord_2551878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908582407780915840925759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62049758032659537939749525 2908582407780915840925759)
  ·
    refine ⟨4362873611671373761388639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908582407780915840925759 4362873611671373761388639)
    ·
      refine ⟨6544310417507060642082959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362873611671373761388639 6544310417507060642082959)
      ·
        refine ⟨9816465626260590963124439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544310417507060642082959 9816465626260590963124439)
        ·
          refine ⟨14724698439390886444686659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816465626260590963124439 14724698439390886444686659)
          ·
            refine ⟨22087047659086329667029989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14724698439390886444686659 22087047659086329667029989)
            ·
              refine ⟨4141321436078686812568123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22087047659086329667029989 4141321436078686812568123)
              ·
                refine ⟨6211982154118030218852185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141321436078686812568123 6211982154118030218852185)
                ·
                  refine ⟨4658986615588522664139139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211982154118030218852185 4658986615588522664139139)
                  ·
                    refine ⟨6988479923382783996208709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4658986615588522664139139 6988479923382783996208709)
                    ·
                      refine ⟨1310339985634271999289133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6988479923382783996208709 1310339985634271999289133)
                      ·
                        rfl

theorem cell23_2551878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2551878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551878 prefixEnd_2551878 := by exact prefixLift 2551878
  have htrace : WordTrace (prefixWord ++ tailWord_2551878) baseStart_2551878 baseEnd_2551878 := by
    simpa [prefixWord, tailWord_2551878, baseEnd_2551878] using wordTrace_append hprefix tailTrace_2551878
  have hstable : (prefixWord ++ tailWord_2551878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551878).length < 2 ^ (prefixWord ++ tailWord_2551878).sum := by decide
  have hdescent : baseEnd_2551878 < baseStart_2551878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551901 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 6]
def baseStart_2551901 : Nat := 118140960795 + 2551901 * 2 ^ 59
def prefixEnd_2551901 : Nat := 4983230072969 + 3 ^ 40 * 2551901 * 2
def baseEnd_2551901 : Nat := 145594643965480601033503

theorem tailTrace_2551901 : CollatzResearch.WordTrace tailWord_2551901 prefixEnd_2551901 145594643965480601033503 := by
  unfold tailWord_2551901
  simp only [CollatzResearch.WordTrace]
  refine ⟨93075475927905981837711557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62050317285270654558474371 93075475927905981837711557)
  ·
    refine ⟨17451651736482371594570917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93075475927905981837711557 17451651736482371594570917)
    ·
      refine ⟨3272184700590444673982047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17451651736482371594570917 3272184700590444673982047)
      ·
        refine ⟨4908277050885667010973071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272184700590444673982047 4908277050885667010973071)
        ·
          refine ⟨7362415576328500516459607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908277050885667010973071 7362415576328500516459607)
          ·
            refine ⟨11043623364492750774689411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362415576328500516459607 11043623364492750774689411)
            ·
              refine ⟨16565435046739126162034117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11043623364492750774689411 16565435046739126162034117)
              ·
                refine ⟨3106019071263586155381397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16565435046739126162034117 3106019071263586155381397)
                ·
                  refine ⟨145594643965480601033503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3106019071263586155381397 145594643965480601033503)
                  ·
                    rfl

theorem cell23_2551901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_2551901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551901 prefixEnd_2551901 := by exact prefixLift 2551901
  have htrace : WordTrace (prefixWord ++ tailWord_2551901) baseStart_2551901 baseEnd_2551901 := by
    simpa [prefixWord, tailWord_2551901, baseEnd_2551901] using wordTrace_append hprefix tailTrace_2551901
  have hstable : (prefixWord ++ tailWord_2551901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551901).length < 2 ^ (prefixWord ++ tailWord_2551901).sum := by decide
  have hdescent : baseEnd_2551901 < baseStart_2551901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551911 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2551911 : Nat := 118140960795 + 2551911 * 2 ^ 59
def prefixEnd_2551911 : Nat := 4983230072969 + 3 ^ 40 * 2551911 * 2
def baseEnd_2551911 : Nat := 1310356930495870370176481

theorem tailTrace_2551911 : CollatzResearch.WordTrace tailWord_2551911 prefixEnd_2551911 1310356930495870370176481 := by
  unfold tailWord_2551911
  simp only [CollatzResearch.WordTrace]
  refine ⟨93075840657869753545575587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62050560438579835697050391 93075840657869753545575587)
  ·
    refine ⟨139613760986804630318363381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93075840657869753545575587 139613760986804630318363381)
    ·
      refine ⟨13088790092512934092346567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139613760986804630318363381 13088790092512934092346567)
      ·
        refine ⟨19633185138769401138519851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13088790092512934092346567 19633185138769401138519851)
        ·
          refine ⟨29449777708154101707779777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19633185138769401138519851 29449777708154101707779777)
          ·
            refine ⟨22087333281115576280834833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29449777708154101707779777 22087333281115576280834833)
            ·
              refine ⟨16565499960836682210626125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22087333281115576280834833 16565499960836682210626125)
              ·
                refine ⟨6212062485313755828984797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16565499960836682210626125 6212062485313755828984797)
                ·
                  refine ⟨2329523431992658435869299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6212062485313755828984797 2329523431992658435869299)
                  ·
                    refine ⟨3494285147988987653803949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329523431992658435869299 3494285147988987653803949)
                    ·
                      refine ⟨1310356930495870370176481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494285147988987653803949 1310356930495870370176481)
                      ·
                        rfl

theorem cell23_2551911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2551911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551911 prefixEnd_2551911 := by exact prefixLift 2551911
  have htrace : WordTrace (prefixWord ++ tailWord_2551911) baseStart_2551911 baseEnd_2551911 := by
    simpa [prefixWord, tailWord_2551911, baseEnd_2551911] using wordTrace_append hprefix tailTrace_2551911
  have hstable : (prefixWord ++ tailWord_2551911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551911).length < 2 ^ (prefixWord ++ tailWord_2551911).sum := by decide
  have hdescent : baseEnd_2551911 < baseStart_2551911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551947 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_2551947 : Nat := 118140960795 + 2551947 * 2 ^ 59
def prefixEnd_2551947 : Nat := 4983230072969 + 3 ^ 40 * 2551947 * 2
def baseEnd_2551947 : Nat := 1310375415799432229326315

theorem tailTrace_2551947 : CollatzResearch.WordTrace tailWord_2551947 prefixEnd_2551947 1310375415799432229326315 := by
  unfold tailWord_2551947
  simp only [CollatzResearch.WordTrace]
  refine ⟨93077153685739331693886095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62051435790492887795924063 93077153685739331693886095)
  ·
    refine ⟨139615730528608997540829143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93077153685739331693886095 139615730528608997540829143)
    ·
      refine ⟨209423595792913496311243715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139615730528608997540829143 209423595792913496311243715)
      ·
        refine ⟨314135393689370244466865573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209423595792913496311243715 314135393689370244466865573)
        ·
          refine ⟨58900386316756920837537295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314135393689370244466865573 58900386316756920837537295)
          ·
            refine ⟨88350579475135381256305943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58900386316756920837537295 88350579475135381256305943)
            ·
              refine ⟨132525869212703071884458915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88350579475135381256305943 132525869212703071884458915)
              ·
                refine ⟨198788803819054607826688373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132525869212703071884458915 198788803819054607826688373)
                ·
                  refine ⟨18636450358036369483752035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198788803819054607826688373 18636450358036369483752035)
                  ·
                    refine ⟨27954675537054554225628053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18636450358036369483752035 27954675537054554225628053)
                    ·
                      refine ⟨1310375415799432229326315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27954675537054554225628053 1310375415799432229326315)
                      ·
                        rfl

theorem cell23_2551947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_2551947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551947 prefixEnd_2551947 := by exact prefixLift 2551947
  have htrace : WordTrace (prefixWord ++ tailWord_2551947) baseStart_2551947 baseEnd_2551947 := by
    simpa [prefixWord, tailWord_2551947, baseEnd_2551947] using wordTrace_append hprefix tailTrace_2551947
  have hstable : (prefixWord ++ tailWord_2551947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551947).length < 2 ^ (prefixWord ++ tailWord_2551947).sum := by decide
  have hdescent : baseEnd_2551947 < baseStart_2551947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551957 : List Nat := [1, 3, 2, 1, 1, 1, 14]
def baseStart_2551957 : Nat := 118140960795 + 2551957 * 2 ^ 59
def prefixEnd_2551957 : Nat := 4983230072969 + 3 ^ 40 * 2551957 * 2
def baseEnd_2551957 : Nat := 16177537661802187533349

theorem tailTrace_2551957 : CollatzResearch.WordTrace tailWord_2551957 prefixEnd_2551957 16177537661802187533349 := by
  unfold tailWord_2551957
  simp only [CollatzResearch.WordTrace]
  refine ⟨93077518415703103401750125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62051678943802068934500083 93077518415703103401750125)
  ·
    refine ⟨34904069405888663775656297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93077518415703103401750125 34904069405888663775656297)
    ·
      refine ⟨26178052054416497831742223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34904069405888663775656297 26178052054416497831742223)
      ·
        refine ⟨39267078081624746747613335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26178052054416497831742223 39267078081624746747613335)
        ·
          refine ⟨58900617122437120121420003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39267078081624746747613335 58900617122437120121420003)
          ·
            refine ⟨88350925683655680182130005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58900617122437120121420003 88350925683655680182130005)
            ·
              refine ⟨16177537661802187533349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 88350925683655680182130005 16177537661802187533349)
              ·
                rfl

theorem cell23_2551957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 14].length) (baseStart_2551957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551957 prefixEnd_2551957 := by exact prefixLift 2551957
  have htrace : WordTrace (prefixWord ++ tailWord_2551957) baseStart_2551957 baseEnd_2551957 := by
    simpa [prefixWord, tailWord_2551957, baseEnd_2551957] using wordTrace_append hprefix tailTrace_2551957
  have hstable : (prefixWord ++ tailWord_2551957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551957).length < 2 ^ (prefixWord ++ tailWord_2551957).sum := by decide
  have hdescent : baseEnd_2551957 < baseStart_2551957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551964 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2551964 : Nat := 118140960795 + 2551964 * 2 ^ 59
def prefixEnd_2551964 : Nat := 4983230072969 + 3 ^ 40 * 2551964 * 2
def baseEnd_2551964 : Nat := 1310384144970558662813737

theorem tailTrace_2551964 : CollatzResearch.WordTrace tailWord_2551964 prefixEnd_2551964 1310384144970558662813737 := by
  unfold tailWord_2551964
  simp only [CollatzResearch.WordTrace]
  refine ⟨46538886863338871798627473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62051849151118495731503297 46538886863338871798627473)
  ·
    refine ⟨34904165147504153848970605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46538886863338871798627473 34904165147504153848970605)
    ·
      refine ⟨13089061930314057693363977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34904165147504153848970605 13089061930314057693363977)
      ·
        refine ⟨9816796447735543270022983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13089061930314057693363977 9816796447735543270022983)
        ·
          refine ⟨14725194671603314905034475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816796447735543270022983 14725194671603314905034475)
          ·
            refine ⟨22087792007404972357551713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14725194671603314905034475 22087792007404972357551713)
            ·
              refine ⟨16565844005553729268163785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22087792007404972357551713 16565844005553729268163785)
              ·
                refine ⟨12424383004165296951122839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16565844005553729268163785 12424383004165296951122839)
                ·
                  refine ⟨18636574506247945426684259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12424383004165296951122839 18636574506247945426684259)
                  ·
                    refine ⟨27954861759371918140026389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18636574506247945426684259 27954861759371918140026389)
                    ·
                      refine ⟨1310384144970558662813737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27954861759371918140026389 1310384144970558662813737)
                      ·
                        rfl

theorem cell23_2551964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2551964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551964 prefixEnd_2551964 := by exact prefixLift 2551964
  have htrace : WordTrace (prefixWord ++ tailWord_2551964) baseStart_2551964 baseEnd_2551964 := by
    simpa [prefixWord, tailWord_2551964, baseEnd_2551964] using wordTrace_append hprefix tailTrace_2551964
  have hstable : (prefixWord ++ tailWord_2551964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551964).length < 2 ^ (prefixWord ++ tailWord_2551964).sum := by decide
  have hdescent : baseEnd_2551964 < baseStart_2551964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551968 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2]
def baseStart_2551968 : Nat := 118140960795 + 2551968 * 2 ^ 59
def prefixEnd_2551968 : Nat := 4983230072969 + 3 ^ 40 * 2551968 * 2
def baseEnd_2551968 : Nat := 1310386198893176647163719

theorem tailTrace_2551968 : CollatzResearch.WordTrace tailWord_2551968 prefixEnd_2551968 1310386198893176647163719 := by
  unfold tailWord_2551968
  simp only [CollatzResearch.WordTrace]
  refine ⟨46538959809331626140200279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62051946412442168186933705 46538959809331626140200279)
  ·
    refine ⟨69808439713997439210300419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46538959809331626140200279 69808439713997439210300419)
    ·
      refine ⟨104712659570996158815450629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69808439713997439210300419 104712659570996158815450629)
      ·
        refine ⟨19633623669561779777896993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104712659570996158815450629 19633623669561779777896993)
        ·
          refine ⟨14725217752171334833422745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19633623669561779777896993 14725217752171334833422745)
          ·
            refine ⟨11043913314128501125067059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14725217752171334833422745 11043913314128501125067059)
            ·
              refine ⟨16565869971192751687600589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11043913314128501125067059 16565869971192751687600589)
              ·
                refine ⟨6212201239197281882850221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16565869971192751687600589 6212201239197281882850221)
                ·
                  refine ⟨2329575464698980706068833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6212201239197281882850221 2329575464698980706068833)
                  ·
                    refine ⟨1747181598524235529551625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329575464698980706068833 1747181598524235529551625)
                    ·
                      refine ⟨1310386198893176647163719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747181598524235529551625 1310386198893176647163719)
                      ·
                        rfl

theorem cell23_2551968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_2551968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551968 prefixEnd_2551968 := by exact prefixLift 2551968
  have htrace : WordTrace (prefixWord ++ tailWord_2551968) baseStart_2551968 baseEnd_2551968 := by
    simpa [prefixWord, tailWord_2551968, baseEnd_2551968] using wordTrace_append hprefix tailTrace_2551968
  have hstable : (prefixWord ++ tailWord_2551968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551968).length < 2 ^ (prefixWord ++ tailWord_2551968).sum := by decide
  have hdescent : baseEnd_2551968 < baseStart_2551968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551981 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2551981 : Nat := 118140960795 + 2551981 * 2 ^ 59
def prefixEnd_2551981 : Nat := 4983230072969 + 3 ^ 40 * 2551981 * 2
def baseEnd_2551981 : Nat := 1310392874141685096301159

theorem tailTrace_2551981 : CollatzResearch.WordTrace tailWord_2551981 prefixEnd_2551981 1310392874141685096301159 := by
  unfold tailWord_2551981
  simp only [CollatzResearch.WordTrace]
  refine ⟨93078393767616155500623797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62052262511744103667082531 93078393767616155500623797)
  ·
    refine ⟨8726099415714014578183481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93078393767616155500623797 8726099415714014578183481)
    ·
      refine ⟨6544574561785510933637611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8726099415714014578183481 6544574561785510933637611)
      ·
        refine ⟨9816861842678266400456417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544574561785510933637611 9816861842678266400456417)
        ·
          refine ⟨7362646382008699800342313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9816861842678266400456417 7362646382008699800342313)
          ·
            refine ⟨5521984786506524850256735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7362646382008699800342313 5521984786506524850256735)
            ·
              refine ⟨8282977179759787275385103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5521984786506524850256735 8282977179759787275385103)
              ·
                refine ⟨12424465769639680913077655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8282977179759787275385103 12424465769639680913077655)
                ·
                  refine ⟨18636698654459521369616483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12424465769639680913077655 18636698654459521369616483)
                  ·
                    refine ⟨27955047981689282054424725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18636698654459521369616483 27955047981689282054424725)
                    ·
                      refine ⟨1310392874141685096301159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27955047981689282054424725 1310392874141685096301159)
                      ·
                        rfl

theorem cell23_2551981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2551981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551981 prefixEnd_2551981 := by exact prefixLift 2551981
  have htrace : WordTrace (prefixWord ++ tailWord_2551981) baseStart_2551981 baseEnd_2551981 := by
    simpa [prefixWord, tailWord_2551981, baseEnd_2551981] using wordTrace_append hprefix tailTrace_2551981
  have hstable : (prefixWord ++ tailWord_2551981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551981).length < 2 ^ (prefixWord ++ tailWord_2551981).sum := by decide
  have hdescent : baseEnd_2551981 < baseStart_2551981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551991 : List Nat := [1, 1, 3, 1, 4, 4, 2, 7]
def baseStart_2551991 : Nat := 118140960795 + 2551991 * 2 ^ 59
def prefixEnd_2551991 : Nat := 4983230072969 + 3 ^ 40 * 2551991 * 2
def baseEnd_2551991 : Nat := 48533259590675187302819

theorem tailTrace_2551991 : CollatzResearch.WordTrace tailWord_2551991 prefixEnd_2551991 48533259590675187302819 := by
  unfold tailWord_2551991
  simp only [CollatzResearch.WordTrace]
  refine ⟨93078758497579927208487827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62052505665053284805658551 93078758497579927208487827)
  ·
    refine ⟨139618137746369890812731741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93078758497579927208487827 139618137746369890812731741)
    ·
      refine ⟨52356801654888709054774403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139618137746369890812731741 52356801654888709054774403)
      ·
        refine ⟨78535202482333063582161605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52356801654888709054774403 78535202482333063582161605)
        ·
          refine ⟨14725350465437449421655301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78535202482333063582161605 14725350465437449421655301)
          ·
            refine ⟨2761003212269521766560369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14725350465437449421655301 2761003212269521766560369)
            ·
              refine ⟨2070752409202141324920277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761003212269521766560369 2070752409202141324920277)
              ·
                refine ⟨48533259590675187302819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2070752409202141324920277 48533259590675187302819)
                ·
                  rfl

theorem cell23_2551991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 7].length) (baseStart_2551991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2551991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2551991 prefixEnd_2551991 := by exact prefixLift 2551991
  have htrace : WordTrace (prefixWord ++ tailWord_2551991) baseStart_2551991 baseEnd_2551991 := by
    simpa [prefixWord, tailWord_2551991, baseEnd_2551991] using wordTrace_append hprefix tailTrace_2551991
  have hstable : (prefixWord ++ tailWord_2551991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551991).length < 2 ^ (prefixWord ++ tailWord_2551991).sum := by decide
  have hdescent : baseEnd_2551991 < baseStart_2551991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552018 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2552018 : Nat := 118140960795 + 2552018 * 2 ^ 59
def prefixEnd_2552018 : Nat := 4983230072969 + 3 ^ 40 * 2552018 * 2
def baseEnd_2552018 : Nat := 1310411872925901451538489

theorem tailTrace_2552018 : CollatzResearch.WordTrace tailWord_2552018 prefixEnd_2552018 1310411872925901451538489 := by
  unfold tailWord_2552018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23269935817120527704930177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62053162178988073879813805 23269935817120527704930177)
  ·
    refine ⟨17452451862840395778697633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23269935817120527704930177 17452451862840395778697633)
    ·
      refine ⟨13089338897130296834023225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17452451862840395778697633 13089338897130296834023225)
      ·
        refine ⟨9817004172847722625517419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13089338897130296834023225 9817004172847722625517419)
        ·
          refine ⟨14725506259271583938276129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9817004172847722625517419 14725506259271583938276129)
          ·
            refine ⟨11044129694453687953707097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14725506259271583938276129 11044129694453687953707097)
            ·
              refine ⟨8283097270840265965280323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11044129694453687953707097 8283097270840265965280323)
              ·
                refine ⟨12424645906260398947920485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283097270840265965280323 12424645906260398947920485)
                ·
                  refine ⟨2329621107423824802735091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12424645906260398947920485 2329621107423824802735091)
                  ·
                    refine ⟨3494431661135737204102637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329621107423824802735091 3494431661135737204102637)
                    ·
                      refine ⟨1310411872925901451538489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494431661135737204102637 1310411872925901451538489)
                      ·
                        rfl

theorem cell23_2552018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2552018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552018 prefixEnd_2552018 := by exact prefixLift 2552018
  have htrace : WordTrace (prefixWord ++ tailWord_2552018) baseStart_2552018 baseEnd_2552018 := by
    simpa [prefixWord, tailWord_2552018, baseEnd_2552018] using wordTrace_append hprefix tailTrace_2552018
  have hstable : (prefixWord ++ tailWord_2552018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552018).length < 2 ^ (prefixWord ++ tailWord_2552018).sum := by decide
  have hdescent : baseEnd_2552018 < baseStart_2552018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552044 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2552044 : Nat := 118140960795 + 2552044 * 2 ^ 59
def prefixEnd_2552044 : Nat := 4983230072969 + 3 ^ 40 * 2552044 * 2
def baseEnd_2552044 : Nat := 1310425223422918349813369

theorem tailTrace_2552044 : CollatzResearch.WordTrace tailWord_2552044 prefixEnd_2552044 1310425223422918349813369 := by
  unfold tailWord_2552044
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540345783193958630083593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62053794377591944840111457 46540345783193958630083593)
  ·
    refine ⟨34905259337395468972562695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46540345783193958630083593 34905259337395468972562695)
    ·
      refine ⟨52357889006093203458844043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34905259337395468972562695 52357889006093203458844043)
      ·
        refine ⟨78536833509139805188266065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52357889006093203458844043 78536833509139805188266065)
        ·
          refine ⟨58902625131854853891199549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78536833509139805188266065 58902625131854853891199549)
          ·
            refine ⟨22088484424445570209199831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58902625131854853891199549 22088484424445570209199831)
            ·
              refine ⟨33132726636668355313799747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22088484424445570209199831 33132726636668355313799747)
              ·
                refine ⟨49699089955002532970699621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33132726636668355313799747 49699089955002532970699621)
                ·
                  refine ⟨9318579366562974932006179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49699089955002532970699621 9318579366562974932006179)
                  ·
                    refine ⟨13977869049844462398009269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9318579366562974932006179 13977869049844462398009269)
                    ·
                      refine ⟨1310425223422918349813369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13977869049844462398009269 1310425223422918349813369)
                      ·
                        rfl

theorem cell23_2552044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2552044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552044 prefixEnd_2552044 := by exact prefixLift 2552044
  have htrace : WordTrace (prefixWord ++ tailWord_2552044) baseStart_2552044 baseEnd_2552044 := by
    simpa [prefixWord, tailWord_2552044, baseEnd_2552044] using wordTrace_append hprefix tailTrace_2552044
  have hstable : (prefixWord ++ tailWord_2552044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552044).length < 2 ^ (prefixWord ++ tailWord_2552044).sum := by decide
  have hdescent : baseEnd_2552044 < baseStart_2552044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552045 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2552045 : Nat := 118140960795 + 2552045 * 2 ^ 59
def prefixEnd_2552045 : Nat := 4983230072969 + 3 ^ 40 * 2552045 * 2
def baseEnd_2552045 : Nat := 1310425736903572845900865

theorem tailTrace_2552045 : CollatzResearch.WordTrace tailWord_2552045 prefixEnd_2552045 1310425736903572845900865 := by
  unfold tailWord_2552045
  simp only [CollatzResearch.WordTrace]
  refine ⟨93080728039384294430953589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62053818692922862953969059 93080728039384294430953589)
  ·
    refine ⟨8726318253692277602901899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93080728039384294430953589 8726318253692277602901899)
    ·
      refine ⟨13089477380538416404352849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8726318253692277602901899 13089477380538416404352849)
      ·
        refine ⟨9817108035403812303264637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13089477380538416404352849 9817108035403812303264637)
        ·
          refine ⟨3681415513276429613724239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9817108035403812303264637 3681415513276429613724239)
          ·
            refine ⟨5522123269914644420586359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681415513276429613724239 5522123269914644420586359)
            ·
              refine ⟨8283184904871966630879539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522123269914644420586359 8283184904871966630879539)
              ·
                refine ⟨12424777357307949946319309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283184904871966630879539 12424777357307949946319309)
                ·
                  refine ⟨4659291508990481229869741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12424777357307949946319309 4659291508990481229869741)
                  ·
                    refine ⟨1747234315871430461201153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4659291508990481229869741 1747234315871430461201153)
                    ·
                      refine ⟨1310425736903572845900865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747234315871430461201153 1310425736903572845900865)
                      ·
                        rfl

theorem cell23_2552045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2552045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552045 prefixEnd_2552045 := by exact prefixLift 2552045
  have htrace : WordTrace (prefixWord ++ tailWord_2552045) baseStart_2552045 baseEnd_2552045 := by
    simpa [prefixWord, tailWord_2552045, baseEnd_2552045] using wordTrace_append hprefix tailTrace_2552045
  have hstable : (prefixWord ++ tailWord_2552045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552045).length < 2 ^ (prefixWord ++ tailWord_2552045).sum := by decide
  have hdescent : baseEnd_2552045 < baseStart_2552045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552058 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_2552058 : Nat := 118140960795 + 2552058 * 2 ^ 59
def prefixEnd_2552058 : Nat := 4983230072969 + 3 ^ 40 * 2552058 * 2
def baseEnd_2552058 : Nat := 1310432412152081295038305

theorem tailTrace_2552058 : CollatzResearch.WordTrace tailWord_2552058 prefixEnd_2552058 1310432412152081295038305 := by
  unfold tailWord_2552058
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270300547084299412794207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62054134792224798434117885 23270300547084299412794207)
  ·
    refine ⟨34905450820626449119191311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23270300547084299412794207 34905450820626449119191311)
    ·
      refine ⟨52358176230939673678786967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34905450820626449119191311 52358176230939673678786967)
      ·
        refine ⟨78537264346409510518180451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52358176230939673678786967 78537264346409510518180451)
        ·
          refine ⟨117805896519614265777270677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78537264346409510518180451 117805896519614265777270677)
          ·
            refine ⟨5522151399356918708309563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117805896519614265777270677 5522151399356918708309563)
            ·
              refine ⟨8283227099035378062464345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522151399356918708309563 8283227099035378062464345)
              ·
                refine ⟨6212420324276533546848259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283227099035378062464345 6212420324276533546848259)
                ·
                  refine ⟨9318630486414800320272389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6212420324276533546848259 9318630486414800320272389)
                  ·
                    refine ⟨1747243216202775060051073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9318630486414800320272389 1747243216202775060051073)
                    ·
                      refine ⟨1310432412152081295038305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747243216202775060051073 1310432412152081295038305)
                      ·
                        rfl

theorem cell23_2552058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_2552058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552058 prefixEnd_2552058 := by exact prefixLift 2552058
  have htrace : WordTrace (prefixWord ++ tailWord_2552058) baseStart_2552058 baseEnd_2552058 := by
    simpa [prefixWord, tailWord_2552058, baseEnd_2552058] using wordTrace_append hprefix tailTrace_2552058
  have hstable : (prefixWord ++ tailWord_2552058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552058).length < 2 ^ (prefixWord ++ tailWord_2552058).sum := by decide
  have hdescent : baseEnd_2552058 < baseStart_2552058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552062 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2552062 : Nat := 118140960795 + 2552062 * 2 ^ 59
def prefixEnd_2552062 : Nat := 4983230072969 + 3 ^ 40 * 2552062 * 2
def baseEnd_2552062 : Nat := 1310434466074699279388287

theorem tailTrace_2552062 : CollatzResearch.WordTrace tailWord_2552062 prefixEnd_2552062 1310434466074699279388287 := by
  unfold tailWord_2552062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635168510040338291790305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62054232053548470889548293 11635168510040338291790305)
  ·
    refine ⟨8726376382530253718842729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11635168510040338291790305 8726376382530253718842729)
    ·
      refine ⟨6544782286897690289132047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8726376382530253718842729 6544782286897690289132047)
      ·
        refine ⟨9817173430346535433698071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544782286897690289132047 9817173430346535433698071)
        ·
          refine ⟨14725760145519803150547107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9817173430346535433698071 14725760145519803150547107)
          ·
            refine ⟨22088640218279704725820661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14725760145519803150547107 22088640218279704725820661)
            ·
              refine ⟨2070810020463722318045687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22088640218279704725820661 2070810020463722318045687)
              ·
                refine ⟨3106215030695583477068531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070810020463722318045687 3106215030695583477068531)
                ·
                  refine ⟨4659322546043375215602797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106215030695583477068531 4659322546043375215602797)
                  ·
                    refine ⟨1747245954766265705851049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4659322546043375215602797 1747245954766265705851049)
                    ·
                      refine ⟨1310434466074699279388287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747245954766265705851049 1310434466074699279388287)
                      ·
                        rfl

theorem cell23_2552062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2552062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552062 prefixEnd_2552062 := by exact prefixLift 2552062
  have htrace : WordTrace (prefixWord ++ tailWord_2552062) baseStart_2552062 baseEnd_2552062 := by
    simpa [prefixWord, tailWord_2552062, baseEnd_2552062] using wordTrace_append hprefix tailTrace_2552062
  have hstable : (prefixWord ++ tailWord_2552062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552062).length < 2 ^ (prefixWord ++ tailWord_2552062).sum := by decide
  have hdescent : baseEnd_2552062 < baseStart_2552062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552074 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2552074 : Nat := 118140960795 + 2552074 * 2 ^ 59
def prefixEnd_2552074 : Nat := 4983230072969 + 3 ^ 40 * 2552074 * 2
def baseEnd_2552074 : Nat := 1310440627842553232438231

theorem tailTrace_2552074 : CollatzResearch.WordTrace tailWord_2552074 prefixEnd_2552074 1310440627842553232438231 := by
  unfold tailWord_2552074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270446439069808095939819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62054523837519488255839517 23270446439069808095939819)
  ·
    refine ⟨34905669658604712143909729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23270446439069808095939819 34905669658604712143909729)
    ·
      refine ⟨26179252243953534107932297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34905669658604712143909729 26179252243953534107932297)
      ·
        refine ⟨19634439182965150580949223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26179252243953534107932297 19634439182965150580949223)
        ·
          refine ⟨29451658774447725871423835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19634439182965150580949223 29451658774447725871423835)
          ·
            refine ⟨44177488161671588807135753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29451658774447725871423835 44177488161671588807135753)
            ·
              refine ⟨33133116121253691605351815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44177488161671588807135753 33133116121253691605351815)
              ·
                refine ⟨49699674181880537408027723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33133116121253691605351815 49699674181880537408027723)
                ·
                  refine ⟨74549511272820806112041585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49699674181880537408027723 74549511272820806112041585)
                  ·
                    refine ⟨55912133454615604584031189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74549511272820806112041585 55912133454615604584031189)
                    ·
                      refine ⟨1310440627842553232438231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55912133454615604584031189 1310440627842553232438231)
                      ·
                        rfl

theorem cell23_2552074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2552074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552074 prefixEnd_2552074 := by exact prefixLift 2552074
  have htrace : WordTrace (prefixWord ++ tailWord_2552074) baseStart_2552074 baseEnd_2552074 := by
    simpa [prefixWord, tailWord_2552074, baseEnd_2552074] using wordTrace_append hprefix tailTrace_2552074
  have hstable : (prefixWord ++ tailWord_2552074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552074).length < 2 ^ (prefixWord ++ tailWord_2552074).sum := by decide
  have hdescent : baseEnd_2552074 < baseStart_2552074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552075 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 2, 2, 2]
def baseStart_2552075 : Nat := 118140960795 + 2552075 * 2 ^ 59
def prefixEnd_2552075 : Nat := 4983230072969 + 3 ^ 40 * 2552075 * 2
def baseEnd_2552075 : Nat := 1310441141323207728525727

theorem tailTrace_2552075 : CollatzResearch.WordTrace tailWord_2552075 prefixEnd_2552075 1310441141323207728525727 := by
  unfold tailWord_2552075
  simp only [CollatzResearch.WordTrace]
  refine ⟨93081822229275609554545679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62054548152850406369697119 93081822229275609554545679)
  ·
    refine ⟨139622733343913414331818519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93081822229275609554545679 139622733343913414331818519)
    ·
      refine ⟨209434100015870121497727779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139622733343913414331818519 209434100015870121497727779)
      ·
        refine ⟨314151150023805182246591669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209434100015870121497727779 314151150023805182246591669)
        ·
          refine ⟨29451670314731735835617969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 314151150023805182246591669 29451670314731735835617969)
          ·
            refine ⟨22088752736048801876713477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29451670314731735835617969 22088752736048801876713477)
            ·
              refine ⟨4141641138009150351883777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22088752736048801876713477 4141641138009150351883777)
              ·
                refine ⟨3106230853506862763912833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4141641138009150351883777 3106230853506862763912833)
                ·
                  refine ⟨2329673140130147072934625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106230853506862763912833 2329673140130147072934625)
                  ·
                    refine ⟨1747254855097610304700969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329673140130147072934625 1747254855097610304700969)
                    ·
                      refine ⟨1310441141323207728525727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747254855097610304700969 1310441141323207728525727)
                      ·
                        rfl

theorem cell23_2552075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2, 2].length) (baseStart_2552075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552075 prefixEnd_2552075 := by exact prefixLift 2552075
  have htrace : WordTrace (prefixWord ++ tailWord_2552075) baseStart_2552075 baseEnd_2552075 := by
    simpa [prefixWord, tailWord_2552075, baseEnd_2552075] using wordTrace_append hprefix tailTrace_2552075
  have hstable : (prefixWord ++ tailWord_2552075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552075).length < 2 ^ (prefixWord ++ tailWord_2552075).sum := by decide
  have hdescent : baseEnd_2552075 < baseStart_2552075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552111 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 2, 5]
def baseStart_2552111 : Nat := 118140960795 + 2552111 * 2 ^ 59
def prefixEnd_2552111 : Nat := 4983230072969 + 3 ^ 40 * 2552111 * 2
def baseEnd_2552111 : Nat := 436819875542256529225187

theorem tailTrace_2552111 : CollatzResearch.WordTrace tailWord_2552111 prefixEnd_2552111 436819875542256529225187 := by
  unfold tailWord_2552111
  simp only [CollatzResearch.WordTrace]
  refine ⟨93083135257145187702856187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62055423504763458468570791 93083135257145187702856187)
  ·
    refine ⟨139624702885717781554284281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93083135257145187702856187 139624702885717781554284281)
    ·
      refine ⟨104718527164288336165713211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139624702885717781554284281 104718527164288336165713211)
      ·
        refine ⟨157077790746432504248569817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104718527164288336165713211 157077790746432504248569817)
        ·
          refine ⟨117808343059824378186427363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157077790746432504248569817 117808343059824378186427363)
          ·
            refine ⟨176712514589736567279641045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117808343059824378186427363 176712514589736567279641045)
            ·
              refine ⟨4141699560696950795616587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176712514589736567279641045 4141699560696950795616587)
              ·
                refine ⟨6212549341045426193424881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141699560696950795616587 6212549341045426193424881)
                ·
                  refine ⟨4659412005784069645068661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212549341045426193424881 4659412005784069645068661)
                  ·
                    refine ⟨436819875542256529225187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4659412005784069645068661 436819875542256529225187)
                    ·
                      rfl

theorem cell23_2552111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_2552111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552111 prefixEnd_2552111 := by exact prefixLift 2552111
  have htrace : WordTrace (prefixWord ++ tailWord_2552111) baseStart_2552111 baseEnd_2552111 := by
    simpa [prefixWord, tailWord_2552111, baseEnd_2552111] using wordTrace_append hprefix tailTrace_2552111
  have hstable : (prefixWord ++ tailWord_2552111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552111).length < 2 ^ (prefixWord ++ tailWord_2552111).sum := by decide
  have hdescent : baseEnd_2552111 < baseStart_2552111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552131 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4]
def baseStart_2552131 : Nat := 118140960795 + 2552131 * 2 ^ 59
def prefixEnd_2552131 : Nat := 4983230072969 + 3 ^ 40 * 2552131 * 2
def baseEnd_2552131 : Nat := 1310469896239859509425469

theorem tailTrace_2552131 : CollatzResearch.WordTrace tailWord_2552131 prefixEnd_2552131 1310469896239859509425469 := by
  unfold tailWord_2552131
  simp only [CollatzResearch.WordTrace]
  refine ⟨93083864717072731118584247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62055909811381820745722831 93083864717072731118584247)
  ·
    refine ⟨139625797075609096677876371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93083864717072731118584247 139625797075609096677876371)
    ·
      refine ⟨209438695613413645016814557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139625797075609096677876371 209438695613413645016814557)
      ·
        refine ⟨78539510855030116881305459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209438695613413645016814557 78539510855030116881305459)
        ·
          refine ⟨117809266282545175321958189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78539510855030116881305459 117809266282545175321958189)
          ·
            refine ⟨44178474855954440745734321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117809266282545175321958189 44178474855954440745734321)
            ·
              refine ⟨33133856141965830559300741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44178474855954440745734321 33133856141965830559300741)
              ·
                refine ⟨6212598026618593229868889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33133856141965830559300741 6212598026618593229868889)
                ·
                  refine ⟨4659448519963944922401667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212598026618593229868889 4659448519963944922401667)
                  ·
                    refine ⟨6989172779945917383602501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659448519963944922401667 6989172779945917383602501)
                    ·
                      refine ⟨1310469896239859509425469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6989172779945917383602501 1310469896239859509425469)
                      ·
                        rfl

theorem cell23_2552131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_2552131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552131 prefixEnd_2552131 := by exact prefixLift 2552131
  have htrace : WordTrace (prefixWord ++ tailWord_2552131) baseStart_2552131 baseEnd_2552131 := by
    simpa [prefixWord, tailWord_2552131, baseEnd_2552131] using wordTrace_append hprefix tailTrace_2552131
  have hstable : (prefixWord ++ tailWord_2552131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552131).length < 2 ^ (prefixWord ++ tailWord_2552131).sum := by decide
  have hdescent : baseEnd_2552131 < baseStart_2552131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552151 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2552151 : Nat := 118140960795 + 2552151 * 2 ^ 59
def prefixEnd_2552151 : Nat := 4983230072969 + 3 ^ 40 * 2552151 * 2
def baseEnd_2552151 : Nat := 1310480165852949431175377

theorem tailTrace_2552151 : CollatzResearch.WordTrace tailWord_2552151 prefixEnd_2552151 1310480165852949431175377 := by
  unfold tailWord_2552151
  simp only [CollatzResearch.WordTrace]
  refine ⟨93084594177000274534312307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62056396118000183022874871 93084594177000274534312307)
  ·
    refine ⟨139626891265500411801468461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93084594177000274534312307 139626891265500411801468461)
    ·
      refine ⟨52360084224562654425550673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139626891265500411801468461 52360084224562654425550673)
      ·
        refine ⟨39270063168421990819163005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52360084224562654425550673 39270063168421990819163005)
        ·
          refine ⟨14726273688158246557186127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39270063168421990819163005 14726273688158246557186127)
          ·
            refine ⟨22089410532237369835779191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14726273688158246557186127 22089410532237369835779191)
            ·
              refine ⟨33134115798356054753668787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22089410532237369835779191 33134115798356054753668787)
              ·
                refine ⟨49701173697534082130503181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33134115798356054753668787 49701173697534082130503181)
                ·
                  refine ⟨18637940136575280798938693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49701173697534082130503181 18637940136575280798938693)
                  ·
                    refine ⟨3494613775607865149801005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18637940136575280798938693 3494613775607865149801005)
                    ·
                      refine ⟨1310480165852949431175377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494613775607865149801005 1310480165852949431175377)
                      ·
                        rfl

theorem cell23_2552151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2552151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552151 prefixEnd_2552151 := by exact prefixLift 2552151
  have htrace : WordTrace (prefixWord ++ tailWord_2552151) baseStart_2552151 baseEnd_2552151 := by
    simpa [prefixWord, tailWord_2552151, baseEnd_2552151] using wordTrace_append hprefix tailTrace_2552151
  have hstable : (prefixWord ++ tailWord_2552151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552151).length < 2 ^ (prefixWord ++ tailWord_2552151).sum := by decide
  have hdescent : baseEnd_2552151 < baseStart_2552151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552168 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2552168 : Nat := 118140960795 + 2552168 * 2 ^ 59
def prefixEnd_2552168 : Nat := 4983230072969 + 3 ^ 40 * 2552168 * 2
def baseEnd_2552168 : Nat := 1310488895024075864662799

theorem tailTrace_2552168 : CollatzResearch.WordTrace tailWord_2552168 prefixEnd_2552168 1310488895024075864662799 := by
  unfold tailWord_2552168
  simp only [CollatzResearch.WordTrace]
  refine ⟨46542607108969343218840579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62056809478625790958454105 46542607108969343218840579)
  ·
    refine ⟨69813910663454014828260869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46542607108969343218840579 69813910663454014828260869)
    ·
      refine ⟨13090108249397627780298913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69813910663454014828260869 13090108249397627780298913)
      ·
        refine ⟨9817581187048220835224185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13090108249397627780298913 9817581187048220835224185)
        ·
          refine ⟨7363185890286165626418139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9817581187048220835224185 7363185890286165626418139)
          ·
            refine ⟨11044778835429248439627209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363185890286165626418139 11044778835429248439627209)
            ·
              refine ⟨8283584126571936329720407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11044778835429248439627209 8283584126571936329720407)
              ·
                refine ⟨12425376189857904494580611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283584126571936329720407 12425376189857904494580611)
                ·
                  refine ⟨18638064284786856741870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12425376189857904494580611 18638064284786856741870917)
                  ·
                    refine ⟨3494637053397535639100797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18638064284786856741870917 3494637053397535639100797)
                    ·
                      refine ⟨1310488895024075864662799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494637053397535639100797 1310488895024075864662799)
                      ·
                        rfl

theorem cell23_2552168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2552168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552168 prefixEnd_2552168 := by exact prefixLift 2552168
  have htrace : WordTrace (prefixWord ++ tailWord_2552168) baseStart_2552168 baseEnd_2552168 := by
    simpa [prefixWord, tailWord_2552168, baseEnd_2552168] using wordTrace_append hprefix tailTrace_2552168
  have hstable : (prefixWord ++ tailWord_2552168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552168).length < 2 ^ (prefixWord ++ tailWord_2552168).sum := by decide
  have hdescent : baseEnd_2552168 < baseStart_2552168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552182 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2552182 : Nat := 118140960795 + 2552182 * 2 ^ 59
def prefixEnd_2552182 : Nat := 4983230072969 + 3 ^ 40 * 2552182 * 2
def baseEnd_2552182 : Nat := 1310496083753238809887735

theorem tailTrace_2552182 : CollatzResearch.WordTrace tailWord_2552182 prefixEnd_2552182 1310496083753238809887735 := by
  unfold tailWord_2552182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817857802492997926793175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62057149893258644552460533 5817857802492997926793175)
  ·
    refine ⟨8726786703739496890189763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5817857802492997926793175 8726786703739496890189763)
    ·
      refine ⟨13090180055609245335284645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8726786703739496890189763 13090180055609245335284645)
      ·
        refine ⟨2454408760426733500365871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13090180055609245335284645 2454408760426733500365871)
        ·
          refine ⟨3681613140640100250548807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454408760426733500365871 3681613140640100250548807)
          ·
            refine ⟨5522419710960150375823211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681613140640100250548807 5522419710960150375823211)
            ·
              refine ⟨8283629566440225563734817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522419710960150375823211 8283629566440225563734817)
              ·
                refine ⟨6212722174830169172801113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283629566440225563734817 6212722174830169172801113)
                ·
                  refine ⟨4659541631122626879600835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212722174830169172801113 4659541631122626879600835)
                  ·
                    refine ⟨6989312446683940319401253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659541631122626879600835 6989312446683940319401253)
                    ·
                      refine ⟨1310496083753238809887735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6989312446683940319401253 1310496083753238809887735)
                      ·
                        rfl

theorem cell23_2552182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2552182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552182 prefixEnd_2552182 := by exact prefixLift 2552182
  have htrace : WordTrace (prefixWord ++ tailWord_2552182) baseStart_2552182 baseEnd_2552182 := by
    simpa [prefixWord, tailWord_2552182, baseEnd_2552182] using wordTrace_append hprefix tailTrace_2552182
  have hstable : (prefixWord ++ tailWord_2552182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552182).length < 2 ^ (prefixWord ++ tailWord_2552182).sum := by decide
  have hdescent : baseEnd_2552182 < baseStart_2552182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552218 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_2552218 : Nat := 118140960795 + 2552218 * 2 ^ 59
def prefixEnd_2552218 : Nat := 4983230072969 + 3 ^ 40 * 2552218 * 2
def baseEnd_2552218 : Nat := 436838189685600223012523

theorem tailTrace_2552218 : CollatzResearch.WordTrace tailWord_2552218 prefixEnd_2552218 436838189685600223012523 := by
  unfold tailWord_2552218
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271759466939386244250327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62058025245171696651334205 23271759466939386244250327)
  ·
    refine ⟨34907639200409079366375491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23271759466939386244250327 34907639200409079366375491)
    ·
      refine ⟨52361458800613619049563237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34907639200409079366375491 52361458800613619049563237)
      ·
        refine ⟨9817773525115053571793107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52361458800613619049563237 9817773525115053571793107)
        ·
          refine ⟨14726660287672580357689661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9817773525115053571793107 14726660287672580357689661)
          ·
            refine ⟨5522497607877217634133623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14726660287672580357689661 5522497607877217634133623)
            ·
              refine ⟨8283746411815826451200435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522497607877217634133623 8283746411815826451200435)
              ·
                refine ⟨12425619617723739676800653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283746411815826451200435 12425619617723739676800653)
                ·
                  refine ⟨4659607356646402378800245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12425619617723739676800653 4659607356646402378800245)
                  ·
                    refine ⟨436838189685600223012523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4659607356646402378800245 436838189685600223012523)
                    ·
                      rfl

theorem cell23_2552218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_2552218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552218 prefixEnd_2552218 := by exact prefixLift 2552218
  have htrace : WordTrace (prefixWord ++ tailWord_2552218) baseStart_2552218 baseEnd_2552218 := by
    simpa [prefixWord, tailWord_2552218, baseEnd_2552218] using wordTrace_append hprefix tailTrace_2552218
  have hstable : (prefixWord ++ tailWord_2552218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552218).length < 2 ^ (prefixWord ++ tailWord_2552218).sum := by decide
  have hdescent : baseEnd_2552218 < baseStart_2552218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552249 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2552249 : Nat := 118140960795 + 2552249 * 2 ^ 59
def prefixEnd_2552249 : Nat := 4983230072969 + 3 ^ 40 * 2552249 * 2
def baseEnd_2552249 : Nat := 1310530486957090047749927

theorem tailTrace_2552249 : CollatzResearch.WordTrace tailWord_2552249 prefixEnd_2552249 1310530486957090047749927 := by
  unfold tailWord_2552249
  simp only [CollatzResearch.WordTrace]
  refine ⟨93088168530645237271379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62058779020430158180919867 93088168530645237271379801)
  ·
    refine ⟨69816126397983927953534851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93088168530645237271379801 69816126397983927953534851)
    ·
      refine ⟨104724189596975891930302277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69816126397983927953534851 104724189596975891930302277)
      ·
        refine ⟨19635785549432979736931677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104724189596975891930302277 19635785549432979736931677)
        ·
          refine ⟨7363419581037367401349379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19635785549432979736931677 7363419581037367401349379)
          ·
            refine ⟨11045129371556051102024069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363419581037367401349379 11045129371556051102024069)
            ·
              refine ⟨2070961757166759581629513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11045129371556051102024069 2070961757166759581629513)
              ·
                refine ⟨1553221317875069686222135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070961757166759581629513 1553221317875069686222135)
                ·
                  refine ⟨2329831976812604529333203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553221317875069686222135 2329831976812604529333203)
                  ·
                    refine ⟨3494747965218906793999805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329831976812604529333203 3494747965218906793999805)
                    ·
                      refine ⟨1310530486957090047749927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494747965218906793999805 1310530486957090047749927)
                      ·
                        rfl

theorem cell23_2552249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2552249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552249 prefixEnd_2552249 := by exact prefixLift 2552249
  have htrace : WordTrace (prefixWord ++ tailWord_2552249) baseStart_2552249 baseEnd_2552249 := by
    simpa [prefixWord, tailWord_2552249, baseEnd_2552249] using wordTrace_append hprefix tailTrace_2552249
  have hstable : (prefixWord ++ tailWord_2552249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552249).length < 2 ^ (prefixWord ++ tailWord_2552249).sum := by decide
  have hdescent : baseEnd_2552249 < baseStart_2552249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552288 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2552288 : Nat := 118140960795 + 2552288 * 2 ^ 59
def prefixEnd_2552288 : Nat := 4983230072969 + 3 ^ 40 * 2552288 * 2
def baseEnd_2552288 : Nat := 1310550512702615395162247

theorem tailTrace_2552288 : CollatzResearch.WordTrace tailWord_2552288 prefixEnd_2552288 1310550512702615395162247 := by
  unfold tailWord_2552288
  simp only [CollatzResearch.WordTrace]
  refine ⟨46544795488751973466024759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62059727318335964621366345 46544795488751973466024759)
  ·
    refine ⟨69817193233127960199037139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46544795488751973466024759 69817193233127960199037139)
    ·
      refine ⟨104725789849691940298555709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69817193233127960199037139 104725789849691940298555709)
      ·
        refine ⟨39272171193634477611958391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104725789849691940298555709 39272171193634477611958391)
        ·
          refine ⟨58908256790451716417937587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39272171193634477611958391 58908256790451716417937587)
          ·
            refine ⟨88362385185677574626906381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58908256790451716417937587 88362385185677574626906381)
            ·
              refine ⟨33135894444629090485089893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88362385185677574626906381 33135894444629090485089893)
              ·
                refine ⟨6212980208367954465954355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33135894444629090485089893 6212980208367954465954355)
                ·
                  refine ⟨9319470312551931698931533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6212980208367954465954355 9319470312551931698931533)
                  ·
                    refine ⟨3494801367206974387099325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9319470312551931698931533 3494801367206974387099325)
                    ·
                      refine ⟨1310550512702615395162247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494801367206974387099325 1310550512702615395162247)
                      ·
                        rfl

theorem cell23_2552288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2552288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552288 prefixEnd_2552288 := by exact prefixLift 2552288
  have htrace : WordTrace (prefixWord ++ tailWord_2552288) baseStart_2552288 baseEnd_2552288 := by
    simpa [prefixWord, tailWord_2552288, baseEnd_2552288] using wordTrace_append hprefix tailTrace_2552288
  have hstable : (prefixWord ++ tailWord_2552288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552288).length < 2 ^ (prefixWord ++ tailWord_2552288).sum := by decide
  have hdescent : baseEnd_2552288 < baseStart_2552288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552289 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_2552289 : Nat := 118140960795 + 2552289 * 2 ^ 59
def prefixEnd_2552289 : Nat := 4983230072969 + 3 ^ 40 * 2552289 * 2
def baseEnd_2552289 : Nat := 1310551026183269891249743

theorem tailTrace_2552289 : CollatzResearch.WordTrace tailWord_2552289 prefixEnd_2552289 1310551026183269891249743 := by
  unfold tailWord_2552289
  simp only [CollatzResearch.WordTrace]
  refine ⟨93089627450500324102835921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62059751633666882735223947 93089627450500324102835921)
  ·
    refine ⟨69817220587875243077126941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93089627450500324102835921 69817220587875243077126941)
    ·
      refine ⟨26181457720453216153922603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69817220587875243077126941 26181457720453216153922603)
      ·
        refine ⟨39272186580679824230883905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26181457720453216153922603 39272186580679824230883905)
        ·
          refine ⟨29454139935509868173162929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39272186580679824230883905 29454139935509868173162929)
          ·
            refine ⟨22090604951632401129872197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29454139935509868173162929 22090604951632401129872197)
            ·
              refine ⟨4141988428431075211851037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22090604951632401129872197 4141988428431075211851037)
              ·
                refine ⟨1553245660661653204444139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4141988428431075211851037 1553245660661653204444139)
                ·
                  refine ⟨2329868490992479806666209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553245660661653204444139 2329868490992479806666209)
                  ·
                    refine ⟨1747401368244359854999657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329868490992479806666209 1747401368244359854999657)
                    ·
                      refine ⟨1310551026183269891249743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747401368244359854999657 1310551026183269891249743)
                      ·
                        rfl

theorem cell23_2552289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_2552289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552289 prefixEnd_2552289 := by exact prefixLift 2552289
  have htrace : WordTrace (prefixWord ++ tailWord_2552289) baseStart_2552289 baseEnd_2552289 := by
    simpa [prefixWord, tailWord_2552289, baseEnd_2552289] using wordTrace_append hprefix tailTrace_2552289
  have hstable : (prefixWord ++ tailWord_2552289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552289).length < 2 ^ (prefixWord ++ tailWord_2552289).sum := by decide
  have hdescent : baseEnd_2552289 < baseStart_2552289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552305 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_2552305 : Nat := 118140960795 + 2552305 * 2 ^ 59
def prefixEnd_2552305 : Nat := 4983230072969 + 3 ^ 40 * 2552305 * 2
def baseEnd_2552305 : Nat := 1310559241873741828649669

theorem tailTrace_2552305 : CollatzResearch.WordTrace tailWord_2552305 prefixEnd_2552305 1310559241873741828649669 := by
  unfold tailWord_2552305
  simp only [CollatzResearch.WordTrace]
  refine ⟨93090211018442358835418369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62060140678961572556945579 93090211018442358835418369)
  ·
    refine ⟨69817658263831769126563777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93090211018442358835418369 69817658263831769126563777)
    ·
      refine ⟨52363243697873826844922833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69817658263831769126563777 52363243697873826844922833)
      ·
        refine ⟨39272432773405370133692125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52363243697873826844922833 39272432773405370133692125)
        ·
          refine ⟨14727162290027013800134547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39272432773405370133692125 14727162290027013800134547)
          ·
            refine ⟨22090743435040520700201821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14727162290027013800134547 22090743435040520700201821)
            ·
              refine ⟨8284028788140195262575683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22090743435040520700201821 8284028788140195262575683)
              ·
                refine ⟨12426043182210292893863525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8284028788140195262575683 12426043182210292893863525)
                ·
                  refine ⟨2329883096664429917599411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12426043182210292893863525 2329883096664429917599411)
                  ·
                    refine ⟨3494824644996644876399117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329883096664429917599411 3494824644996644876399117)
                    ·
                      refine ⟨1310559241873741828649669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494824644996644876399117 1310559241873741828649669)
                      ·
                        rfl

theorem cell23_2552305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_2552305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552305 prefixEnd_2552305 := by exact prefixLift 2552305
  have htrace : WordTrace (prefixWord ++ tailWord_2552305) baseStart_2552305 baseEnd_2552305 := by
    simpa [prefixWord, tailWord_2552305, baseEnd_2552305] using wordTrace_append hprefix tailTrace_2552305
  have hstable : (prefixWord ++ tailWord_2552305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552305).length < 2 ^ (prefixWord ++ tailWord_2552305).sum := by decide
  have hdescent : baseEnd_2552305 < baseStart_2552305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552326 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2552326 : Nat := 118140960795 + 2552326 * 2 ^ 59
def prefixEnd_2552326 : Nat := 4983230072969 + 3 ^ 40 * 2552326 * 2
def baseEnd_2552326 : Nat := 1310570024967486246487073

theorem tailTrace_2552326 : CollatzResearch.WordTrace tailWord_2552326 prefixEnd_2552326 1310570024967486246487073 := by
  unfold tailWord_2552326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909093029730196231935401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62060651300910852947955221 2909093029730196231935401)
  ·
    refine ⟨2181819772297647173951551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2909093029730196231935401 2181819772297647173951551)
    ·
      refine ⟨3272729658446470760927327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181819772297647173951551 3272729658446470760927327)
      ·
        refine ⟨4909094487669706141390991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272729658446470760927327 4909094487669706141390991)
        ·
          refine ⟨7363641731504559212086487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909094487669706141390991 7363641731504559212086487)
          ·
            refine ⟨11045462597256838818129731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363641731504559212086487 11045462597256838818129731)
            ·
              refine ⟨16568193895885258227194597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045462597256838818129731 16568193895885258227194597)
              ·
                refine ⟨3106536355478485917598987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16568193895885258227194597 3106536355478485917598987)
                ·
                  refine ⟨4659804533217728876398481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106536355478485917598987 4659804533217728876398481)
                  ·
                    refine ⟨3494853399913296657298861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4659804533217728876398481 3494853399913296657298861)
                    ·
                      refine ⟨1310570024967486246487073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3494853399913296657298861 1310570024967486246487073)
                      ·
                        rfl

theorem cell23_2552326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2552326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552326 prefixEnd_2552326 := by exact prefixLift 2552326
  have htrace : WordTrace (prefixWord ++ tailWord_2552326) baseStart_2552326 baseEnd_2552326 := by
    simpa [prefixWord, tailWord_2552326, baseEnd_2552326] using wordTrace_append hprefix tailTrace_2552326
  have hstable : (prefixWord ++ tailWord_2552326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552326).length < 2 ^ (prefixWord ++ tailWord_2552326).sum := by decide
  have hdescent : baseEnd_2552326 < baseStart_2552326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552332 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_2552332 : Nat := 118140960795 + 2552332 * 2 ^ 59
def prefixEnd_2552332 : Nat := 4983230072969 + 3 ^ 40 * 2552332 * 2
def baseEnd_2552332 : Nat := 1310573105851413223012045

theorem tailTrace_2552332 : CollatzResearch.WordTrace tailWord_2552332 prefixEnd_2552332 1310573105851413223012045 := by
  unfold tailWord_2552332
  simp only [CollatzResearch.WordTrace]
  refine ⟨46545597894672271223325625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62060797192896361631100833 46545597894672271223325625)
  ·
    refine ⟨34909198421004203417494219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46545597894672271223325625 34909198421004203417494219)
    ·
      refine ⟨52363797631506305126241329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34909198421004203417494219 52363797631506305126241329)
      ·
        refine ⟨39272848223629728844680997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52363797631506305126241329 39272848223629728844680997)
        ·
          refine ⟨7363659041930574158377687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39272848223629728844680997 7363659041930574158377687)
          ·
            refine ⟨11045488562895861237566531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363659041930574158377687 11045488562895861237566531)
            ·
              refine ⟨16568232844343791856349797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045488562895861237566531 16568232844343791856349797)
              ·
                refine ⟨3106543658314460973065587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16568232844343791856349797 3106543658314460973065587)
                ·
                  refine ⟨4659815487471691459598381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106543658314460973065587 4659815487471691459598381)
                  ·
                    refine ⟨1747430807801884297349393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4659815487471691459598381 1747430807801884297349393)
                    ·
                      refine ⟨1310573105851413223012045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747430807801884297349393 1310573105851413223012045)
                      ·
                        rfl

theorem cell23_2552332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_2552332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552332 prefixEnd_2552332 := by exact prefixLift 2552332
  have htrace : WordTrace (prefixWord ++ tailWord_2552332) baseStart_2552332 baseEnd_2552332 := by
    simpa [prefixWord, tailWord_2552332, baseEnd_2552332] using wordTrace_append hprefix tailTrace_2552332
  have hstable : (prefixWord ++ tailWord_2552332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552332).length < 2 ^ (prefixWord ++ tailWord_2552332).sum := by decide
  have hdescent : baseEnd_2552332 < baseStart_2552332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552348 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2552348 : Nat := 118140960795 + 2552348 * 2 ^ 59
def prefixEnd_2552348 : Nat := 4983230072969 + 3 ^ 40 * 2552348 * 2
def baseEnd_2552348 : Nat := 1310581321541885160411971

theorem tailTrace_2552348 : CollatzResearch.WordTrace tailWord_2552348 prefixEnd_2552348 1310581321541885160411971 := by
  unfold tailWord_2552348
  simp only [CollatzResearch.WordTrace]
  refine ⟨46545889678643288589616849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62061186238191051452822465 46545889678643288589616849)
  ·
    refine ⟨34909417258982466442212637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46545889678643288589616849 34909417258982466442212637)
    ·
      refine ⟨13091031472118424915829739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34909417258982466442212637 13091031472118424915829739)
      ·
        refine ⟨19636547208177637373744609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13091031472118424915829739 19636547208177637373744609)
        ·
          refine ⟨14727410406133228030308457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19636547208177637373744609 14727410406133228030308457)
          ·
            refine ⟨11045557804599921022731343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14727410406133228030308457 11045557804599921022731343)
            ·
              refine ⟨16568336706899881534097015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045557804599921022731343 16568336706899881534097015)
              ·
                refine ⟨24852505060349822301145523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16568336706899881534097015 24852505060349822301145523)
                ·
                  refine ⟨37278757590524733451718285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24852505060349822301145523 37278757590524733451718285)
                  ·
                    refine ⟨13979534096446775044394357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37278757590524733451718285 13979534096446775044394357)
                    ·
                      refine ⟨1310581321541885160411971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13979534096446775044394357 1310581321541885160411971)
                      ·
                        rfl

theorem cell23_2552348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2552348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552348 prefixEnd_2552348 := by exact prefixLift 2552348
  have htrace : WordTrace (prefixWord ++ tailWord_2552348) baseStart_2552348 baseEnd_2552348 := by
    simpa [prefixWord, tailWord_2552348, baseEnd_2552348] using wordTrace_append hprefix tailTrace_2552348
  have hstable : (prefixWord ++ tailWord_2552348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552348).length < 2 ^ (prefixWord ++ tailWord_2552348).sum := by decide
  have hdescent : baseEnd_2552348 < baseStart_2552348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552368 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 7]
def baseStart_2552368 : Nat := 118140960795 + 2552368 * 2 ^ 59
def prefixEnd_2552368 : Nat := 4983230072969 + 3 ^ 40 * 2552368 * 2
def baseEnd_2552368 : Nat := 145621287906108342462431

theorem tailTrace_2552368 : CollatzResearch.WordTrace tailWord_2552368 prefixEnd_2552368 145621287906108342462431 := by
  unfold tailWord_2552368
  simp only [CollatzResearch.WordTrace]
  refine ⟨46546254408607060297480879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62061672544809413729974505 46546254408607060297480879)
  ·
    refine ⟨69819381612910590446221319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46546254408607060297480879 69819381612910590446221319)
    ·
      refine ⟨104729072419365885669331979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69819381612910590446221319 104729072419365885669331979)
      ·
        refine ⟨157093608629048828503997969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104729072419365885669331979 157093608629048828503997969)
        ·
          refine ⟨117820206471786621377998477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157093608629048828503997969 117820206471786621377998477)
          ·
            refine ⟨44182577426919983016749429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117820206471786621377998477 44182577426919983016749429)
            ·
              refine ⟨4142116633773748407820259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44182577426919983016749429 4142116633773748407820259)
              ·
                refine ⟨6213174950660622611730389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142116633773748407820259 6213174950660622611730389)
                ·
                  refine ⟨145621287906108342462431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6213174950660622611730389 145621287906108342462431)
                  ·
                    rfl

theorem cell23_2552368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_2552368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552368 prefixEnd_2552368 := by exact prefixLift 2552368
  have htrace : WordTrace (prefixWord ++ tailWord_2552368) baseStart_2552368 baseEnd_2552368 := by
    simpa [prefixWord, tailWord_2552368, baseEnd_2552368] using wordTrace_append hprefix tailTrace_2552368
  have hstable : (prefixWord ++ tailWord_2552368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552368).length < 2 ^ (prefixWord ++ tailWord_2552368).sum := by decide
  have hdescent : baseEnd_2552368 < baseStart_2552368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552398 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2552398 : Nat := 118140960795 + 2552398 * 2 ^ 59
def prefixEnd_2552398 : Nat := 4983230072969 + 3 ^ 40 * 2552398 * 2
def baseEnd_2552398 : Nat := 436868998524869988262247

theorem tailTrace_2552398 : CollatzResearch.WordTrace tailWord_2552398 prefixEnd_2552398 436868998524869988262247 := by
  unfold tailWord_2552398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11636700375888179464819231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62062402004736957145702565 11636700375888179464819231)
  ·
    refine ⟨17455050563832269197228847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11636700375888179464819231 17455050563832269197228847)
    ·
      refine ⟨26182575845748403795843271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17455050563832269197228847 26182575845748403795843271)
      ·
        refine ⟨39273863768622605693764907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26182575845748403795843271 39273863768622605693764907)
        ·
          refine ⟨58910795652933908540647361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39273863768622605693764907 58910795652933908540647361)
          ·
            refine ⟨44183096739700431405485521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58910795652933908540647361 44183096739700431405485521)
            ·
              refine ⟨33137322554775323554114141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44183096739700431405485521 33137322554775323554114141)
              ·
                refine ⟨12426495958040746332792803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33137322554775323554114141 12426495958040746332792803)
                ·
                  refine ⟨18639743937061119499189205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12426495958040746332792803 18639743937061119499189205)
                  ·
                    refine ⟨436868998524869988262247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18639743937061119499189205 436868998524869988262247)
                    ·
                      rfl

theorem cell23_2552398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2552398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552398 prefixEnd_2552398 := by exact prefixLift 2552398
  have htrace : WordTrace (prefixWord ++ tailWord_2552398) baseStart_2552398 baseEnd_2552398 := by
    simpa [prefixWord, tailWord_2552398, baseEnd_2552398] using wordTrace_append hprefix tailTrace_2552398
  have hstable : (prefixWord ++ tailWord_2552398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552398).length < 2 ^ (prefixWord ++ tailWord_2552398).sum := by decide
  have hdescent : baseEnd_2552398 < baseStart_2552398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552408 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2552408 : Nat := 118140960795 + 2552408 * 2 ^ 59
def prefixEnd_2552408 : Nat := 4983230072969 + 3 ^ 40 * 2552408 * 2
def baseEnd_2552408 : Nat := 1310612130381154925661695

theorem tailTrace_2552408 : CollatzResearch.WordTrace tailWord_2552408 prefixEnd_2552408 1310612130381154925661695 := by
  unfold tailWord_2552408
  simp only [CollatzResearch.WordTrace]
  refine ⟨46546983868534603713208939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62062645158046138284278585 46546983868534603713208939)
  ·
    refine ⟨69820475802801905569813409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46546983868534603713208939 69820475802801905569813409)
    ·
      refine ⟨52365356852101429177360057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69820475802801905569813409 52365356852101429177360057)
      ·
        refine ⟨39274017639076071883020043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52365356852101429177360057 39274017639076071883020043)
        ·
          refine ⟨58911026458614107824530065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39274017639076071883020043 58911026458614107824530065)
          ·
            refine ⟨44183269843960580868397549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58911026458614107824530065 44183269843960580868397549)
            ·
              refine ⟨16568726191485217825649081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44183269843960580868397549 16568726191485217825649081)
              ·
                refine ⟨12426544643613913369236811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16568726191485217825649081 12426544643613913369236811)
                ·
                  refine ⟨18639816965420870053855217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12426544643613913369236811 18639816965420870053855217)
                  ·
                    refine ⟨13979862724065652540391413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18639816965420870053855217 13979862724065652540391413)
                    ·
                      refine ⟨1310612130381154925661695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13979862724065652540391413 1310612130381154925661695)
                      ·
                        rfl

theorem cell23_2552408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2552408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552408 prefixEnd_2552408 := by exact prefixLift 2552408
  have htrace : WordTrace (prefixWord ++ tailWord_2552408) baseStart_2552408 baseEnd_2552408 := by
    simpa [prefixWord, tailWord_2552408, baseEnd_2552408] using wordTrace_append hprefix tailTrace_2552408
  have hstable : (prefixWord ++ tailWord_2552408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552408).length < 2 ^ (prefixWord ++ tailWord_2552408).sum := by decide
  have hdescent : baseEnd_2552408 < baseStart_2552408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552452 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2552452 : Nat := 118140960795 + 2552452 * 2 ^ 59
def prefixEnd_2552452 : Nat := 4983230072969 + 3 ^ 40 * 2552452 * 2
def baseEnd_2552452 : Nat := 1310634723529952753511493

theorem tailTrace_2552452 : CollatzResearch.WordTrace tailWord_2552452 prefixEnd_2552452 1310634723529952753511493 := by
  unfold tailWord_2552452
  simp only [CollatzResearch.WordTrace]
  refine ⟨46547786274454901470509805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62063715032606535294013073 46547786274454901470509805)
  ·
    refine ⟨17455419852920588051441177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46547786274454901470509805 17455419852920588051441177)
    ·
      refine ⟨13091564889690441038580883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17455419852920588051441177 13091564889690441038580883)
      ·
        refine ⟨19637347334535661557871325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13091564889690441038580883 19637347334535661557871325)
        ·
          refine ⟨7364005250450873084201747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19637347334535661557871325 7364005250450873084201747)
          ·
            refine ⟨11046007875676309626302621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364005250450873084201747 11046007875676309626302621)
            ·
              refine ⟨4142252953378616109863483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11046007875676309626302621 4142252953378616109863483)
              ·
                refine ⟨6213379430067924164795225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142252953378616109863483 6213379430067924164795225)
                ·
                  refine ⟨4660034572550943123596419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6213379430067924164795225 4660034572550943123596419)
                  ·
                    refine ⟨6990051858826414685394629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660034572550943123596419 6990051858826414685394629)
                    ·
                      refine ⟨1310634723529952753511493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6990051858826414685394629 1310634723529952753511493)
                      ·
                        rfl

theorem cell23_2552452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2552452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552452 prefixEnd_2552452 := by exact prefixLift 2552452
  have htrace : WordTrace (prefixWord ++ tailWord_2552452) baseStart_2552452 baseEnd_2552452 := by
    simpa [prefixWord, tailWord_2552452, baseEnd_2552452] using wordTrace_append hprefix tailTrace_2552452
  have hstable : (prefixWord ++ tailWord_2552452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552452).length < 2 ^ (prefixWord ++ tailWord_2552452).sum := by decide
  have hdescent : baseEnd_2552452 < baseStart_2552452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552455 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2552455 : Nat := 118140960795 + 2552455 * 2 ^ 59
def prefixEnd_2552455 : Nat := 4983230072969 + 3 ^ 40 * 2552455 * 2
def baseEnd_2552455 : Nat := 1310636263971916241773979

theorem tailTrace_2552455 : CollatzResearch.WordTrace tailWord_2552455 prefixEnd_2552455 1310636263971916241773979 := by
  unfold tailWord_2552455
  simp only [CollatzResearch.WordTrace]
  refine ⟨93095681967898934453378819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62063787978599289635585879 93095681967898934453378819)
  ·
    refine ⟨139643522951848401680068229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93095681967898934453378819 139643522951848401680068229)
    ·
      refine ⟨26183160553471575315012793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139643522951848401680068229 26183160553471575315012793)
      ·
        refine ⟨19637370415103681486259595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26183160553471575315012793 19637370415103681486259595)
        ·
          refine ⟨29456055622655522229389393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19637370415103681486259595 29456055622655522229389393)
          ·
            refine ⟨22092041716991641672042045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29456055622655522229389393 22092041716991641672042045)
            ·
              refine ⟨8284515643871865627015767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22092041716991641672042045 8284515643871865627015767)
              ·
                refine ⟨12426773465807798440523651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8284515643871865627015767 12426773465807798440523651)
                ·
                  refine ⟨18640160198711697660785477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12426773465807798440523651 18640160198711697660785477)
                  ·
                    refine ⟨3495030037258443311397277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18640160198711697660785477 3495030037258443311397277)
                    ·
                      refine ⟨1310636263971916241773979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495030037258443311397277 1310636263971916241773979)
                      ·
                        rfl

theorem cell23_2552455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2552455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552455 prefixEnd_2552455 := by exact prefixLift 2552455
  have htrace : WordTrace (prefixWord ++ tailWord_2552455) baseStart_2552455 baseEnd_2552455 := by
    simpa [prefixWord, tailWord_2552455, baseEnd_2552455] using wordTrace_append hprefix tailTrace_2552455
  have hstable : (prefixWord ++ tailWord_2552455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552455).length < 2 ^ (prefixWord ++ tailWord_2552455).sum := by decide
  have hdescent : baseEnd_2552455 < baseStart_2552455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552512 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2]
def baseStart_2552512 : Nat := 118140960795 + 2552512 * 2 ^ 59
def prefixEnd_2552512 : Nat := 4983230072969 + 3 ^ 40 * 2552512 * 2
def baseEnd_2552512 : Nat := 1310665532369222518761217

theorem tailTrace_2552512 : CollatzResearch.WordTrace tailWord_2552512 prefixEnd_2552512 1310665532369222518761217 := by
  unfold tailWord_2552512
  simp only [CollatzResearch.WordTrace]
  refine ⟨46548880464346216594101895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62065173952461622125469193 46548880464346216594101895)
  ·
    refine ⟨69823320696519324891152843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46548880464346216594101895 69823320696519324891152843)
    ·
      refine ⟨104734981044778987336729265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69823320696519324891152843 104734981044778987336729265)
      ·
        refine ⟨78551235783584240502546949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104734981044778987336729265 78551235783584240502546949)
        ·
          refine ⟨14728356709422045094227553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78551235783584240502546949 14728356709422045094227553)
          ·
            refine ⟨11046267532066533820670665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14728356709422045094227553 11046267532066533820670665)
            ·
              refine ⟨8284700649049900365502999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11046267532066533820670665 8284700649049900365502999)
              ·
                refine ⟨12427050973574850548254499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8284700649049900365502999 12427050973574850548254499)
                ·
                  refine ⟨18640576460362275822381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12427050973574850548254499 18640576460362275822381749)
                  ·
                    refine ⟨1747554043158963358348289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18640576460362275822381749 1747554043158963358348289)
                    ·
                      refine ⟨1310665532369222518761217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747554043158963358348289 1310665532369222518761217)
                      ·
                        rfl

theorem cell23_2552512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_2552512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552512 prefixEnd_2552512 := by exact prefixLift 2552512
  have htrace : WordTrace (prefixWord ++ tailWord_2552512) baseStart_2552512 baseEnd_2552512 := by
    simpa [prefixWord, tailWord_2552512, baseEnd_2552512] using wordTrace_append hprefix tailTrace_2552512
  have hstable : (prefixWord ++ tailWord_2552512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552512).length < 2 ^ (prefixWord ++ tailWord_2552512).sum := by decide
  have hdescent : baseEnd_2552512 < baseStart_2552512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552519 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_2552519 : Nat := 118140960795 + 2552519 * 2 ^ 59
def prefixEnd_2552519 : Nat := 4983230072969 + 3 ^ 40 * 2552519 * 2
def baseEnd_2552519 : Nat := 1310669126733803991373685

theorem tailTrace_2552519 : CollatzResearch.WordTrace tailWord_2552519 prefixEnd_2552519 1310669126733803991373685 := by
  unfold tailWord_2552519
  simp only [CollatzResearch.WordTrace]
  refine ⟨93098016239667073383708611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62065344159778048922472407 93098016239667073383708611)
  ·
    refine ⟨139647024359500610075562917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93098016239667073383708611 139647024359500610075562917)
    ·
      refine ⟨26183817067406364389168047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139647024359500610075562917 26183817067406364389168047)
      ·
        refine ⟨39275725601109546583752071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26183817067406364389168047 39275725601109546583752071)
        ·
          refine ⟨58913588401664319875628107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39275725601109546583752071 58913588401664319875628107)
          ·
            refine ⟨88370382602496479813442161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58913588401664319875628107 88370382602496479813442161)
            ·
              refine ⟨66277786951872359860081621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88370382602496479813442161 66277786951872359860081621)
              ·
                refine ⟨1553385631684508434220663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66277786951872359860081621 1553385631684508434220663)
                ·
                  refine ⟨2330078447526762651330995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553385631684508434220663 2330078447526762651330995)
                  ·
                    refine ⟨3495117671290143976996493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330078447526762651330995 3495117671290143976996493)
                    ·
                      refine ⟨1310669126733803991373685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495117671290143976996493 1310669126733803991373685)
                      ·
                        rfl

theorem cell23_2552519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_2552519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552519 prefixEnd_2552519 := by exact prefixLift 2552519
  have htrace : WordTrace (prefixWord ++ tailWord_2552519) baseStart_2552519 baseEnd_2552519 := by
    simpa [prefixWord, tailWord_2552519, baseEnd_2552519] using wordTrace_append hprefix tailTrace_2552519
  have hstable : (prefixWord ++ tailWord_2552519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552519).length < 2 ^ (prefixWord ++ tailWord_2552519).sum := by decide
  have hdescent : baseEnd_2552519 < baseStart_2552519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552522 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_2552522 : Nat := 118140960795 + 2552522 * 2 ^ 59
def prefixEnd_2552522 : Nat := 4983230072969 + 3 ^ 40 * 2552522 * 2
def baseEnd_2552522 : Nat := 436890222391922493212057

theorem tailTrace_2552522 : CollatzResearch.WordTrace tailWord_2552522 prefixEnd_2552522 436890222391922493212057 := by
  unfold tailWord_2552522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23274531414664051224016955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62065417105770803264045213 23274531414664051224016955)
  ·
    refine ⟨34911797121996076836025433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23274531414664051224016955 34911797121996076836025433)
    ·
      refine ⟨26183847841497057627019075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34911797121996076836025433 26183847841497057627019075)
      ·
        refine ⟨39275771762245586440528613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26183847841497057627019075 39275771762245586440528613)
        ·
          refine ⟨7364207205421047457599115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39275771762245586440528613 7364207205421047457599115)
          ·
            refine ⟨11046310808131571186398673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364207205421047457599115 11046310808131571186398673)
            ·
              refine ⟨8284733106098678389799005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11046310808131571186398673 8284733106098678389799005)
              ·
                refine ⟨3106774914787004396174627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8284733106098678389799005 3106774914787004396174627)
                ·
                  refine ⟨4660162372180506594261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106774914787004396174627 4660162372180506594261941)
                  ·
                    refine ⟨436890222391922493212057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4660162372180506594261941 436890222391922493212057)
                    ·
                      rfl

theorem cell23_2552522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_2552522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552522 prefixEnd_2552522 := by exact prefixLift 2552522
  have htrace : WordTrace (prefixWord ++ tailWord_2552522) baseStart_2552522 baseEnd_2552522 := by
    simpa [prefixWord, tailWord_2552522, baseEnd_2552522] using wordTrace_append hprefix tailTrace_2552522
  have hstable : (prefixWord ++ tailWord_2552522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552522).length < 2 ^ (prefixWord ++ tailWord_2552522).sum := by decide
  have hdescent : baseEnd_2552522 < baseStart_2552522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552555 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4]
def baseStart_2552555 : Nat := 118140960795 + 2552555 * 2 ^ 59
def prefixEnd_2552555 : Nat := 4983230072969 + 3 ^ 40 * 2552555 * 2
def baseEnd_2552555 : Nat := 1310687612037365850523519

theorem tailTrace_2552555 : CollatzResearch.WordTrace tailWord_2552555 prefixEnd_2552555 1310687612037365850523519 := by
  unfold tailWord_2552555
  simp only [CollatzResearch.WordTrace]
  refine ⟨93099329267536651532019119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62066219511691101021346079 93099329267536651532019119)
  ·
    refine ⟨139648993901304977298028679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93099329267536651532019119 139648993901304977298028679)
    ·
      refine ⟨209473490851957465947043019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139648993901304977298028679 209473490851957465947043019)
      ·
        refine ⟨314210236277936198920564529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209473490851957465947043019 314210236277936198920564529)
        ·
          refine ⟨235657677208452149190423397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314210236277936198920564529 235657677208452149190423397)
          ·
            refine ⟨44185814476584777973204387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235657677208452149190423397 44185814476584777973204387)
            ·
              refine ⟨66278721714877166959806581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44185814476584777973204387 66278721714877166959806581)
              ·
                refine ⟨6213630160769734402481867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66278721714877166959806581 6213630160769734402481867)
                ·
                  refine ⟨9320445241154601603722801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213630160769734402481867 9320445241154601603722801)
                  ·
                    refine ⟨6990333930865951202792101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9320445241154601603722801 6990333930865951202792101)
                    ·
                      refine ⟨1310687612037365850523519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6990333930865951202792101 1310687612037365850523519)
                      ·
                        rfl

theorem cell23_2552555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_2552555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552555 prefixEnd_2552555 := by exact prefixLift 2552555
  have htrace : WordTrace (prefixWord ++ tailWord_2552555) baseStart_2552555 baseEnd_2552555 := by
    simpa [prefixWord, tailWord_2552555, baseEnd_2552555] using wordTrace_append hprefix tailTrace_2552555
  have hstable : (prefixWord ++ tailWord_2552555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552555).length < 2 ^ (prefixWord ++ tailWord_2552555).sum := by decide
  have hdescent : baseEnd_2552555 < baseStart_2552555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552559 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_2552559 : Nat := 118140960795 + 2552559 * 2 ^ 59
def prefixEnd_2552559 : Nat := 4983230072969 + 3 ^ 40 * 2552559 * 2
def baseEnd_2552559 : Nat := 1310689665959983834873501

theorem tailTrace_2552559 : CollatzResearch.WordTrace tailWord_2552559 prefixEnd_2552559 1310689665959983834873501 := by
  unfold tailWord_2552559
  simp only [CollatzResearch.WordTrace]
  refine ⟨93099475159522160215164731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62066316773014773476776487 93099475159522160215164731)
  ·
    refine ⟨139649212739283240322747097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93099475159522160215164731 139649212739283240322747097)
    ·
      refine ⟨104736909554462430242060323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139649212739283240322747097 104736909554462430242060323)
      ·
        refine ⟨157105364331693645363090485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104736909554462430242060323 157105364331693645363090485)
        ·
          refine ⟨14728627906096279252789733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157105364331693645363090485 14728627906096279252789733)
          ·
            refine ⟨2761617732393052359898075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14728627906096279252789733 2761617732393052359898075)
            ·
              refine ⟨4142426598589578539847113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761617732393052359898075 4142426598589578539847113)
              ·
                refine ⟨3106819948942183904885335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4142426598589578539847113 3106819948942183904885335)
                ·
                  refine ⟨4660229923413275857328003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106819948942183904885335 4660229923413275857328003)
                  ·
                    refine ⟨6990344885119913785992005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660229923413275857328003 6990344885119913785992005)
                    ·
                      refine ⟨1310689665959983834873501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6990344885119913785992005 1310689665959983834873501)
                      ·
                        rfl

theorem cell23_2552559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_2552559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552559 prefixEnd_2552559 := by exact prefixLift 2552559
  have htrace : WordTrace (prefixWord ++ tailWord_2552559) baseStart_2552559 baseEnd_2552559 := by
    simpa [prefixWord, tailWord_2552559, baseEnd_2552559] using wordTrace_append hprefix tailTrace_2552559
  have hstable : (prefixWord ++ tailWord_2552559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552559).length < 2 ^ (prefixWord ++ tailWord_2552559).sum := by decide
  have hdescent : baseEnd_2552559 < baseStart_2552559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552572 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2552572 : Nat := 118140960795 + 2552572 * 2 ^ 59
def prefixEnd_2552572 : Nat := 4983230072969 + 3 ^ 40 * 2552572 * 2
def baseEnd_2552572 : Nat := 1310696341208492284010941

theorem tailTrace_2552572 : CollatzResearch.WordTrace tailWord_2552572 prefixEnd_2552572 1310696341208492284010941 := by
  unfold tailWord_2552572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46549974654237531717693985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62066632872316708956925313 46549974654237531717693985)
  ·
    refine ⟨34912480990678148788270489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46549974654237531717693985 34912480990678148788270489)
    ·
      refine ⟨26184360743008611591202867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34912480990678148788270489 26184360743008611591202867)
      ·
        refine ⟨39276541114512917386804301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26184360743008611591202867 39276541114512917386804301)
        ·
          refine ⟨14728702917942344020051613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39276541114512917386804301 14728702917942344020051613)
          ·
            refine ⟨5523263594228379007519355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14728702917942344020051613 5523263594228379007519355)
            ·
              refine ⟨8284895391342568511279033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523263594228379007519355 8284895391342568511279033)
              ·
                refine ⟨6213671543506926383459275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8284895391342568511279033 6213671543506926383459275)
                ·
                  refine ⟨9320507315260389575188913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213671543506926383459275 9320507315260389575188913)
                  ·
                    refine ⟨6990380486445292181391685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9320507315260389575188913 6990380486445292181391685)
                    ·
                      refine ⟨1310696341208492284010941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6990380486445292181391685 1310696341208492284010941)
                      ·
                        rfl

theorem cell23_2552572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2552572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552572 prefixEnd_2552572 := by exact prefixLift 2552572
  have htrace : WordTrace (prefixWord ++ tailWord_2552572) baseStart_2552572 baseEnd_2552572 := by
    simpa [prefixWord, tailWord_2552572, baseEnd_2552572] using wordTrace_append hprefix tailTrace_2552572
  have hstable : (prefixWord ++ tailWord_2552572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552572).length < 2 ^ (prefixWord ++ tailWord_2552572).sum := by decide
  have hdescent : baseEnd_2552572 < baseStart_2552572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552593 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 1, 2, 2]
def baseStart_2552593 : Nat := 118140960795 + 2552593 * 2 ^ 59
def prefixEnd_2552593 : Nat := 4983230072969 + 3 ^ 40 * 2552593 * 2
def baseEnd_2552593 : Nat := 1310707124302236701848345

theorem tailTrace_2552593 : CollatzResearch.WordTrace tailWord_2552593 prefixEnd_2552593 1310707124302236701848345 := by
  unfold tailWord_2552593
  simp only [CollatzResearch.WordTrace]
  refine ⟨93100715241398984021902433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62067143494265989347934955 93100715241398984021902433)
  ·
    refine ⟨69825536431049238016426825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93100715241398984021902433 69825536431049238016426825)
    ·
      refine ⟨52369152323286928512320119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69825536431049238016426825 52369152323286928512320119)
      ·
        refine ⟨78553728484930392768480179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52369152323286928512320119 78553728484930392768480179)
        ·
          refine ⟨117830592727395589152720269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78553728484930392768480179 117830592727395589152720269)
          ·
            refine ⟨44186472272773345932270101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117830592727395589152720269 44186472272773345932270101)
            ·
              refine ⟨2071240887786250590575161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44186472272773345932270101 2071240887786250590575161)
              ·
                refine ⟨1553430665839687942931371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071240887786250590575161 1553430665839687942931371)
                ·
                  refine ⟨2330145998759531914397057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553430665839687942931371 2330145998759531914397057)
                  ·
                    refine ⟨1747609499069648935797793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2330145998759531914397057 1747609499069648935797793)
                    ·
                      refine ⟨1310707124302236701848345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747609499069648935797793 1310707124302236701848345)
                      ·
                        rfl

theorem cell23_2552593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_2552593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552593 prefixEnd_2552593 := by exact prefixLift 2552593
  have htrace : WordTrace (prefixWord ++ tailWord_2552593) baseStart_2552593 baseEnd_2552593 := by
    simpa [prefixWord, tailWord_2552593, baseEnd_2552593] using wordTrace_append hprefix tailTrace_2552593
  have hstable : (prefixWord ++ tailWord_2552593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552593).length < 2 ^ (prefixWord ++ tailWord_2552593).sum := by decide
  have hdescent : baseEnd_2552593 < baseStart_2552593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552599 : List Nat := [1, 1, 3, 4, 4, 1, 1, 8]
def baseStart_2552599 : Nat := 118140960795 + 2552599 * 2 ^ 59
def prefixEnd_2552599 : Nat := 4983230072969 + 3 ^ 40 * 2552599 * 2
def baseEnd_2552599 : Nat := 48544822414302358458271

theorem tailTrace_2552599 : CollatzResearch.WordTrace tailWord_2552599 prefixEnd_2552599 48544822414302358458271 := by
  unfold tailWord_2552599
  simp only [CollatzResearch.WordTrace]
  refine ⟨93100934079377247046620851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62067289386251498031080567 93100934079377247046620851)
  ·
    refine ⟨139651401119065870569931277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93100934079377247046620851 139651401119065870569931277)
    ·
      refine ⟨52369275419649701463724229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139651401119065870569931277 52369275419649701463724229)
      ·
        refine ⟨9819239141184319024448293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52369275419649701463724229 9819239141184319024448293)
        ·
          refine ⟨1841107338972059817084055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9819239141184319024448293 1841107338972059817084055)
          ·
            refine ⟨2761661008458089725626083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841107338972059817084055 2761661008458089725626083)
            ·
              refine ⟨4142491512687134588439125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761661008458089725626083 4142491512687134588439125)
              ·
                refine ⟨48544822414302358458271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4142491512687134588439125 48544822414302358458271)
                ·
                  rfl

theorem cell23_2552599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 8].length) (baseStart_2552599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552599 prefixEnd_2552599 := by exact prefixLift 2552599
  have htrace : WordTrace (prefixWord ++ tailWord_2552599) baseStart_2552599 baseEnd_2552599 := by
    simpa [prefixWord, tailWord_2552599, baseEnd_2552599] using wordTrace_append hprefix tailTrace_2552599
  have hstable : (prefixWord ++ tailWord_2552599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552599).length < 2 ^ (prefixWord ++ tailWord_2552599).sum := by decide
  have hdescent : baseEnd_2552599 < baseStart_2552599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552609 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2552609 : Nat := 118140960795 + 2552609 * 2 ^ 59
def prefixEnd_2552609 : Nat := 4983230072969 + 3 ^ 40 * 2552609 * 2
def baseEnd_2552609 : Nat := 1310715339992708639248271

theorem tailTrace_2552609 : CollatzResearch.WordTrace tailWord_2552609 prefixEnd_2552609 1310715339992708639248271 := by
  unfold tailWord_2552609
  simp only [CollatzResearch.WordTrace]
  refine ⟨93101298809341018754484881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62067532539560679169656587 93101298809341018754484881)
  ·
    refine ⟨69825974107005764065863661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93101298809341018754484881 69825974107005764065863661)
    ·
      refine ⟨26184740290127161524698873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69825974107005764065863661 26184740290127161524698873)
      ·
        refine ⟨19638555217595371143524155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26184740290127161524698873 19638555217595371143524155)
        ·
          refine ⟨29457832826393056715286233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19638555217595371143524155 29457832826393056715286233)
          ·
            refine ⟨22093374619794792536464675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29457832826393056715286233 22093374619794792536464675)
            ·
              refine ⟨33140061929692188804697013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22093374619794792536464675 33140061929692188804697013)
              ·
                refine ⟨3106880805908642700440345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33140061929692188804697013 3106880805908642700440345)
                ·
                  refine ⟨2330160604431482025330259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106880805908642700440345 2330160604431482025330259)
                  ·
                    refine ⟨3495240906647223037995389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330160604431482025330259 3495240906647223037995389)
                    ·
                      refine ⟨1310715339992708639248271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495240906647223037995389 1310715339992708639248271)
                      ·
                        rfl

theorem cell23_2552609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2552609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552609 prefixEnd_2552609 := by exact prefixLift 2552609
  have htrace : WordTrace (prefixWord ++ tailWord_2552609) baseStart_2552609 baseEnd_2552609 := by
    simpa [prefixWord, tailWord_2552609, baseEnd_2552609] using wordTrace_append hprefix tailTrace_2552609
  have hstable : (prefixWord ++ tailWord_2552609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552609).length < 2 ^ (prefixWord ++ tailWord_2552609).sum := by decide
  have hdescent : baseEnd_2552609 < baseStart_2552609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552625 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_2552625 : Nat := 118140960795 + 2552625 * 2 ^ 59
def prefixEnd_2552625 : Nat := 4983230072969 + 3 ^ 40 * 2552625 * 2
def baseEnd_2552625 : Nat := 436907851894393525549399

theorem tailTrace_2552625 : CollatzResearch.WordTrace tailWord_2552625 prefixEnd_2552625 436907851894393525549399 := by
  unfold tailWord_2552625
  simp only [CollatzResearch.WordTrace]
  refine ⟨93101882377283053487067329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62067921584855368991378219 93101882377283053487067329)
  ·
    refine ⟨69826411782962290115300497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93101882377283053487067329 69826411782962290115300497)
    ·
      refine ⟨52369808837221717586475373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69826411782962290115300497 52369808837221717586475373)
      ·
        refine ⟨19638678313958144094928265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52369808837221717586475373 19638678313958144094928265)
        ·
          refine ⟨14729008735468608071196199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19638678313958144094928265 14729008735468608071196199)
          ·
            refine ⟨22093513103202912106794299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729008735468608071196199 22093513103202912106794299)
            ·
              refine ⟨33140269654804368160191449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22093513103202912106794299 33140269654804368160191449)
              ·
                refine ⟨24855202241103276120143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33140269654804368160191449 24855202241103276120143587)
                ·
                  refine ⟨37282803361654914180215381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24855202241103276120143587 37282803361654914180215381)
                  ·
                    refine ⟨436907851894393525549399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37282803361654914180215381 436907851894393525549399)
                    ·
                      rfl

theorem cell23_2552625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_2552625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552625 prefixEnd_2552625 := by exact prefixLift 2552625
  have htrace : WordTrace (prefixWord ++ tailWord_2552625) baseStart_2552625 baseEnd_2552625 := by
    simpa [prefixWord, tailWord_2552625, baseEnd_2552625] using wordTrace_append hprefix tailTrace_2552625
  have hstable : (prefixWord ++ tailWord_2552625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552625).length < 2 ^ (prefixWord ++ tailWord_2552625).sum := by decide
  have hdescent : baseEnd_2552625 < baseStart_2552625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552630 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2552630 : Nat := 118140960795 + 2552630 * 2 ^ 59
def prefixEnd_2552630 : Nat := 4983230072969 + 3 ^ 40 * 2552630 * 2
def baseEnd_2552630 : Nat := 1310726123086453057085675

theorem tailTrace_2552630 : CollatzResearch.WordTrace tailWord_2552630 prefixEnd_2552630 1310726123086453057085675 := by
  unfold tailWord_2552630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818879046391558708812459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62068043161509959560666229 5818879046391558708812459)
  ·
    refine ⟨8728318569587338063218689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5818879046391558708812459 8728318569587338063218689)
    ·
      refine ⟨6546238927190503547414017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8728318569587338063218689 6546238927190503547414017)
      ·
        refine ⟨4909679195392877660560513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6546238927190503547414017 4909679195392877660560513)
        ·
          refine ⟨3682259396544658245420385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4909679195392877660560513 3682259396544658245420385)
          ·
            refine ⟨2761694547408493684065289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3682259396544658245420385 2761694547408493684065289)
            ·
              refine ⟨2071270910556370263048967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761694547408493684065289 2071270910556370263048967)
              ·
                refine ⟨3106906365834555394573451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071270910556370263048967 3106906365834555394573451)
                ·
                  refine ⟨4660359548751833091860177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106906365834555394573451 4660359548751833091860177)
                  ·
                    refine ⟨3495269661563874818895133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4660359548751833091860177 3495269661563874818895133)
                    ·
                      refine ⟨1310726123086453057085675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495269661563874818895133 1310726123086453057085675)
                      ·
                        rfl

theorem cell23_2552630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2552630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552630 prefixEnd_2552630 := by exact prefixLift 2552630
  have htrace : WordTrace (prefixWord ++ tailWord_2552630) baseStart_2552630 baseEnd_2552630 := by
    simpa [prefixWord, tailWord_2552630, baseEnd_2552630] using wordTrace_append hprefix tailTrace_2552630
  have hstable : (prefixWord ++ tailWord_2552630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552630).length < 2 ^ (prefixWord ++ tailWord_2552630).sum := by decide
  have hdescent : baseEnd_2552630 < baseStart_2552630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552666 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_2552666 : Nat := 118140960795 + 2552666 * 2 ^ 59
def prefixEnd_2552666 : Nat := 4983230072969 + 3 ^ 40 * 2552666 * 2
def baseEnd_2552666 : Nat := 1310744608390014916235509

theorem tailTrace_2552666 : CollatzResearch.WordTrace tailWord_2552666 prefixEnd_2552666 1310744608390014916235509 := by
  unfold tailWord_2552666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275844442533629372327463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62068918513423011659539901 23275844442533629372327463)
  ·
    refine ⟨34913766663800444058491195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23275844442533629372327463 34913766663800444058491195)
    ·
      refine ⟨52370649995700666087736793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34913766663800444058491195 52370649995700666087736793)
      ·
        refine ⟨39277987496775499565802595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52370649995700666087736793 39277987496775499565802595)
        ·
          refine ⟨58916981245163249348703893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39277987496775499565802595 58916981245163249348703893)
          ·
            refine ⟨2761733495867027313220495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58916981245163249348703893 2761733495867027313220495)
            ·
              refine ⟨4142600243800540969830743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761733495867027313220495 4142600243800540969830743)
              ·
                refine ⟨6213900365700811454746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142600243800540969830743 6213900365700811454746115)
                ·
                  refine ⟨9320850548551217182119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213900365700811454746115 9320850548551217182119173)
                  ·
                    refine ⟨1747659477853353221647345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9320850548551217182119173 1747659477853353221647345)
                    ·
                      refine ⟨1310744608390014916235509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747659477853353221647345 1310744608390014916235509)
                      ·
                        rfl

theorem cell23_2552666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_2552666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552666 prefixEnd_2552666 := by exact prefixLift 2552666
  have htrace : WordTrace (prefixWord ++ tailWord_2552666) baseStart_2552666 baseEnd_2552666 := by
    simpa [prefixWord, tailWord_2552666, baseEnd_2552666] using wordTrace_append hprefix tailTrace_2552666
  have hstable : (prefixWord ++ tailWord_2552666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552666).length < 2 ^ (prefixWord ++ tailWord_2552666).sum := by decide
  have hdescent : baseEnd_2552666 < baseStart_2552666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552689 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 5]
def baseStart_2552689 : Nat := 118140960795 + 2552689 * 2 ^ 59
def prefixEnd_2552689 : Nat := 4983230072969 + 3 ^ 40 * 2552689 * 2
def baseEnd_2552689 : Nat := 145639602049452036249767

theorem tailTrace_2552689 : CollatzResearch.WordTrace tailWord_2552689 prefixEnd_2552689 145639602049452036249767 := by
  unfold tailWord_2552689
  simp only [CollatzResearch.WordTrace]
  refine ⟨93104216649051192417397121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62069477766034128278264747 93104216649051192417397121)
  ·
    refine ⟨69828162486788394313047841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93104216649051192417397121 69828162486788394313047841)
    ·
      refine ⟨52371121865091295734785881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69828162486788394313047841 52371121865091295734785881)
      ·
        refine ⟨39278341398818471801089411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52371121865091295734785881 39278341398818471801089411)
        ·
          refine ⟨58917512098227707701634117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39278341398818471801089411 58917512098227707701634117)
          ·
            refine ⟨11047033518417695194056397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58917512098227707701634117 11047033518417695194056397)
            ·
              refine ⟨4142637569406635697771149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11047033518417695194056397 4142637569406635697771149)
              ·
                refine ⟨1553489088527488386664181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4142637569406635697771149 1553489088527488386664181)
                ·
                  refine ⟨145639602049452036249767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1553489088527488386664181 145639602049452036249767)
                  ·
                    rfl

theorem cell23_2552689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 5].length) (baseStart_2552689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552689 prefixEnd_2552689 := by exact prefixLift 2552689
  have htrace : WordTrace (prefixWord ++ tailWord_2552689) baseStart_2552689 baseEnd_2552689 := by
    simpa [prefixWord, tailWord_2552689, baseEnd_2552689] using wordTrace_append hprefix tailTrace_2552689
  have hstable : (prefixWord ++ tailWord_2552689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552689).length < 2 ^ (prefixWord ++ tailWord_2552689).sum := by decide
  have hdescent : baseEnd_2552689 < baseStart_2552689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552695 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2552695 : Nat := 118140960795 + 2552695 * 2 ^ 59
def prefixEnd_2552695 : Nat := 4983230072969 + 3 ^ 40 * 2552695 * 2
def baseEnd_2552695 : Nat := 1310759499328995302772875

theorem tailTrace_2552695 : CollatzResearch.WordTrace tailWord_2552695 prefixEnd_2552695 1310759499328995302772875 := by
  unfold tailWord_2552695
  simp only [CollatzResearch.WordTrace]
  refine ⟨93104435487029455442115539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62069623658019636961410359 93104435487029455442115539)
  ·
    refine ⟨139656653230544183163173309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93104435487029455442115539 139656653230544183163173309)
    ·
      refine ⟨52371244961454068686189991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139656653230544183163173309 52371244961454068686189991)
      ·
        refine ⟨78556867442181103029284987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52371244961454068686189991 78556867442181103029284987)
        ·
          refine ⟨117835301163271654543927481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78556867442181103029284987 117835301163271654543927481)
          ·
            refine ⟨88376475872453740907945611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117835301163271654543927481 88376475872453740907945611)
            ·
              refine ⟨132564713808680611361918417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88376475872453740907945611 132564713808680611361918417)
              ·
                refine ⟨99423535356510458521438813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132564713808680611361918417 99423535356510458521438813)
                ·
                  refine ⟨37283825758691421945539555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99423535356510458521438813 37283825758691421945539555)
                  ·
                    refine ⟨55925738638037132918309333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37283825758691421945539555 55925738638037132918309333)
                    ·
                      refine ⟨1310759499328995302772875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55925738638037132918309333 1310759499328995302772875)
                      ·
                        rfl

theorem cell23_2552695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2552695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552695 prefixEnd_2552695 := by exact prefixLift 2552695
  have htrace : WordTrace (prefixWord ++ tailWord_2552695) baseStart_2552695 baseEnd_2552695 := by
    simpa [prefixWord, tailWord_2552695, baseEnd_2552695] using wordTrace_append hprefix tailTrace_2552695
  have hstable : (prefixWord ++ tailWord_2552695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552695).length < 2 ^ (prefixWord ++ tailWord_2552695).sum := by decide
  have hdescent : baseEnd_2552695 < baseStart_2552695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552712 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2552712 : Nat := 118140960795 + 2552712 * 2 ^ 59
def prefixEnd_2552712 : Nat := 4983230072969 + 3 ^ 40 * 2552712 * 2
def baseEnd_2552712 : Nat := 1310768228500121736260297

theorem tailTrace_2552712 : CollatzResearch.WordTrace tailWord_2552712 prefixEnd_2552712 1310768228500121736260297 := by
  unfold tailWord_2552712
  simp only [CollatzResearch.WordTrace]
  refine ⟨46552527763983933672742195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62070037018645244896989593 46552527763983933672742195)
  ·
    refine ⟨69828791645975900509113293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46552527763983933672742195 69828791645975900509113293)
    ·
      refine ⟨26185796867240962690917485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69828791645975900509113293 26185796867240962690917485)
      ·
        refine ⟨9819673825215361009094057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26185796867240962690917485 9819673825215361009094057)
        ·
          refine ⟨7364755368911520756820543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9819673825215361009094057 7364755368911520756820543)
          ·
            refine ⟨11047133053367281135230815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364755368911520756820543 11047133053367281135230815)
            ·
              refine ⟨16570699580050921702846223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047133053367281135230815 16570699580050921702846223)
              ·
                refine ⟨24856049370076382554269335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16570699580050921702846223 24856049370076382554269335)
                ·
                  refine ⟨37284074055114573831404003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24856049370076382554269335 37284074055114573831404003)
                  ·
                    refine ⟨55926111082671860747106005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37284074055114573831404003 55926111082671860747106005)
                    ·
                      refine ⟨1310768228500121736260297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55926111082671860747106005 1310768228500121736260297)
                      ·
                        rfl

theorem cell23_2552712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2552712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552712 prefixEnd_2552712 := by exact prefixLift 2552712
  have htrace : WordTrace (prefixWord ++ tailWord_2552712) baseStart_2552712 baseEnd_2552712 := by
    simpa [prefixWord, tailWord_2552712, baseEnd_2552712] using wordTrace_append hprefix tailTrace_2552712
  have hstable : (prefixWord ++ tailWord_2552712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552712).length < 2 ^ (prefixWord ++ tailWord_2552712).sum := by decide
  have hdescent : baseEnd_2552712 < baseStart_2552712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552759 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_2552759 : Nat := 118140960795 + 2552759 * 2 ^ 59
def prefixEnd_2552759 : Nat := 4983230072969 + 3 ^ 40 * 2552759 * 2
def baseEnd_2552759 : Nat := 1310792362090883052372581

theorem tailTrace_2552759 : CollatzResearch.WordTrace tailWord_2552759 prefixEnd_2552759 1310792362090883052372581 := by
  unfold tailWord_2552759
  simp only [CollatzResearch.WordTrace]
  refine ⟨93106769758797594372445331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62071179839198396248296887 93106769758797594372445331)
  ·
    refine ⟨139660154638196391558667997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93106769758797594372445331 139660154638196391558667997)
    ·
      refine ⟨52372557989323646834500499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139660154638196391558667997 52372557989323646834500499)
      ·
        refine ⟨78558836983985470251750749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52372557989323646834500499 78558836983985470251750749)
        ·
          refine ⟨29459563868994551344406531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78558836983985470251750749 29459563868994551344406531)
          ·
            refine ⟨44189345803491827016609797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29459563868994551344406531 44189345803491827016609797)
            ·
              refine ⟨8285502338154717565614337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44189345803491827016609797 8285502338154717565614337)
              ·
                refine ⟨6214126753616038174210753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8285502338154717565614337 6214126753616038174210753)
                ·
                  refine ⟨4660595065212028630658065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6214126753616038174210753 4660595065212028630658065)
                  ·
                    refine ⟨3495446298909021472993549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4660595065212028630658065 3495446298909021472993549)
                    ·
                      refine ⟨1310792362090883052372581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495446298909021472993549 1310792362090883052372581)
                      ·
                        rfl

theorem cell23_2552759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_2552759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552759 prefixEnd_2552759 := by exact prefixLift 2552759
  have htrace : WordTrace (prefixWord ++ tailWord_2552759) baseStart_2552759 baseEnd_2552759 := by
    simpa [prefixWord, tailWord_2552759, baseEnd_2552759] using wordTrace_append hprefix tailTrace_2552759
  have hstable : (prefixWord ++ tailWord_2552759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552759).length < 2 ^ (prefixWord ++ tailWord_2552759).sum := by decide
  have hdescent : baseEnd_2552759 < baseStart_2552759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552846 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2552846 : Nat := 118140960795 + 2552846 * 2 ^ 59
def prefixEnd_2552846 : Nat := 4983230072969 + 3 ^ 40 * 2552846 * 2
def baseEnd_2552846 : Nat := 1310837034907824211984681

theorem tailTrace_2552846 : CollatzResearch.WordTrace tailWord_2552846 prefixEnd_2552846 1310837034907824211984681 := by
  unfold tailWord_2552846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638742863685301028857799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62073295272988272153908261 11638742863685301028857799)
  ·
    refine ⟨17458114295527951543286699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11638742863685301028857799 17458114295527951543286699)
    ·
      refine ⟨26187171443291927314930049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17458114295527951543286699 26187171443291927314930049)
      ·
        refine ⟨19640378582468945486197537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26187171443291927314930049 19640378582468945486197537)
        ·
          refine ⟨14730283936851709114648153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19640378582468945486197537 14730283936851709114648153)
          ·
            refine ⟨11047712952638781835986115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14730283936851709114648153 11047712952638781835986115)
            ·
              refine ⟨16571569428958172753979173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047712952638781835986115 16571569428958172753979173)
              ·
                refine ⟨3107169267929657391371095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16571569428958172753979173 3107169267929657391371095)
                ·
                  refine ⟨4660753901894486087056643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107169267929657391371095 4660753901894486087056643)
                  ·
                    refine ⟨6991130852841729130584965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660753901894486087056643 6991130852841729130584965)
                    ·
                      refine ⟨1310837034907824211984681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6991130852841729130584965 1310837034907824211984681)
                      ·
                        rfl

theorem cell23_2552846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2552846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552846 prefixEnd_2552846 := by exact prefixLift 2552846
  have htrace : WordTrace (prefixWord ++ tailWord_2552846) baseStart_2552846 baseEnd_2552846 := by
    simpa [prefixWord, tailWord_2552846, baseEnd_2552846] using wordTrace_append hprefix tailTrace_2552846
  have hstable : (prefixWord ++ tailWord_2552846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552846).length < 2 ^ (prefixWord ++ tailWord_2552846).sum := by decide
  have hdescent : baseEnd_2552846 < baseStart_2552846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552849 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_2552849 : Nat := 118140960795 + 2552849 * 2 ^ 59
def prefixEnd_2552849 : Nat := 4983230072969 + 3 ^ 40 * 2552849 * 2
def baseEnd_2552849 : Nat := 1310838575349787700247167

theorem tailTrace_2552849 : CollatzResearch.WordTrace tailWord_2552849 prefixEnd_2552849 1310838575349787700247167 := by
  unfold tailWord_2552849
  simp only [CollatzResearch.WordTrace]
  refine ⟨93110052328471539743221601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62073368218981026495481067 93110052328471539743221601)
  ·
    refine ⟨69832539246353654807416201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93110052328471539743221601 69832539246353654807416201)
    ·
      refine ⟨52374404434765241105562151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69832539246353654807416201 52374404434765241105562151)
      ·
        refine ⟨78561606652147861658343227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52374404434765241105562151 78561606652147861658343227)
        ·
          refine ⟨117842409978221792487514841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78561606652147861658343227 117842409978221792487514841)
          ·
            refine ⟨88381807483666344365636131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117842409978221792487514841 88381807483666344365636131)
            ·
              refine ⟨132572711225499516548454197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88381807483666344365636131 132572711225499516548454197)
              ·
                refine ⟨12428691677390579676417581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132572711225499516548454197 12428691677390579676417581)
                ·
                  refine ⟨4660759379021467378656593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12428691677390579676417581 4660759379021467378656593)
                  ·
                    refine ⟨3495569534266100533992445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4660759379021467378656593 3495569534266100533992445)
                    ·
                      refine ⟨1310838575349787700247167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495569534266100533992445 1310838575349787700247167)
                      ·
                        rfl

theorem cell23_2552849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_2552849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552849 prefixEnd_2552849 := by exact prefixLift 2552849
  have htrace : WordTrace (prefixWord ++ tailWord_2552849) baseStart_2552849 baseEnd_2552849 := by
    simpa [prefixWord, tailWord_2552849, baseEnd_2552849] using wordTrace_append hprefix tailTrace_2552849
  have hstable : (prefixWord ++ tailWord_2552849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552849).length < 2 ^ (prefixWord ++ tailWord_2552849).sum := by decide
  have hdescent : baseEnd_2552849 < baseStart_2552849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552866 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_2552866 : Nat := 118140960795 + 2552866 * 2 ^ 59
def prefixEnd_2552866 : Nat := 4983230072969 + 3 ^ 40 * 2552866 * 2
def baseEnd_2552866 : Nat := 1310847304520914133734589

theorem tailTrace_2552866 : CollatzResearch.WordTrace tailWord_2552866 prefixEnd_2552866 1310847304520914133734589 := by
  unfold tailWord_2552866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23277668092352487911647613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62073781579606634431060301 23277668092352487911647613)
  ·
    refine ⟨8729125534632182966867855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23277668092352487911647613 8729125534632182966867855)
    ·
      refine ⟨13093688301948274450301783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8729125534632182966867855 13093688301948274450301783)
      ·
        refine ⟨19640532452922411675452675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13093688301948274450301783 19640532452922411675452675)
        ·
          refine ⟨29460798679383617513179013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19640532452922411675452675 29460798679383617513179013)
          ·
            refine ⟨5523899752384428283721065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29460798679383617513179013 5523899752384428283721065)
            ·
              refine ⟨4142924814288321212790799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5523899752384428283721065 4142924814288321212790799)
              ·
                refine ⟨6214387221432481819186199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142924814288321212790799 6214387221432481819186199)
                ·
                  refine ⟨9321580832148722728779299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6214387221432481819186199 9321580832148722728779299)
                  ·
                    refine ⟨13982371248223084093168949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9321580832148722728779299 13982371248223084093168949)
                    ·
                      refine ⟨1310847304520914133734589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13982371248223084093168949 1310847304520914133734589)
                      ·
                        rfl

theorem cell23_2552866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_2552866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552866 prefixEnd_2552866 := by exact prefixLift 2552866
  have htrace : WordTrace (prefixWord ++ tailWord_2552866) baseStart_2552866 baseEnd_2552866 := by
    simpa [prefixWord, tailWord_2552866, baseEnd_2552866] using wordTrace_append hprefix tailTrace_2552866
  have hstable : (prefixWord ++ tailWord_2552866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552866).length < 2 ^ (prefixWord ++ tailWord_2552866).sum := by decide
  have hdescent : baseEnd_2552866 < baseStart_2552866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552886 : List Nat := [5, 1, 2, 1, 1, 3, 2, 8]
def baseStart_2552886 : Nat := 118140960795 + 2552886 * 2 ^ 59
def prefixEnd_2552886 : Nat := 4983230072969 + 3 ^ 40 * 2552886 * 2
def baseEnd_2552886 : Nat := 48550280523481631684611

theorem tailTrace_2552886 : CollatzResearch.WordTrace tailWord_2552886 prefixEnd_2552886 48550280523481631684611 := by
  unfold tailWord_2552886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819462614333593441394907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62074267886224996708212341 5819462614333593441394907)
  ·
    refine ⟨8729193921500390162092361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5819462614333593441394907 8729193921500390162092361)
    ·
      refine ⟨6546895441125292621569271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8729193921500390162092361 6546895441125292621569271)
      ·
        refine ⟨9820343161687938932353907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6546895441125292621569271 9820343161687938932353907)
        ·
          refine ⟨14730514742531908398530861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9820343161687938932353907 14730514742531908398530861)
          ·
            refine ⟨5523943028449465649449073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14730514742531908398530861 5523943028449465649449073)
            ·
              refine ⟨4142957271337099237086805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5523943028449465649449073 4142957271337099237086805)
              ·
                refine ⟨48550280523481631684611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4142957271337099237086805 48550280523481631684611)
                ·
                  rfl

theorem cell23_2552886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_2552886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552886 prefixEnd_2552886 := by exact prefixLift 2552886
  have htrace : WordTrace (prefixWord ++ tailWord_2552886) baseStart_2552886 baseEnd_2552886 := by
    simpa [prefixWord, tailWord_2552886, baseEnd_2552886] using wordTrace_append hprefix tailTrace_2552886
  have hstable : (prefixWord ++ tailWord_2552886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552886).length < 2 ^ (prefixWord ++ tailWord_2552886).sum := by decide
  have hdescent : baseEnd_2552886 < baseStart_2552886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552930 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2552930 : Nat := 118140960795 + 2552930 * 2 ^ 59
def prefixEnd_2552930 : Nat := 4983230072969 + 3 ^ 40 * 2552930 * 2
def baseEnd_2552930 : Nat := 1310880167282801883334295

theorem tailTrace_2552930 : CollatzResearch.WordTrace tailWord_2552930 prefixEnd_2552930 1310880167282801883334295 := by
  unfold tailWord_2552930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23278251660294522644230061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62075337760785393717946829 23278251660294522644230061)
  ·
    refine ⟨8729344372610445991586273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23278251660294522644230061 8729344372610445991586273)
    ·
      refine ⟨6547008279457834493689705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8729344372610445991586273 6547008279457834493689705)
      ·
        refine ⟨4910256209593375870267279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6547008279457834493689705 4910256209593375870267279)
        ·
          refine ⟨7365384314390063805400919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910256209593375870267279 7365384314390063805400919)
          ·
            refine ⟨11048076471585095708101379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7365384314390063805400919 11048076471585095708101379)
            ·
              refine ⟨16572114707377643562152069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11048076471585095708101379 16572114707377643562152069)
              ·
                refine ⟨3107271507633308167903513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16572114707377643562152069 3107271507633308167903513)
                ·
                  refine ⟨2330453630724981125927635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3107271507633308167903513 2330453630724981125927635)
                  ·
                    refine ⟨3495680446087471688891453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330453630724981125927635 3495680446087471688891453)
                    ·
                      refine ⟨1310880167282801883334295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3495680446087471688891453 1310880167282801883334295)
                      ·
                        rfl

theorem cell23_2552930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2552930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2552930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2552930 prefixEnd_2552930 := by exact prefixLift 2552930
  have htrace : WordTrace (prefixWord ++ tailWord_2552930) baseStart_2552930 baseEnd_2552930 := by
    simpa [prefixWord, tailWord_2552930, baseEnd_2552930] using wordTrace_append hprefix tailTrace_2552930
  have hstable : (prefixWord ++ tailWord_2552930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552930).length < 2 ^ (prefixWord ++ tailWord_2552930).sum := by decide
  have hdescent : baseEnd_2552930 < baseStart_2552930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553029 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2553029 : Nat := 118140960795 + 2553029 * 2 ^ 59
def prefixEnd_2553029 : Nat := 4983230072969 + 3 ^ 40 * 2553029 * 2
def baseEnd_2553029 : Nat := 1310931001867596995996339

theorem tailTrace_2553029 : CollatzResearch.WordTrace tailWord_2553029 prefixEnd_2553029 1310931001867596995996339 := by
  unfold tailWord_2553029
  simp only [CollatzResearch.WordTrace]
  refine ⟨93116617467819430484774141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62077744978546286989849427 93116617467819430484774141)
  ·
    refine ⟨34918731550432286431790303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93116617467819430484774141 34918731550432286431790303)
    ·
      refine ⟨52378097325648429647685455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34918731550432286431790303 52378097325648429647685455)
      ·
        refine ⟨78567145988472644471528183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52378097325648429647685455 78567145988472644471528183)
        ·
          refine ⟨117850718982708966707292275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78567145988472644471528183 117850718982708966707292275)
          ·
            refine ⟨176776078474063450060938413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117850718982708966707292275 176776078474063450060938413)
            ·
              refine ⟨66291029427773793772851905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176776078474063450060938413 66291029427773793772851905)
              ·
                refine ⟨49718272070830345329638929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66291029427773793772851905 49718272070830345329638929)
                ·
                  refine ⟨37288704053122758997229197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49718272070830345329638929 37288704053122758997229197)
                  ·
                    refine ⟨13983264019921034623960949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37288704053122758997229197 13983264019921034623960949)
                    ·
                      refine ⟨1310931001867596995996339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13983264019921034623960949 1310931001867596995996339)
                      ·
                        rfl

theorem cell23_2553029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2553029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553029 prefixEnd_2553029 := by exact prefixLift 2553029
  have htrace : WordTrace (prefixWord ++ tailWord_2553029) baseStart_2553029 baseEnd_2553029 := by
    simpa [prefixWord, tailWord_2553029, baseEnd_2553029] using wordTrace_append hprefix tailTrace_2553029
  have hstable : (prefixWord ++ tailWord_2553029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553029).length < 2 ^ (prefixWord ++ tailWord_2553029).sum := by decide
  have hdescent : baseEnd_2553029 < baseStart_2553029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553039 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_2553039 : Nat := 118140960795 + 2553039 * 2 ^ 59
def prefixEnd_2553039 : Nat := 4983230072969 + 3 ^ 40 * 2553039 * 2
def baseEnd_2553039 : Nat := 1310936136674141956871293

theorem tailTrace_2553039 : CollatzResearch.WordTrace tailWord_2553039 prefixEnd_2553039 1310936136674141956871293 := by
  unfold tailWord_2553039
  simp only [CollatzResearch.WordTrace]
  refine ⟨93116982197783202192638171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62077988131855468128425447 93116982197783202192638171)
  ·
    refine ⟨139675473296674803288957257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93116982197783202192638171 139675473296674803288957257)
    ·
      refine ⟨104756604972506102466717943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139675473296674803288957257 104756604972506102466717943)
      ·
        refine ⟨157134907458759153700076915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104756604972506102466717943 157134907458759153700076915)
        ·
          refine ⟨235702361188138730550115373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157134907458759153700076915 235702361188138730550115373)
          ·
            refine ⟨88388385445552023956293265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235702361188138730550115373 88388385445552023956293265)
            ·
              refine ⟨66291289084164017967219949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88388385445552023956293265 66291289084164017967219949)
              ·
                refine ⟨24859233406561506737707481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66291289084164017967219949 24859233406561506737707481)
                ·
                  refine ⟨18644425054921130053280611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24859233406561506737707481 18644425054921130053280611)
                  ·
                    refine ⟨27966637582381695079920917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18644425054921130053280611 27966637582381695079920917)
                    ·
                      refine ⟨1310936136674141956871293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27966637582381695079920917 1310936136674141956871293)
                      ·
                        rfl

theorem cell23_2553039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_2553039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553039 prefixEnd_2553039 := by exact prefixLift 2553039
  have htrace : WordTrace (prefixWord ++ tailWord_2553039) baseStart_2553039 baseEnd_2553039 := by
    simpa [prefixWord, tailWord_2553039, baseEnd_2553039] using wordTrace_append hprefix tailTrace_2553039
  have hstable : (prefixWord ++ tailWord_2553039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553039).length < 2 ^ (prefixWord ++ tailWord_2553039).sum := by decide
  have hdescent : baseEnd_2553039 < baseStart_2553039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553079 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 9]
def baseStart_2553079 : Nat := 118140960795 + 2553079 * 2 ^ 59
def prefixEnd_2553079 : Nat := 4983230072969 + 3 ^ 40 * 2553079 * 2
def baseEnd_2553079 : Nat := 436985558633440600123703

theorem tailTrace_2553079 : CollatzResearch.WordTrace tailWord_2553079 prefixEnd_2553079 436985558633440600123703 := by
  unfold tailWord_2553079
  simp only [CollatzResearch.WordTrace]
  refine ⟨93118441117638289024094291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62078960745092192682729527 93118441117638289024094291)
  ·
    refine ⟨139677661676457433536141437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93118441117638289024094291 139677661676457433536141437)
    ·
      refine ⟨52379123128671537576053039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139677661676457433536141437 52379123128671537576053039)
      ·
        refine ⟨78568684693007306364079559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52379123128671537576053039 78568684693007306364079559)
        ·
          refine ⟨117853027039510959546119339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78568684693007306364079559 117853027039510959546119339)
          ·
            refine ⟨176779540559266439319179009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117853027039510959546119339 176779540559266439319179009)
            ·
              refine ⟨132584655419449829489384257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176779540559266439319179009 132584655419449829489384257)
              ·
                refine ⟨99438491564587372117038193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132584655419449829489384257 99438491564587372117038193)
                ·
                  refine ⟨74578868673440529087778645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99438491564587372117038193 74578868673440529087778645)
                  ·
                    refine ⟨436985558633440600123703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74578868673440529087778645 436985558633440600123703)
                    ·
                      rfl

theorem cell23_2553079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_2553079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553079 prefixEnd_2553079 := by exact prefixLift 2553079
  have htrace : WordTrace (prefixWord ++ tailWord_2553079) baseStart_2553079 baseEnd_2553079 := by
    simpa [prefixWord, tailWord_2553079, baseEnd_2553079] using wordTrace_append hprefix tailTrace_2553079
  have hstable : (prefixWord ++ tailWord_2553079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553079).length < 2 ^ (prefixWord ++ tailWord_2553079).sum := by decide
  have hdescent : baseEnd_2553079 < baseStart_2553079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553137 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_2553137 : Nat := 118140960795 + 2553137 * 2 ^ 59
def prefixEnd_2553137 : Nat := 4983230072969 + 3 ^ 40 * 2553137 * 2
def baseEnd_2553137 : Nat := 1310986457778282573445843

theorem tailTrace_2553137 : CollatzResearch.WordTrace tailWord_2553137 prefixEnd_2553137 1310986457778282573445843 := by
  unfold tailWord_2553137
  simp only [CollatzResearch.WordTrace]
  refine ⟨93120556551428164929705665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62080371034285443286470443 93120556551428164929705665)
  ·
    refine ⟨69840417413571123697279249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93120556551428164929705665 69840417413571123697279249)
    ·
      refine ⟨52380313060178342772959437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69840417413571123697279249 52380313060178342772959437)
      ·
        refine ⟨19642617397566878539859789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52380313060178342772959437 19642617397566878539859789)
        ·
          refine ⟨7365981524087579452447421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19642617397566878539859789 7365981524087579452447421)
          ·
            refine ⟨2762243071532842294667783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7365981524087579452447421 2762243071532842294667783)
            ·
              refine ⟨4143364607299263442001675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762243071532842294667783 4143364607299263442001675)
              ·
                refine ⟨6215046910948895163002513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143364607299263442001675 6215046910948895163002513)
                ·
                  refine ⟨4661285183211671372251885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215046910948895163002513 4661285183211671372251885)
                  ·
                    refine ⟨1747981943704376764594457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4661285183211671372251885 1747981943704376764594457)
                    ·
                      refine ⟨1310986457778282573445843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1747981943704376764594457 1310986457778282573445843)
                      ·
                        rfl

theorem cell23_2553137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_2553137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553137 prefixEnd_2553137 := by exact prefixLift 2553137
  have htrace : WordTrace (prefixWord ++ tailWord_2553137) baseStart_2553137 baseEnd_2553137 := by
    simpa [prefixWord, tailWord_2553137, baseEnd_2553137] using wordTrace_append hprefix tailTrace_2553137
  have hstable : (prefixWord ++ tailWord_2553137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553137).length < 2 ^ (prefixWord ++ tailWord_2553137).sum := by decide
  have hdescent : baseEnd_2553137 < baseStart_2553137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553150 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2553150 : Nat := 118140960795 + 2553150 * 2 ^ 59
def prefixEnd_2553150 : Nat := 4983230072969 + 3 ^ 40 * 2553150 * 2
def baseEnd_2553150 : Nat := 1310993133026791022583283

theorem tailTrace_2553150 : CollatzResearch.WordTrace tailWord_2553150 prefixEnd_2553150 1310993133026791022583283 := by
  unfold tailWord_2553150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11640128837547633518741113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62080687133587378766619269 11640128837547633518741113)
  ·
    refine ⟨8730096628160725139055835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11640128837547633518741113 8730096628160725139055835)
    ·
      refine ⟨13095144942241087708583753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8730096628160725139055835 13095144942241087708583753)
      ·
        refine ⟨9821358706680815781437815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13095144942241087708583753 9821358706680815781437815)
        ·
          refine ⟨14732038060021223672156723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9821358706680815781437815 14732038060021223672156723)
          ·
            refine ⟨22098057090031835508235085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14732038060021223672156723 22098057090031835508235085)
            ·
              refine ⟨8286771408761938315588157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22098057090031835508235085 8286771408761938315588157)
              ·
                refine ⟨3107539278285726868345559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8286771408761938315588157 3107539278285726868345559)
                ·
                  refine ⟨4661308917428590302518339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107539278285726868345559 4661308917428590302518339)
                  ·
                    refine ⟨6991963376142885453777509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4661308917428590302518339 6991963376142885453777509)
                    ·
                      refine ⟨1310993133026791022583283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6991963376142885453777509 1310993133026791022583283)
                      ·
                        rfl

theorem cell23_2553150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2553150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553150 prefixEnd_2553150 := by exact prefixLift 2553150
  have htrace : WordTrace (prefixWord ++ tailWord_2553150) baseStart_2553150 baseEnd_2553150 := by
    simpa [prefixWord, tailWord_2553150, baseEnd_2553150] using wordTrace_append hprefix tailTrace_2553150
  have hstable : (prefixWord ++ tailWord_2553150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553150).length < 2 ^ (prefixWord ++ tailWord_2553150).sum := by decide
  have hdescent : baseEnd_2553150 < baseStart_2553150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553216 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_2553216 : Nat := 118140960795 + 2553216 * 2 ^ 59
def prefixEnd_2553216 : Nat := 4983230072969 + 3 ^ 40 * 2553216 * 2
def baseEnd_2553216 : Nat := 437009007583329254785993

theorem tailTrace_2553216 : CollatzResearch.WordTrace tailWord_2553216 prefixEnd_2553216 437009007583329254785993 := by
  unfold tailWord_2553216
  simp only [CollatzResearch.WordTrace]
  refine ⟨46561718959070980710915751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62082291945427974281221001 46561718959070980710915751)
  ·
    refine ⟨69842578438606471066373627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46561718959070980710915751 69842578438606471066373627)
    ·
      refine ⟨104763867657909706599560441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69842578438606471066373627 104763867657909706599560441)
      ·
        refine ⟨78572900743432279949670331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104763867657909706599560441 78572900743432279949670331)
        ·
          refine ⟨117859351115148419924505497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78572900743432279949670331 117859351115148419924505497)
          ·
            refine ⟨88394513336361314943379123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117859351115148419924505497 88394513336361314943379123)
            ·
              refine ⟨132591770004541972415068685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88394513336361314943379123 132591770004541972415068685)
              ·
                refine ⟨49721913751703239655650757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132591770004541972415068685 49721913751703239655650757)
                ·
                  refine ⟨9322858828444357435434517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49721913751703239655650757 9322858828444357435434517)
                  ·
                    refine ⟨437009007583329254785993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9322858828444357435434517 437009007583329254785993)
                    ·
                      rfl

theorem cell23_2553216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_2553216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553216 prefixEnd_2553216 := by exact prefixLift 2553216
  have htrace : WordTrace (prefixWord ++ tailWord_2553216) baseStart_2553216 baseEnd_2553216 := by
    simpa [prefixWord, tailWord_2553216, baseEnd_2553216] using wordTrace_append hprefix tailTrace_2553216
  have hstable : (prefixWord ++ tailWord_2553216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553216).length < 2 ^ (prefixWord ++ tailWord_2553216).sum := by decide
  have hdescent : baseEnd_2553216 < baseStart_2553216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553244 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2553244 : Nat := 118140960795 + 2553244 * 2 ^ 59
def prefixEnd_2553244 : Nat := 4983230072969 + 3 ^ 40 * 2553244 * 2
def baseEnd_2553244 : Nat := 1311041400208313654807851

theorem tailTrace_2553244 : CollatzResearch.WordTrace tailWord_2553244 prefixEnd_2553244 1311041400208313654807851 := by
  unfold tailWord_2553244
  simp only [CollatzResearch.WordTrace]
  refine ⟨46562229581020261101925393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62082972774693681469233857 46562229581020261101925393)
  ·
    refine ⟨34921672185765195826444045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46562229581020261101925393 34921672185765195826444045)
    ·
      refine ⟨13095627069661948434916517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34921672185765195826444045 13095627069661948434916517)
      ·
        refine ⟨2455430075561615331546847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13095627069661948434916517 2455430075561615331546847)
        ·
          refine ⟨3683145113342422997320271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455430075561615331546847 3683145113342422997320271)
          ·
            refine ⟨5524717670013634495980407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683145113342422997320271 5524717670013634495980407)
            ·
              refine ⟨8287076505020451743970611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524717670013634495980407 8287076505020451743970611)
              ·
                refine ⟨12430614757530677615955917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287076505020451743970611 12430614757530677615955917)
                ·
                  refine ⟨4661480534074004105983469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12430614757530677615955917 4661480534074004105983469)
                  ·
                    refine ⟨1748055200277751539743801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4661480534074004105983469 1748055200277751539743801)
                    ·
                      refine ⟨1311041400208313654807851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748055200277751539743801 1311041400208313654807851)
                      ·
                        rfl

theorem cell23_2553244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2553244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553244 prefixEnd_2553244 := by exact prefixLift 2553244
  have htrace : WordTrace (prefixWord ++ tailWord_2553244) baseStart_2553244 baseEnd_2553244 := by
    simpa [prefixWord, tailWord_2553244, baseEnd_2553244] using wordTrace_append hprefix tailTrace_2553244
  have hstable : (prefixWord ++ tailWord_2553244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553244).length < 2 ^ (prefixWord ++ tailWord_2553244).sum := by decide
  have hdescent : baseEnd_2553244 < baseStart_2553244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553261 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2553261 : Nat := 118140960795 + 2553261 * 2 ^ 59
def prefixEnd_2553261 : Nat := 4983230072969 + 3 ^ 40 * 2553261 * 2
def baseEnd_2553261 : Nat := 1311050129379440088295273

theorem tailTrace_2553261 : CollatzResearch.WordTrace tailWord_2553261 prefixEnd_2553261 1311050129379440088295273 := by
  unfold tailWord_2553261
  simp only [CollatzResearch.WordTrace]
  refine ⟨93125079202978934107219637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62083386135319289404813091 93125079202978934107219637)
  ·
    refine ⟨8730476175279275072551841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93125079202978934107219637 8730476175279275072551841)
    ·
      refine ⟨6547857131459456304413881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8730476175279275072551841 6547857131459456304413881)
      ·
        refine ⟨4910892848594592228310411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6547857131459456304413881 4910892848594592228310411)
        ·
          refine ⟨7366339272891888342465617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910892848594592228310411 7366339272891888342465617)
          ·
            refine ⟨5524754454668916256849213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7366339272891888342465617 5524754454668916256849213)
            ·
              refine ⟨2071782920500843596318455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5524754454668916256849213 2071782920500843596318455)
              ·
                refine ⟨3107674380751265394477683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071782920500843596318455 3107674380751265394477683)
                ·
                  refine ⟨4661511571126898091716525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107674380751265394477683 4661511571126898091716525)
                  ·
                    refine ⟨1748066839172586784393697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4661511571126898091716525 1748066839172586784393697)
                    ·
                      refine ⟨1311050129379440088295273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748066839172586784393697 1311050129379440088295273)
                      ·
                        rfl

theorem cell23_2553261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2553261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553261 prefixEnd_2553261 := by exact prefixLift 2553261
  have htrace : WordTrace (prefixWord ++ tailWord_2553261) baseStart_2553261 baseEnd_2553261 := by
    simpa [prefixWord, tailWord_2553261, baseEnd_2553261] using wordTrace_append hprefix tailTrace_2553261
  have hstable : (prefixWord ++ tailWord_2553261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553261).length < 2 ^ (prefixWord ++ tailWord_2553261).sum := by decide
  have hdescent : baseEnd_2553261 < baseStart_2553261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553290 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_2553290 : Nat := 118140960795 + 2553290 * 2 ^ 59
def prefixEnd_2553290 : Nat := 4983230072969 + 3 ^ 40 * 2553290 * 2
def baseEnd_2553290 : Nat := 1311065020318420474832639

theorem tailTrace_2553290 : CollatzResearch.WordTrace tailWord_2553290 prefixEnd_2553290 1311065020318420474832639 := by
  unfold tailWord_2553290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23281534229968468015006331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62084091279915914706683549 23281534229968468015006331)
  ·
    refine ⟨34922301344952702022509497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23281534229968468015006331 34922301344952702022509497)
    ·
      refine ⟨26191726008714526516882123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34922301344952702022509497 26191726008714526516882123)
      ·
        refine ⟨39287589013071789775323185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26191726008714526516882123 39287589013071789775323185)
        ·
          refine ⟨29465691759803842331492389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39287589013071789775323185 29465691759803842331492389)
          ·
            refine ⟨5524817204963220437154823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29465691759803842331492389 5524817204963220437154823)
            ·
              refine ⟨8287225807444830655732235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524817204963220437154823 8287225807444830655732235)
              ·
                refine ⟨12430838711167245983598353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287225807444830655732235 12430838711167245983598353)
                ·
                  refine ⟨9323129033375434487698765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12430838711167245983598353 9323129033375434487698765)
                  ·
                    refine ⟨3496173387515787932887037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9323129033375434487698765 3496173387515787932887037)
                    ·
                      refine ⟨1311065020318420474832639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3496173387515787932887037 1311065020318420474832639)
                      ·
                        rfl

theorem cell23_2553290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_2553290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553290 prefixEnd_2553290 := by exact prefixLift 2553290
  have htrace : WordTrace (prefixWord ++ tailWord_2553290) baseStart_2553290 baseEnd_2553290 := by
    simpa [prefixWord, tailWord_2553290, baseEnd_2553290] using wordTrace_append hprefix tailTrace_2553290
  have hstable : (prefixWord ++ tailWord_2553290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553290).length < 2 ^ (prefixWord ++ tailWord_2553290).sum := by decide
  have hdescent : baseEnd_2553290 < baseStart_2553290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553340 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_2553340 : Nat := 118140960795 + 2553340 * 2 ^ 59
def prefixEnd_2553340 : Nat := 4983230072969 + 3 ^ 40 * 2553340 * 2
def baseEnd_2553340 : Nat := 437030231450381759735803

theorem tailTrace_2553340 : CollatzResearch.WordTrace tailWord_2553340 prefixEnd_2553340 437030231450381759735803 := by
  unfold tailWord_2553340
  simp only [CollatzResearch.WordTrace]
  refine ⟨46563980284846365299672737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62085307046461820399563649 46563980284846365299672737)
  ·
    refine ⟨34922985213634773974754553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46563980284846365299672737 34922985213634773974754553)
    ·
      refine ⟨26192238910226080481065915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34922985213634773974754553 26192238910226080481065915)
      ·
        refine ⟨39288358365339120721598873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26192238910226080481065915 39288358365339120721598873)
        ·
          refine ⟨29466268774004340541199155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39288358365339120721598873 29466268774004340541199155)
          ·
            refine ⟨44199403161006510811798733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29466268774004340541199155 44199403161006510811798733)
            ·
              refine ⟨16574776185377441554424525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44199403161006510811798733 16574776185377441554424525)
              ·
                refine ⟨6215541069516540582909197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16574776185377441554424525 6215541069516540582909197)
                ·
                  refine ⟨2330827901068702718590949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6215541069516540582909197 2330827901068702718590949)
                  ·
                    refine ⟨437030231450381759735803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2330827901068702718590949 437030231450381759735803)
                    ·
                      rfl

theorem cell23_2553340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_2553340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553340 prefixEnd_2553340 := by exact prefixLift 2553340
  have htrace : WordTrace (prefixWord ++ tailWord_2553340) baseStart_2553340 baseEnd_2553340 := by
    simpa [prefixWord, tailWord_2553340, baseEnd_2553340] using wordTrace_append hprefix tailTrace_2553340
  have hstable : (prefixWord ++ tailWord_2553340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553340).length < 2 ^ (prefixWord ++ tailWord_2553340).sum := by decide
  have hdescent : baseEnd_2553340 < baseStart_2553340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553384 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2553384 : Nat := 118140960795 + 2553384 * 2 ^ 59
def prefixEnd_2553384 : Nat := 4983230072969 + 3 ^ 40 * 2553384 * 2
def baseEnd_2553384 : Nat := 1311113287499943107057207

theorem tailTrace_2553384 : CollatzResearch.WordTrace tailWord_2553384 prefixEnd_2553384 1311113287499943107057207 := by
  unfold tailWord_2553384
  simp only [CollatzResearch.WordTrace]
  refine ⟨46564782690766663056973603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62086376921022217409298137 46564782690766663056973603)
  ·
    refine ⟨69847174036149994585460405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46564782690766663056973603 69847174036149994585460405)
    ·
      refine ⟨6548172565889061992386913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69847174036149994585460405 6548172565889061992386913)
      ·
        refine ⟨4911129424416796494290185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548172565889061992386913 4911129424416796494290185)
        ·
          refine ⟨3683347068312597370717639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4911129424416796494290185 3683347068312597370717639)
          ·
            refine ⟨5525020602468896056076459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683347068312597370717639 5525020602468896056076459)
            ·
              refine ⟨8287530903703344084114689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525020602468896056076459 8287530903703344084114689)
              ·
                refine ⟨6215648177777508063086017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8287530903703344084114689 6215648177777508063086017)
                ·
                  refine ⟨4661736133333131047314513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215648177777508063086017 4661736133333131047314513)
                  ·
                    refine ⟨3496302099999848285485885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4661736133333131047314513 3496302099999848285485885)
                    ·
                      refine ⟨1311113287499943107057207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3496302099999848285485885 1311113287499943107057207)
                      ·
                        rfl

theorem cell23_2553384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2553384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553384 prefixEnd_2553384 := by exact prefixLift 2553384
  have htrace : WordTrace (prefixWord ++ tailWord_2553384) baseStart_2553384 baseEnd_2553384 := by
    simpa [prefixWord, tailWord_2553384, baseEnd_2553384] using wordTrace_append hprefix tailTrace_2553384
  have hstable : (prefixWord ++ tailWord_2553384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553384).length < 2 ^ (prefixWord ++ tailWord_2553384).sum := by decide
  have hdescent : baseEnd_2553384 < baseStart_2553384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553393 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2553393 : Nat := 118140960795 + 2553393 * 2 ^ 59
def prefixEnd_2553393 : Nat := 4983230072969 + 3 ^ 40 * 2553393 * 2
def baseEnd_2553393 : Nat := 1311117908825833571844665

theorem tailTrace_2553393 : CollatzResearch.WordTrace tailWord_2553393 prefixEnd_2553393 1311117908825833571844665 := by
  unfold tailWord_2553393
  simp only [CollatzResearch.WordTrace]
  refine ⟨93129893638500720651024833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62086595759000480434016555 93129893638500720651024833)
  ·
    refine ⟨69847420228875540488268625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93129893638500720651024833 69847420228875540488268625)
    ·
      refine ⟨52385565171656655366201469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69847420228875540488268625 52385565171656655366201469)
      ·
        refine ⟨19644586939371245762325551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52385565171656655366201469 19644586939371245762325551)
        ·
          refine ⟨29466880409056868643488327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19644586939371245762325551 29466880409056868643488327)
          ·
            refine ⟨44200320613585302965232491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29466880409056868643488327 44200320613585302965232491)
            ·
              refine ⟨66300480920377954447848737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44200320613585302965232491 66300480920377954447848737)
              ·
                refine ⟨49725360690283465835886553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66300480920377954447848737 49725360690283465835886553)
                ·
                  refine ⟨37294020517712599376914915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49725360690283465835886553 37294020517712599376914915)
                  ·
                    refine ⟨55941030776568899065372373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37294020517712599376914915 55941030776568899065372373)
                    ·
                      refine ⟨1311117908825833571844665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55941030776568899065372373 1311117908825833571844665)
                      ·
                        rfl

theorem cell23_2553393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2553393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553393 prefixEnd_2553393 := by exact prefixLift 2553393
  have htrace : WordTrace (prefixWord ++ tailWord_2553393) baseStart_2553393 baseEnd_2553393 := by
    simpa [prefixWord, tailWord_2553393, baseEnd_2553393] using wordTrace_append hprefix tailTrace_2553393
  have hstable : (prefixWord ++ tailWord_2553393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553393).length < 2 ^ (prefixWord ++ tailWord_2553393).sum := by decide
  have hdescent : baseEnd_2553393 < baseStart_2553393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553404 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 6]
def baseStart_2553404 : Nat := 118140960795 + 2553404 * 2 ^ 59
def prefixEnd_2553404 : Nat := 4983230072969 + 3 ^ 40 * 2553404 * 2
def baseEnd_2553404 : Nat := 145680395234781447645235

theorem tailTrace_2553404 : CollatzResearch.WordTrace tailWord_2553404 prefixEnd_2553404 145680395234781447645235 := by
  unfold tailWord_2553404
  simp only [CollatzResearch.WordTrace]
  refine ⟨46565147420730434764837633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62086863227640579686450177 46565147420730434764837633)
  ·
    refine ⟨34923860565547826073628225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46565147420730434764837633 34923860565547826073628225)
    ·
      refine ⟨26192895424160869555221169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34923860565547826073628225 26192895424160869555221169)
      ·
        refine ⟨19644671568120652166415877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26192895424160869555221169 19644671568120652166415877)
        ·
          refine ⟨3683375919022622281202977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19644671568120652166415877 3683375919022622281202977)
          ·
            refine ⟨2762531939266966710902233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683375919022622281202977 2762531939266966710902233)
            ·
              refine ⟨2071898954450225033176675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762531939266966710902233 2071898954450225033176675)
              ·
                refine ⟨3107848431675337549765013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071898954450225033176675 3107848431675337549765013)
                ·
                  refine ⟨145680395234781447645235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3107848431675337549765013 145680395234781447645235)
                  ·
                    rfl

theorem cell23_2553404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_2553404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553404 prefixEnd_2553404 := by exact prefixLift 2553404
  have htrace : WordTrace (prefixWord ++ tailWord_2553404) baseStart_2553404 baseEnd_2553404 := by
    simpa [prefixWord, tailWord_2553404, baseEnd_2553404] using wordTrace_append hprefix tailTrace_2553404
  have hstable : (prefixWord ++ tailWord_2553404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553404).length < 2 ^ (prefixWord ++ tailWord_2553404).sum := by decide
  have hdescent : baseEnd_2553404 < baseStart_2553404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553443 : List Nat := [1, 1, 1, 5, 1, 14]
def baseStart_2553443 : Nat := 118140960795 + 2553443 * 2 ^ 59
def prefixEnd_2553443 : Nat := 4983230072969 + 3 ^ 40 * 2553443 * 2
def baseEnd_2553443 : Nat := 5395652604356207309545

theorem tailTrace_2553443 : CollatzResearch.WordTrace tailWord_2553443 prefixEnd_2553443 5395652604356207309545 := by
  unfold tailWord_2553443
  simp only [CollatzResearch.WordTrace]
  refine ⟨93131717288319579190344983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62087811525546386126896655 93131717288319579190344983)
  ·
    refine ⟨139697575932479368785517475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93131717288319579190344983 139697575932479368785517475)
    ·
      refine ⟨209546363898719053178276213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139697575932479368785517475 209546363898719053178276213)
      ·
        refine ⟨19644971615504911235463395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209546363898719053178276213 19644971615504911235463395)
        ·
          refine ⟨29467457423257366853195093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19644971615504911235463395 29467457423257366853195093)
          ·
            refine ⟨5395652604356207309545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 29467457423257366853195093 5395652604356207309545)
            ·
              rfl

theorem cell23_2553443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 14].length) (baseStart_2553443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553443 prefixEnd_2553443 := by exact prefixLift 2553443
  have htrace : WordTrace (prefixWord ++ tailWord_2553443) baseStart_2553443 baseEnd_2553443 := by
    simpa [prefixWord, tailWord_2553443, baseEnd_2553443] using wordTrace_append hprefix tailTrace_2553443
  have hstable : (prefixWord ++ tailWord_2553443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553443).length < 2 ^ (prefixWord ++ tailWord_2553443).sum := by decide
  have hdescent : baseEnd_2553443 < baseStart_2553443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553447 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2553447 : Nat := 118140960795 + 2553447 * 2 ^ 59
def prefixEnd_2553447 : Nat := 4983230072969 + 3 ^ 40 * 2553447 * 2
def baseEnd_2553447 : Nat := 437048545593725453523139

theorem tailTrace_2553447 : CollatzResearch.WordTrace tailWord_2553447 prefixEnd_2553447 437048545593725453523139 := by
  unfold tailWord_2553447
  simp only [CollatzResearch.WordTrace]
  refine ⟨93131863180305087873490595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62087908786870058582327063 93131863180305087873490595)
  ·
    refine ⟨139697794770457631810235893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93131863180305087873490595 139697794770457631810235893)
    ·
      refine ⟨13096668259730402982209615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139697794770457631810235893 13096668259730402982209615)
      ·
        refine ⟨19645002389595604473314423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13096668259730402982209615 19645002389595604473314423)
        ·
          refine ⟨29467503584393406709971635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19645002389595604473314423 29467503584393406709971635)
          ·
            refine ⟨44201255376590110064957453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29467503584393406709971635 44201255376590110064957453)
            ·
              refine ⟨16575470766221291274359045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44201255376590110064957453 16575470766221291274359045)
              ·
                refine ⟨3107900768666492113942321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16575470766221291274359045 3107900768666492113942321)
                ·
                  refine ⟨2330925576499869085456741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3107900768666492113942321 2330925576499869085456741)
                  ·
                    refine ⟨437048545593725453523139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2330925576499869085456741 437048545593725453523139)
                    ·
                      rfl

theorem cell23_2553447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2553447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553447 prefixEnd_2553447 := by exact prefixLift 2553447
  have htrace : WordTrace (prefixWord ++ tailWord_2553447) baseStart_2553447 baseEnd_2553447 := by
    simpa [prefixWord, tailWord_2553447, baseEnd_2553447] using wordTrace_append hprefix tailTrace_2553447
  have hstable : (prefixWord ++ tailWord_2553447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553447).length < 2 ^ (prefixWord ++ tailWord_2553447).sum := by decide
  have hdescent : baseEnd_2553447 < baseStart_2553447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553448 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2553448 : Nat := 118140960795 + 2553448 * 2 ^ 59
def prefixEnd_2553448 : Nat := 4983230072969 + 3 ^ 40 * 2553448 * 2
def baseEnd_2553448 : Nat := 1311146150261830856656913

theorem tailTrace_2553448 : CollatzResearch.WordTrace tailWord_2553448 prefixEnd_2553448 1311146150261830856656913 := by
  unfold tailWord_2553448
  simp only [CollatzResearch.WordTrace]
  refine ⟨46565949826650732522138499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62087933102200976696184665 46565949826650732522138499)
  ·
    refine ⟨69848924739976098783207749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46565949826650732522138499 69848924739976098783207749)
    ·
      refine ⟨13096673388745518521851453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69848924739976098783207749 13096673388745518521851453)
      ·
        refine ⟨4911252520779569445694295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13096673388745518521851453 4911252520779569445694295)
        ·
          refine ⟨7366878781169354168541443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911252520779569445694295 7366878781169354168541443)
          ·
            refine ⟨11050318171754031252812165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366878781169354168541443 11050318171754031252812165)
            ·
              refine ⟨2071934657203880859902281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11050318171754031252812165 2071934657203880859902281)
              ·
                refine ⟨1553950992902910644926711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071934657203880859902281 1553950992902910644926711)
                ·
                  refine ⟨2330926489354365967390067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553950992902910644926711 2330926489354365967390067)
                  ·
                    refine ⟨3496389734031548951085101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330926489354365967390067 3496389734031548951085101)
                    ·
                      refine ⟨1311146150261830856656913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3496389734031548951085101 1311146150261830856656913)
                      ·
                        rfl

theorem cell23_2553448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2553448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553448 prefixEnd_2553448 := by exact prefixLift 2553448
  have htrace : WordTrace (prefixWord ++ tailWord_2553448) baseStart_2553448 baseEnd_2553448 := by
    simpa [prefixWord, tailWord_2553448, baseEnd_2553448] using wordTrace_append hprefix tailTrace_2553448
  have hstable : (prefixWord ++ tailWord_2553448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553448).length < 2 ^ (prefixWord ++ tailWord_2553448).sum := by decide
  have hdescent : baseEnd_2553448 < baseStart_2553448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553497 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 5, 3, 2]
def baseStart_2553497 : Nat := 118140960795 + 2553497 * 2 ^ 59
def prefixEnd_2553497 : Nat := 4983230072969 + 3 ^ 40 * 2553497 * 2
def baseEnd_2553497 : Nat := 1311171310813901164944187

theorem tailTrace_2553497 : CollatzResearch.WordTrace tailWord_2553497 prefixEnd_2553497 1311171310813901164944187 := by
  unfold tailWord_2553497
  simp only [CollatzResearch.WordTrace]
  refine ⟨93133686830123946412810745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62089124553415964275207163 93133686830123946412810745)
  ·
    refine ⟨69850265122592959809608059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93133686830123946412810745 69850265122592959809608059)
    ·
      refine ⟨104775397683889439714412089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69850265122592959809608059 104775397683889439714412089)
      ·
        refine ⟨78581548262917079785809067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104775397683889439714412089 78581548262917079785809067)
        ·
          refine ⟨117872322394375619678713601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78581548262917079785809067 117872322394375619678713601)
          ·
            refine ⟨88404241795781714759035201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117872322394375619678713601 88404241795781714759035201)
            ·
              refine ⟨66303181346836286069276401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88404241795781714759035201 66303181346836286069276401)
              ·
                refine ⟨49727386010127214551957301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66303181346836286069276401 49727386010127214551957301)
                ·
                  refine ⟨4661942438449426364245997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49727386010127214551957301 4661942438449426364245997)
                  ·
                    refine ⟨1748228414418534886592249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4661942438449426364245997 1748228414418534886592249)
                    ·
                      refine ⟨1311171310813901164944187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748228414418534886592249 1311171310813901164944187)
                      ·
                        rfl

theorem cell23_2553497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_2553497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553497 prefixEnd_2553497 := by exact prefixLift 2553497
  have htrace : WordTrace (prefixWord ++ tailWord_2553497) baseStart_2553497 baseEnd_2553497 := by
    simpa [prefixWord, tailWord_2553497, baseEnd_2553497] using wordTrace_append hprefix tailTrace_2553497
  have hstable : (prefixWord ++ tailWord_2553497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553497).length < 2 ^ (prefixWord ++ tailWord_2553497).sum := by decide
  have hdescent : baseEnd_2553497 < baseStart_2553497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553504 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2553504 : Nat := 118140960795 + 2553504 * 2 ^ 59
def prefixEnd_2553504 : Nat := 4983230072969 + 3 ^ 40 * 2553504 * 2
def baseEnd_2553504 : Nat := 1311174905178482637556655

theorem tailTrace_2553504 : CollatzResearch.WordTrace tailWord_2553504 prefixEnd_2553504 1311174905178482637556655 := by
  unfold tailWord_2553504
  simp only [CollatzResearch.WordTrace]
  refine ⟨46566971070549293304157783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62089294760732391072210377 46566971070549293304157783)
  ·
    refine ⟨69850456605823939956236675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46566971070549293304157783 69850456605823939956236675)
    ·
      refine ⟨104775684908735909934355013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69850456605823939956236675 104775684908735909934355013)
      ·
        refine ⟨19645440920387983112691565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104775684908735909934355013 19645440920387983112691565)
        ·
          refine ⟨7367040345145493667259337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19645440920387983112691565 7367040345145493667259337)
          ·
            refine ⟨5525280258859120250444503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7367040345145493667259337 5525280258859120250444503)
            ·
              refine ⟨8287920388288680375666755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525280258859120250444503 8287920388288680375666755)
              ·
                refine ⟨12431880582433020563500133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287920388288680375666755 12431880582433020563500133)
                ·
                  refine ⟨2330977609206191355656275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12431880582433020563500133 2330977609206191355656275)
                  ·
                    refine ⟨3496466413809287033484413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330977609206191355656275 3496466413809287033484413)
                    ·
                      refine ⟨1311174905178482637556655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3496466413809287033484413 1311174905178482637556655)
                      ·
                        rfl

theorem cell23_2553504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2553504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553504 prefixEnd_2553504 := by exact prefixLift 2553504
  have htrace : WordTrace (prefixWord ++ tailWord_2553504) baseStart_2553504 baseEnd_2553504 := by
    simpa [prefixWord, tailWord_2553504, baseEnd_2553504] using wordTrace_append hprefix tailTrace_2553504
  have hstable : (prefixWord ++ tailWord_2553504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553504).length < 2 ^ (prefixWord ++ tailWord_2553504).sum := by decide
  have hdescent : baseEnd_2553504 < baseStart_2553504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553518 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2553518 : Nat := 118140960795 + 2553518 * 2 ^ 59
def prefixEnd_2553518 : Nat := 4983230072969 + 3 ^ 40 * 2553518 * 2
def baseEnd_2553518 : Nat := 1311182093907645582781591

theorem tailTrace_2553518 : CollatzResearch.WordTrace tailWord_2553518 prefixEnd_2553518 1311182093907645582781591 := by
  unfold tailWord_2553518
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641806595380983374915651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62089635175365244666216805 11641806595380983374915651)
  ·
    refine ⟨17462709893071475062373477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641806595380983374915651 17462709893071475062373477)
    ·
      refine ⟨3274258104950901574195027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17462709893071475062373477 3274258104950901574195027)
      ·
        refine ⟨4911387157426352361292541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274258104950901574195027 4911387157426352361292541)
        ·
          refine ⟨1841770184034882135484703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4911387157426352361292541 1841770184034882135484703)
          ·
            refine ⟨2762655276052323203227055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841770184034882135484703 2762655276052323203227055)
            ·
              refine ⟨4143982914078484804840583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762655276052323203227055 4143982914078484804840583)
              ·
                refine ⟨6215974371117727207260875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143982914078484804840583 6215974371117727207260875)
                ·
                  refine ⟨9323961556676590810891313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215974371117727207260875 9323961556676590810891313)
                  ·
                    refine ⟨6992971167507443108168485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9323961556676590810891313 6992971167507443108168485)
                    ·
                      refine ⟨1311182093907645582781591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6992971167507443108168485 1311182093907645582781591)
                      ·
                        rfl

theorem cell23_2553518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2553518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553518 prefixEnd_2553518 := by exact prefixLift 2553518
  have htrace : WordTrace (prefixWord ++ tailWord_2553518) baseStart_2553518 baseEnd_2553518 := by
    simpa [prefixWord, tailWord_2553518, baseEnd_2553518] using wordTrace_append hprefix tailTrace_2553518
  have hstable : (prefixWord ++ tailWord_2553518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553518).length < 2 ^ (prefixWord ++ tailWord_2553518).sum := by decide
  have hdescent : baseEnd_2553518 < baseStart_2553518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553520 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_2553520 : Nat := 118140960795 + 2553520 * 2 ^ 59
def prefixEnd_2553520 : Nat := 4983230072969 + 3 ^ 40 * 2553520 * 2
def baseEnd_2553520 : Nat := 437061040289651524985527

theorem tailTrace_2553520 : CollatzResearch.WordTrace tailWord_2553520 prefixEnd_2553520 437061040289651524985527 := by
  unfold tailWord_2553520
  simp only [CollatzResearch.WordTrace]
  refine ⟨46567262854520310670449007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62089683806027080893932009 46567262854520310670449007)
  ·
    refine ⟨69850894281780466005673511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46567262854520310670449007 69850894281780466005673511)
    ·
      refine ⟨104776341422670699008510267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69850894281780466005673511 104776341422670699008510267)
      ·
        refine ⟨157164512134006048512765401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104776341422670699008510267 157164512134006048512765401)
        ·
          refine ⟨117873384100504536384574051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157164512134006048512765401 117873384100504536384574051)
          ·
            refine ⟨176810076150756804576861077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117873384100504536384574051 176810076150756804576861077)
            ·
              refine ⟨8287972319566725214540363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 176810076150756804576861077 8287972319566725214540363)
              ·
                refine ⟨12431958479350087821810545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287972319566725214540363 12431958479350087821810545)
                ·
                  refine ⟨9323968859512565866357909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12431958479350087821810545 9323968859512565866357909)
                  ·
                    refine ⟨437061040289651524985527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9323968859512565866357909 437061040289651524985527)
                    ·
                      rfl

theorem cell23_2553520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_2553520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553520 prefixEnd_2553520 := by exact prefixLift 2553520
  have htrace : WordTrace (prefixWord ++ tailWord_2553520) baseStart_2553520 baseEnd_2553520 := by
    simpa [prefixWord, tailWord_2553520, baseEnd_2553520] using wordTrace_append hprefix tailTrace_2553520
  have hstable : (prefixWord ++ tailWord_2553520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553520).length < 2 ^ (prefixWord ++ tailWord_2553520).sum := by decide
  have hdescent : baseEnd_2553520 < baseStart_2553520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553544 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_2553544 : Nat := 118140960795 + 2553544 * 2 ^ 59
def prefixEnd_2553544 : Nat := 4983230072969 + 3 ^ 40 * 2553544 * 2
def baseEnd_2553544 : Nat := 1311195444404662481056471

theorem tailTrace_2553544 : CollatzResearch.WordTrace tailWord_2553544 prefixEnd_2553544 1311195444404662481056471 := by
  unfold tailWord_2553544
  simp only [CollatzResearch.WordTrace]
  refine ⟨46567700530476836719885843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62090267373969115626514457 46567700530476836719885843)
  ·
    refine ⟨69851550795715255079828765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46567700530476836719885843 69851550795715255079828765)
    ·
      refine ⟨26194331548393220654935787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69851550795715255079828765 26194331548393220654935787)
      ·
        refine ⟨39291497322589830982403681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26194331548393220654935787 39291497322589830982403681)
        ·
          refine ⟨29468622991942373236802761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39291497322589830982403681 29468622991942373236802761)
          ·
            refine ⟨22101467243956779927602071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29468622991942373236802761 22101467243956779927602071)
            ·
              refine ⟨33152200865935169891403107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22101467243956779927602071 33152200865935169891403107)
              ·
                refine ⟨49728301298902754837104661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33152200865935169891403107 49728301298902754837104661)
                ·
                  refine ⟨2331014123386066632989281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49728301298902754837104661 2331014123386066632989281)
                  ·
                    refine ⟨1748260592539549974741961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2331014123386066632989281 1748260592539549974741961)
                    ·
                      refine ⟨1311195444404662481056471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748260592539549974741961 1311195444404662481056471)
                      ·
                        rfl

theorem cell23_2553544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_2553544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553544 prefixEnd_2553544 := by exact prefixLift 2553544
  have htrace : WordTrace (prefixWord ++ tailWord_2553544) baseStart_2553544 baseEnd_2553544 := by
    simpa [prefixWord, tailWord_2553544, baseEnd_2553544] using wordTrace_append hprefix tailTrace_2553544
  have hstable : (prefixWord ++ tailWord_2553544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553544).length < 2 ^ (prefixWord ++ tailWord_2553544).sum := by decide
  have hdescent : baseEnd_2553544 < baseStart_2553544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553560 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2553560 : Nat := 118140960795 + 2553560 * 2 ^ 59
def prefixEnd_2553560 : Nat := 4983230072969 + 3 ^ 40 * 2553560 * 2
def baseEnd_2553560 : Nat := 1311203660095134418456397

theorem tailTrace_2553560 : CollatzResearch.WordTrace tailWord_2553560 prefixEnd_2553560 1311203660095134418456397 := by
  unfold tailWord_2553560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46567992314447854086177067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62090656419263805448236089 46567992314447854086177067)
  ·
    refine ⟨69851988471671781129265601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46567992314447854086177067 69851988471671781129265601)
    ·
      refine ⟨52388991353753835846949201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69851988471671781129265601 52388991353753835846949201)
      ·
        refine ⟨39291743515315376885211901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52388991353753835846949201 39291743515315376885211901)
        ·
          refine ⟨14734403818243266331954463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39291743515315376885211901 14734403818243266331954463)
          ·
            refine ⟨22101605727364899497931695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14734403818243266331954463 22101605727364899497931695)
            ·
              refine ⟨33152408591047349246897543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22101605727364899497931695 33152408591047349246897543)
              ·
                refine ⟨49728612886571023870346315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33152408591047349246897543 49728612886571023870346315)
                ·
                  refine ⟨74592919329856535805519473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49728612886571023870346315 74592919329856535805519473)
                  ·
                    refine ⟨55944689497392401854139605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74592919329856535805519473 55944689497392401854139605)
                    ·
                      refine ⟨1311203660095134418456397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55944689497392401854139605 1311203660095134418456397)
                      ·
                        rfl

theorem cell23_2553560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2553560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553560 prefixEnd_2553560 := by exact prefixLift 2553560
  have htrace : WordTrace (prefixWord ++ tailWord_2553560) baseStart_2553560 baseEnd_2553560 := by
    simpa [prefixWord, tailWord_2553560, baseEnd_2553560] using wordTrace_append hprefix tailTrace_2553560
  have hstable : (prefixWord ++ tailWord_2553560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553560).length < 2 ^ (prefixWord ++ tailWord_2553560).sum := by decide
  have hdescent : baseEnd_2553560 < baseStart_2553560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553578 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_2553578 : Nat := 118140960795 + 2553578 * 2 ^ 59
def prefixEnd_2553578 : Nat := 4983230072969 + 3 ^ 40 * 2553578 * 2
def baseEnd_2553578 : Nat := 1311212902746915348031315

theorem tailTrace_2553578 : CollatzResearch.WordTrace tailWord_2553578 prefixEnd_2553578 1311212902746915348031315 := by
  unfold tailWord_2553578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284160285707624311627347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62091094095220331497672925 23284160285707624311627347)
  ·
    refine ⟨34926240428561436467441021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23284160285707624311627347 34926240428561436467441021)
    ·
      refine ⟨13097340160710538675290383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34926240428561436467441021 13097340160710538675290383)
      ·
        refine ⟨19646010241065808012935575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13097340160710538675290383 19646010241065808012935575)
        ·
          refine ⟨29469015361598712019403363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19646010241065808012935575 29469015361598712019403363)
          ·
            refine ⟨44203523042398068029105045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29469015361598712019403363 44203523042398068029105045)
            ·
              refine ⟨2072040142612409438864299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44203523042398068029105045 2072040142612409438864299)
              ·
                refine ⟨3108060213918614158296449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072040142612409438864299 3108060213918614158296449)
                ·
                  refine ⟨2331045160438960618722337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3108060213918614158296449 2331045160438960618722337)
                  ·
                    refine ⟨1748283870329220464041753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2331045160438960618722337 1748283870329220464041753)
                    ·
                      refine ⟨1311212902746915348031315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748283870329220464041753 1311212902746915348031315)
                      ·
                        rfl

theorem cell23_2553578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_2553578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553578 prefixEnd_2553578 := by exact prefixLift 2553578
  have htrace : WordTrace (prefixWord ++ tailWord_2553578) baseStart_2553578 baseEnd_2553578 := by
    simpa [prefixWord, tailWord_2553578, baseEnd_2553578] using wordTrace_append hprefix tailTrace_2553578
  have hstable : (prefixWord ++ tailWord_2553578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553578).length < 2 ^ (prefixWord ++ tailWord_2553578).sum := by decide
  have hdescent : baseEnd_2553578 < baseStart_2553578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553580 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_2553580 : Nat := 118140960795 + 2553580 * 2 ^ 59
def prefixEnd_2553580 : Nat := 4983230072969 + 3 ^ 40 * 2553580 * 2
def baseEnd_2553580 : Nat := 437071309902741446735435

theorem tailTrace_2553580 : CollatzResearch.WordTrace tailWord_2553580 prefixEnd_2553580 437071309902741446735435 := by
  unfold tailWord_2553580
  simp only [CollatzResearch.WordTrace]
  refine ⟨46568357044411625794041097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62091142725882167725388129 46568357044411625794041097)
  ·
    refine ⟨34926267783308719345530823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46568357044411625794041097 34926267783308719345530823)
    ·
      refine ⟨52389401674963079018296235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34926267783308719345530823 52389401674963079018296235)
      ·
        refine ⟨78584102512444618527444353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52389401674963079018296235 78584102512444618527444353)
        ·
          refine ⟨58938076884333463895583265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78584102512444618527444353 58938076884333463895583265)
          ·
            refine ⟨44203557663250097921687449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58938076884333463895583265 44203557663250097921687449)
            ·
              refine ⟨33152668247437573441265587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44203557663250097921687449 33152668247437573441265587)
              ·
                refine ⟨49729002371156360161898381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33152668247437573441265587 49729002371156360161898381)
                ·
                  refine ⟨18648375889183635060711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49729002371156360161898381 18648375889183635060711893)
                  ·
                    refine ⟨437071309902741446735435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18648375889183635060711893 437071309902741446735435)
                    ·
                      rfl

theorem cell23_2553580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_2553580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553580 prefixEnd_2553580 := by exact prefixLift 2553580
  have htrace : WordTrace (prefixWord ++ tailWord_2553580) baseStart_2553580 baseEnd_2553580 := by
    simpa [prefixWord, tailWord_2553580, baseEnd_2553580] using wordTrace_append hprefix tailTrace_2553580
  have hstable : (prefixWord ++ tailWord_2553580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553580).length < 2 ^ (prefixWord ++ tailWord_2553580).sum := by decide
  have hdescent : baseEnd_2553580 < baseStart_2553580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553618 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_2553618 : Nat := 118140960795 + 2553618 * 2 ^ 59
def prefixEnd_2553618 : Nat := 4983230072969 + 3 ^ 40 * 2553618 * 2
def baseEnd_2553618 : Nat := 145692604663677243503459

theorem tailTrace_2553618 : CollatzResearch.WordTrace tailWord_2553618 prefixEnd_2553618 145692604663677243503459 := by
  unfold tailWord_2553618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284525015671396019491377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62092066708457056051977005 23284525015671396019491377)
  ·
    refine ⟨17463393761753547014618533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23284525015671396019491377 17463393761753547014618533)
    ·
      refine ⟨3274386330328790065240975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17463393761753547014618533 3274386330328790065240975)
      ·
        refine ⟨4911579495493185097861463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274386330328790065240975 4911579495493185097861463)
        ·
          refine ⟨7367369243239777646792195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911579495493185097861463 7367369243239777646792195)
          ·
            refine ⟨11051053864859666470188293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367369243239777646792195 11051053864859666470188293)
            ·
              refine ⟨2072072599661187463160305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11051053864859666470188293 2072072599661187463160305)
              ·
                refine ⟨1554054449745890597370229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072072599661187463160305 1554054449745890597370229)
                ·
                  refine ⟨145692604663677243503459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554054449745890597370229 145692604663677243503459)
                  ·
                    rfl

theorem cell23_2553618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_2553618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553618 prefixEnd_2553618 := by exact prefixLift 2553618
  have htrace : WordTrace (prefixWord ++ tailWord_2553618) baseStart_2553618 baseEnd_2553618 := by
    simpa [prefixWord, tailWord_2553618, baseEnd_2553618] using wordTrace_append hprefix tailTrace_2553618
  have hstable : (prefixWord ++ tailWord_2553618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553618).length < 2 ^ (prefixWord ++ tailWord_2553618).sum := by decide
  have hdescent : baseEnd_2553618 < baseStart_2553618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553644 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_2553644 : Nat := 118140960795 + 2553644 * 2 ^ 59
def prefixEnd_2553644 : Nat := 4983230072969 + 3 ^ 40 * 2553644 * 2
def baseEnd_2553644 : Nat := 437082264156704029935337

theorem tailTrace_2553644 : CollatzResearch.WordTrace tailWord_2553644 prefixEnd_2553644 437082264156704029935337 := by
  unfold tailWord_2553644
  simp only [CollatzResearch.WordTrace]
  refine ⟨46569524180295695259205993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62092698907060927012274657 46569524180295695259205993)
  ·
    refine ⟨34927143135221771444404495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46569524180295695259205993 34927143135221771444404495)
    ·
      refine ⟨52390714702832657166606743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34927143135221771444404495 52390714702832657166606743)
      ·
        refine ⟨78586072054248985749910115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52390714702832657166606743 78586072054248985749910115)
        ·
          refine ⟨117879108081373478624865173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78586072054248985749910115 117879108081373478624865173)
          ·
            refine ⟨5525583191314381810540555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117879108081373478624865173 5525583191314381810540555)
            ·
              refine ⟨8288374786971572715810833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525583191314381810540555 8288374786971572715810833)
              ·
                refine ⟨6216281090228679536858125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288374786971572715810833 6216281090228679536858125)
                ·
                  refine ⟨2331105408835754826321797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6216281090228679536858125 2331105408835754826321797)
                  ·
                    refine ⟨437082264156704029935337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331105408835754826321797 437082264156704029935337)
                    ·
                      rfl

theorem cell23_2553644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_2553644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553644 prefixEnd_2553644 := by exact prefixLift 2553644
  have htrace : WordTrace (prefixWord ++ tailWord_2553644) baseStart_2553644 baseEnd_2553644 := by
    simpa [prefixWord, tailWord_2553644, baseEnd_2553644] using wordTrace_append hprefix tailTrace_2553644
  have hstable : (prefixWord ++ tailWord_2553644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553644).length < 2 ^ (prefixWord ++ tailWord_2553644).sum := by decide
  have hdescent : baseEnd_2553644 < baseStart_2553644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553651 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 4]
def baseStart_2553651 : Nat := 118140960795 + 2553651 * 2 ^ 59
def prefixEnd_2553651 : Nat := 4983230072969 + 3 ^ 40 * 2553651 * 2
def baseEnd_2553651 : Nat := 1311250386834693562418479

theorem tailTrace_2553651 : CollatzResearch.WordTrace tailWord_2553651 prefixEnd_2553651 1311250386834693562418479 := by
  unfold tailWord_2553651
  simp only [CollatzResearch.WordTrace]
  refine ⟨93139303671566030713916807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62092869114377353809277871 93139303671566030713916807)
  ·
    refine ⟨139708955507349046070875211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93139303671566030713916807 139708955507349046070875211)
    ·
      refine ⟨209563433261023569106312817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139708955507349046070875211 209563433261023569106312817)
      ·
        refine ⟨157172574945767676829734613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209563433261023569106312817 157172574945767676829734613)
        ·
          refine ⟨3683732225291429925696905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 157172574945767676829734613 3683732225291429925696905)
          ·
            refine ⟨2762799168968572444272679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683732225291429925696905 2762799168968572444272679)
            ·
              refine ⟨4144198753452858666409019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762799168968572444272679 4144198753452858666409019)
              ·
                refine ⟨6216298130179287999613529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144198753452858666409019 6216298130179287999613529)
                ·
                  refine ⟨4662223597634465999710147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6216298130179287999613529 4662223597634465999710147)
                  ·
                    refine ⟨6993335396451698999565221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4662223597634465999710147 6993335396451698999565221)
                    ·
                      refine ⟨1311250386834693562418479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6993335396451698999565221 1311250386834693562418479)
                      ·
                        rfl

theorem cell23_2553651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_2553651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553651 prefixEnd_2553651 := by exact prefixLift 2553651
  have htrace : WordTrace (prefixWord ++ tailWord_2553651) baseStart_2553651 baseEnd_2553651 := by
    simpa [prefixWord, tailWord_2553651, baseEnd_2553651] using wordTrace_append hprefix tailTrace_2553651
  have hstable : (prefixWord ++ tailWord_2553651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553651).length < 2 ^ (prefixWord ++ tailWord_2553651).sum := by decide
  have hdescent : baseEnd_2553651 < baseStart_2553651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553735 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_2553735 : Nat := 118140960795 + 2553735 * 2 ^ 59
def prefixEnd_2553735 : Nat := 4983230072969 + 3 ^ 40 * 2553735 * 2
def baseEnd_2553735 : Nat := 1311293519209671233768093

theorem tailTrace_2553735 : CollatzResearch.WordTrace tailWord_2553735 prefixEnd_2553735 1311293519209671233768093 := by
  unfold tailWord_2553735
  simp only [CollatzResearch.WordTrace]
  refine ⟨93142367403261713059974659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62094911602174475373316439 93142367403261713059974659)
  ·
    refine ⟨139713551104892569589961989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93142367403261713059974659 139713551104892569589961989)
    ·
      refine ⟨26196290832167356798117873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139713551104892569589961989 26196290832167356798117873)
      ·
        refine ⟨19647218124125517598588405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26196290832167356798117873 19647218124125517598588405)
        ·
          refine ⟨1841926699136767274867663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19647218124125517598588405 1841926699136767274867663)
          ·
            refine ⟨2762890048705150912301495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841926699136767274867663 2762890048705150912301495)
            ·
              refine ⟨4144335073057726368452243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762890048705150912301495 4144335073057726368452243)
              ·
                refine ⟨6216502609586589552678365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144335073057726368452243 6216502609586589552678365)
                ·
                  refine ⟨2331188478594971082254387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6216502609586589552678365 2331188478594971082254387)
                  ·
                    refine ⟨3496782717892456623381581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2331188478594971082254387 3496782717892456623381581)
                    ·
                      refine ⟨1311293519209671233768093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3496782717892456623381581 1311293519209671233768093)
                      ·
                        rfl

theorem cell23_2553735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_2553735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553735 prefixEnd_2553735 := by exact prefixLift 2553735
  have htrace : WordTrace (prefixWord ++ tailWord_2553735) baseStart_2553735 baseEnd_2553735 := by
    simpa [prefixWord, tailWord_2553735, baseEnd_2553735] using wordTrace_append hprefix tailTrace_2553735
  have hstable : (prefixWord ++ tailWord_2553735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553735).length < 2 ^ (prefixWord ++ tailWord_2553735).sum := by decide
  have hdescent : baseEnd_2553735 < baseStart_2553735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553737 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_2553737 : Nat := 118140960795 + 2553737 * 2 ^ 59
def prefixEnd_2553737 : Nat := 4983230072969 + 3 ^ 40 * 2553737 * 2
def baseEnd_2553737 : Nat := 1311294546170980225943083

theorem tailTrace_2553737 : CollatzResearch.WordTrace tailWord_2553737 prefixEnd_2553737 1311294546170980225943083 := by
  unfold tailWord_2553737
  simp only [CollatzResearch.WordTrace]
  refine ⟨93142440349254467401547465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62094960232836311601031643 93142440349254467401547465)
  ·
    refine ⟨69856830261940850551160599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93142440349254467401547465 69856830261940850551160599)
    ·
      refine ⟨104785245392911275826740899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69856830261940850551160599 104785245392911275826740899)
      ·
        refine ⟨157177868089366913740111349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104785245392911275826740899 157177868089366913740111349)
        ·
          refine ⟨14735425133378148163135439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157177868089366913740111349 14735425133378148163135439)
          ·
            refine ⟨22103137700067222244703159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14735425133378148163135439 22103137700067222244703159)
            ·
              refine ⟨33154706550100833367054739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22103137700067222244703159 33154706550100833367054739)
              ·
                refine ⟨49732059825151250050582109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33154706550100833367054739 49732059825151250050582109)
                ·
                  refine ⟨18649522434431718768968291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49732059825151250050582109 18649522434431718768968291)
                  ·
                    refine ⟨27974283651647578153452437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18649522434431718768968291 27974283651647578153452437)
                    ·
                      refine ⟨1311294546170980225943083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27974283651647578153452437 1311294546170980225943083)
                      ·
                        rfl

theorem cell23_2553737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_2553737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553737 prefixEnd_2553737 := by exact prefixLift 2553737
  have htrace : WordTrace (prefixWord ++ tailWord_2553737) baseStart_2553737 baseEnd_2553737 := by
    simpa [prefixWord, tailWord_2553737, baseEnd_2553737] using wordTrace_append hprefix tailTrace_2553737
  have hstable : (prefixWord ++ tailWord_2553737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553737).length < 2 ^ (prefixWord ++ tailWord_2553737).sum := by decide
  have hdescent : baseEnd_2553737 < baseStart_2553737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553751 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 2, 4]
def baseStart_2553751 : Nat := 118140960795 + 2553751 * 2 ^ 59
def prefixEnd_2553751 : Nat := 4983230072969 + 3 ^ 40 * 2553751 * 2
def baseEnd_2553751 : Nat := 437100578300047723722673

theorem tailTrace_2553751 : CollatzResearch.WordTrace tailWord_2553751 prefixEnd_2553751 437100578300047723722673 := by
  unfold tailWord_2553751
  simp only [CollatzResearch.WordTrace]
  refine ⟨93142950971203747792557107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62095300647469165195038071 93142950971203747792557107)
  ·
    refine ⟨139714426456805621688835661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93142950971203747792557107 139714426456805621688835661)
    ·
      refine ⟨52392909921302108133313373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139714426456805621688835661 52392909921302108133313373)
      ·
        refine ⟨19647341220488290549992515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52392909921302108133313373 19647341220488290549992515)
        ·
          refine ⟨29471011830732435824988773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19647341220488290549992515 29471011830732435824988773)
          ·
            refine ⟨5525814718262331717185395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29471011830732435824988773 5525814718262331717185395)
            ·
              refine ⟨8288722077393497575778093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525814718262331717185395 8288722077393497575778093)
              ·
                refine ⟨3108270779022561590916785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8288722077393497575778093 3108270779022561590916785)
                ·
                  refine ⟨2331203084266921193187589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3108270779022561590916785 2331203084266921193187589)
                  ·
                    refine ⟨437100578300047723722673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331203084266921193187589 437100578300047723722673)
                    ·
                      rfl

theorem cell23_2553751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_2553751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553751 prefixEnd_2553751 := by exact prefixLift 2553751
  have htrace : WordTrace (prefixWord ++ tailWord_2553751) baseStart_2553751 baseEnd_2553751 := by
    simpa [prefixWord, tailWord_2553751, baseEnd_2553751] using wordTrace_append hprefix tailTrace_2553751
  have hstable : (prefixWord ++ tailWord_2553751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553751).length < 2 ^ (prefixWord ++ tailWord_2553751).sum := by decide
  have hdescent : baseEnd_2553751 < baseStart_2553751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553754 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2553754 : Nat := 118140960795 + 2553754 * 2 ^ 59
def prefixEnd_2553754 : Nat := 4983230072969 + 3 ^ 40 * 2553754 * 2
def baseEnd_2553754 : Nat := 1311303275342106659430505

theorem tailTrace_2553754 : CollatzResearch.WordTrace tailWord_2553754 prefixEnd_2553754 1311303275342106659430505 := by
  unfold tailWord_2553754
  simp only [CollatzResearch.WordTrace]
  refine ⟨23285765097548219826229079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62095373593461919536610877 23285765097548219826229079)
  ·
    refine ⟨34928647646322329739343619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23285765097548219826229079 34928647646322329739343619)
    ·
      refine ⟨52392971469483494609015429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34928647646322329739343619 52392971469483494609015429)
      ·
        refine ⟨9823682150528155239190393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52392971469483494609015429 9823682150528155239190393)
        ·
          refine ⟨7367761612896116429392795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9823682150528155239190393 7367761612896116429392795)
          ·
            refine ⟨11051642419344174644089193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367761612896116429392795 11051642419344174644089193)
            ·
              refine ⟨8288731814508130983066895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11051642419344174644089193 8288731814508130983066895)
              ·
                refine ⟨12433097721762196474600343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8288731814508130983066895 12433097721762196474600343)
                ·
                  refine ⟨18649646582643294711900515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12433097721762196474600343 18649646582643294711900515)
                  ·
                    refine ⟨27974469873964942067850773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18649646582643294711900515 27974469873964942067850773)
                    ·
                      refine ⟨1311303275342106659430505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27974469873964942067850773 1311303275342106659430505)
                      ·
                        rfl

theorem cell23_2553754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2553754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553754 prefixEnd_2553754 := by exact prefixLift 2553754
  have htrace : WordTrace (prefixWord ++ tailWord_2553754) baseStart_2553754 baseEnd_2553754 := by
    simpa [prefixWord, tailWord_2553754, baseEnd_2553754] using wordTrace_append hprefix tailTrace_2553754
  have hstable : (prefixWord ++ tailWord_2553754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553754).length < 2 ^ (prefixWord ++ tailWord_2553754).sum := by decide
  have hdescent : baseEnd_2553754 < baseStart_2553754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553768 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2553768 : Nat := 118140960795 + 2553768 * 2 ^ 59
def prefixEnd_2553768 : Nat := 4983230072969 + 3 ^ 40 * 2553768 * 2
def baseEnd_2553768 : Nat := 437103488023756534885147

theorem tailTrace_2553768 : CollatzResearch.WordTrace tailWord_2553768 prefixEnd_2553768 437103488023756534885147 := by
  unfold tailWord_2553768
  simp only [CollatzResearch.WordTrace]
  refine ⟨46571785506071079847962979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62095714008094773130617305 46571785506071079847962979)
  ·
    refine ⟨69857678259106619771944469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46571785506071079847962979 69857678259106619771944469)
    ·
      refine ⟨3274578668395622801809897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69857678259106619771944469 3274578668395622801809897)
      ·
        refine ⟨2455934001296717101357423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3274578668395622801809897 2455934001296717101357423)
        ·
          refine ⟨3683901001945075652036135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455934001296717101357423 3683901001945075652036135)
          ·
            refine ⟨5525851502917613478054203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683901001945075652036135 5525851502917613478054203)
            ·
              refine ⟨8288777254376420217081305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525851502917613478054203 8288777254376420217081305)
              ·
                refine ⟨6216582940782315162810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288777254376420217081305 6216582940782315162810979)
                ·
                  refine ⟨9324874411173472744216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216582940782315162810979 9324874411173472744216469)
                  ·
                    refine ⟨437103488023756534885147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9324874411173472744216469 437103488023756534885147)
                    ·
                      rfl

theorem cell23_2553768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2553768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553768 prefixEnd_2553768 := by exact prefixLift 2553768
  have htrace : WordTrace (prefixWord ++ tailWord_2553768) baseStart_2553768 baseEnd_2553768 := by
    simpa [prefixWord, tailWord_2553768, baseEnd_2553768] using wordTrace_append hprefix tailTrace_2553768
  have hstable : (prefixWord ++ tailWord_2553768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553768).length < 2 ^ (prefixWord ++ tailWord_2553768).sum := by decide
  have hdescent : baseEnd_2553768 < baseStart_2553768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553787 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_2553787 : Nat := 118140960795 + 2553787 * 2 ^ 59
def prefixEnd_2553787 : Nat := 4983230072969 + 3 ^ 40 * 2553787 * 2
def baseEnd_2553787 : Nat := 1311320220203705030317853

theorem tailTrace_2553787 : CollatzResearch.WordTrace tailWord_2553787 prefixEnd_2553787 1311320220203705030317853 := by
  unfold tailWord_2553787
  simp only [CollatzResearch.WordTrace]
  refine ⟨93144263999073325940867615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62096175999382217293911743 93144263999073325940867615)
  ·
    refine ⟨139716395998609988911301423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93144263999073325940867615 139716395998609988911301423)
    ·
      refine ⟨209574593997914983366952135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139716395998609988911301423 209574593997914983366952135)
      ·
        refine ⟨314361890996872475050428203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209574593997914983366952135 314361890996872475050428203)
        ·
          refine ⟨471542836495308712575642305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314361890996872475050428203 471542836495308712575642305)
          ·
            refine ⟨353657127371481534431731729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471542836495308712575642305 353657127371481534431731729)
            ·
              refine ⟨265242845528611150823798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353657127371481534431731729 265242845528611150823798797)
              ·
                refine ⟨99466067073229181558924549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265242845528611150823798797 99466067073229181558924549)
                ·
                  refine ⟨18649887576230471542298353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99466067073229181558924549 18649887576230471542298353)
                  ·
                    refine ⟨13987415682172853656723765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18649887576230471542298353 13987415682172853656723765)
                    ·
                      refine ⟨1311320220203705030317853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13987415682172853656723765 1311320220203705030317853)
                      ·
                        rfl

theorem cell23_2553787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_2553787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553787 prefixEnd_2553787 := by exact prefixLift 2553787
  have htrace : WordTrace (prefixWord ++ tailWord_2553787) baseStart_2553787 baseEnd_2553787 := by
    simpa [prefixWord, tailWord_2553787, baseEnd_2553787] using wordTrace_append hprefix tailTrace_2553787
  have hstable : (prefixWord ++ tailWord_2553787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553787).length < 2 ^ (prefixWord ++ tailWord_2553787).sum := by decide
  have hdescent : baseEnd_2553787 < baseStart_2553787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553834 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2553834 : Nat := 118140960795 + 2553834 * 2 ^ 59
def prefixEnd_2553834 : Nat := 4983230072969 + 3 ^ 40 * 2553834 * 2
def baseEnd_2553834 : Nat := 1311344353794466346430137

theorem tailTrace_2553834 : CollatzResearch.WordTrace tailWord_2553834 prefixEnd_2553834 1311344353794466346430137 := by
  unfold tailWord_2553834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23286494557475763241957139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62097318819935368645219037 23286494557475763241957139)
  ·
    refine ⟨34929741836213644862935709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23286494557475763241957139 34929741836213644862935709)
    ·
      refine ⟨13098653188580116823600891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34929741836213644862935709 13098653188580116823600891)
      ·
        refine ⟨19647979782870175235401337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13098653188580116823600891 19647979782870175235401337)
        ·
          refine ⟨14735984837152631426551003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19647979782870175235401337 14735984837152631426551003)
          ·
            refine ⟨22103977255728947139826505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14735984837152631426551003 22103977255728947139826505)
            ·
              refine ⟨16577982941796710354869879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22103977255728947139826505 16577982941796710354869879)
              ·
                refine ⟨24866974412695065532304819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16577982941796710354869879 24866974412695065532304819)
                ·
                  refine ⟨37300461619042598298457229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24866974412695065532304819 37300461619042598298457229)
                  ·
                    refine ⟨13987673107140974361921461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37300461619042598298457229 13987673107140974361921461)
                    ·
                      refine ⟨1311344353794466346430137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13987673107140974361921461 1311344353794466346430137)
                      ·
                        rfl

theorem cell23_2553834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2553834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553834 prefixEnd_2553834 := by exact prefixLift 2553834
  have htrace : WordTrace (prefixWord ++ tailWord_2553834) baseStart_2553834 baseEnd_2553834 := by
    simpa [prefixWord, tailWord_2553834, baseEnd_2553834] using wordTrace_append hprefix tailTrace_2553834
  have hstable : (prefixWord ++ tailWord_2553834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553834).length < 2 ^ (prefixWord ++ tailWord_2553834).sum := by decide
  have hdescent : baseEnd_2553834 < baseStart_2553834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553961 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 6]
def baseStart_2553961 : Nat := 118140960795 + 2553961 * 2 ^ 59
def prefixEnd_2553961 : Nat := 4983230072969 + 3 ^ 40 * 2553961 * 2
def baseEnd_2553961 : Nat := 145712173981954149949117

theorem tailTrace_2553961 : CollatzResearch.WordTrace tailWord_2553961 prefixEnd_2553961 145712173981954149949117 := by
  unfold tailWord_2553961
  simp only [CollatzResearch.WordTrace]
  refine ⟨93150610300442953657701737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62100406866961969105134491 93150610300442953657701737)
  ·
    refine ⟨69862957725332215243276303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93150610300442953657701737 69862957725332215243276303)
    ·
      refine ⟨104794436587998322864914455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69862957725332215243276303 104794436587998322864914455)
      ·
        refine ⟨157191654881997484297371683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104794436587998322864914455 157191654881997484297371683)
        ·
          refine ⟨235787482322996226446057525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157191654881997484297371683 235787482322996226446057525)
          ·
            refine ⟨22105076467780896229317893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235787482322996226446057525 22105076467780896229317893)
            ·
              refine ⟨4144701837708918042997105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22105076467780896229317893 4144701837708918042997105)
              ·
                refine ⟨3108526378281688532247829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144701837708918042997105 3108526378281688532247829)
                ·
                  refine ⟨145712173981954149949117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3108526378281688532247829 145712173981954149949117)
                  ·
                    rfl

theorem cell23_2553961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_2553961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553961 prefixEnd_2553961 := by exact prefixLift 2553961
  have htrace : WordTrace (prefixWord ++ tailWord_2553961) baseStart_2553961 baseEnd_2553961 := by
    simpa [prefixWord, tailWord_2553961, baseEnd_2553961] using wordTrace_append hprefix tailTrace_2553961
  have hstable : (prefixWord ++ tailWord_2553961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553961).length < 2 ^ (prefixWord ++ tailWord_2553961).sum := by decide
  have hdescent : baseEnd_2553961 < baseStart_2553961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553965 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2553965 : Nat := 118140960795 + 2553965 * 2 ^ 59
def prefixEnd_2553965 : Nat := 4983230072969 + 3 ^ 40 * 2553965 * 2
def baseEnd_2553965 : Nat := 437137206586735111297345

theorem tailTrace_2553965 : CollatzResearch.WordTrace tailWord_2553965 prefixEnd_2553965 437137206586735111297345 := by
  unfold tailWord_2553965
  simp only [CollatzResearch.WordTrace]
  refine ⟨93150756192428462340847349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62100504128285641560564899 93150756192428462340847349)
  ·
    refine ⟨8732883393040168344454439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93150756192428462340847349 8732883393040168344454439)
    ·
      refine ⟨13099325089560252516681659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8732883393040168344454439 13099325089560252516681659)
      ·
        refine ⟨19648987634340378775022489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13099325089560252516681659 19648987634340378775022489)
        ·
          refine ⟨14736740725755284081266867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19648987634340378775022489 14736740725755284081266867)
          ·
            refine ⟨22105111088632926121900301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14736740725755284081266867 22105111088632926121900301)
            ·
              refine ⟨8289416658237347295712613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22105111088632926121900301 8289416658237347295712613)
              ·
                refine ⟨1554265623419502617946115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8289416658237347295712613 1554265623419502617946115)
                ·
                  refine ⟨2331398435129253926919173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554265623419502617946115 2331398435129253926919173)
                  ·
                    refine ⟨437137206586735111297345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331398435129253926919173 437137206586735111297345)
                    ·
                      rfl

theorem cell23_2553965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2553965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553965 prefixEnd_2553965 := by exact prefixLift 2553965
  have htrace : WordTrace (prefixWord ++ tailWord_2553965) baseStart_2553965 baseEnd_2553965 := by
    simpa [prefixWord, tailWord_2553965, baseEnd_2553965] using wordTrace_append hprefix tailTrace_2553965
  have hstable : (prefixWord ++ tailWord_2553965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553965).length < 2 ^ (prefixWord ++ tailWord_2553965).sum := by decide
  have hdescent : baseEnd_2553965 < baseStart_2553965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553984 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2553984 : Nat := 118140960795 + 2553984 * 2 ^ 59
def prefixEnd_2553984 : Nat := 4983230072969 + 3 ^ 40 * 2553984 * 2
def baseEnd_2553984 : Nat := 1311421375892640759554447

theorem tailTrace_2553984 : CollatzResearch.WordTrace tailWord_2553984 prefixEnd_2553984 1311421375892640759554447 := by
  unfold tailWord_2553984
  simp only [CollatzResearch.WordTrace]
  refine ⟨46575724589679814292894503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62100966119573085723859337 46575724589679814292894503)
  ·
    refine ⟨69863586884519721439341755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46575724589679814292894503 69863586884519721439341755)
    ·
      refine ⟨104795380326779582159012633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69863586884519721439341755 104795380326779582159012633)
      ·
        refine ⟨78596535245084686619259475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104795380326779582159012633 78596535245084686619259475)
        ·
          refine ⟨117894802867627029928889213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78596535245084686619259475 117894802867627029928889213)
          ·
            refine ⟨44210551075360136223333455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117894802867627029928889213 44210551075360136223333455)
            ·
              refine ⟨66315826613040204335000183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44210551075360136223333455 66315826613040204335000183)
              ·
                refine ⟨99473739919560306502500275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66315826613040204335000183 99473739919560306502500275)
                ·
                  refine ⟨149210609879340459753750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99473739919560306502500275 149210609879340459753750413)
                  ·
                    refine ⟨55953978704752672407656405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149210609879340459753750413 55953978704752672407656405)
                    ·
                      refine ⟨1311421375892640759554447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55953978704752672407656405 1311421375892640759554447)
                      ·
                        rfl

theorem cell23_2553984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2553984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553984 prefixEnd_2553984 := by exact prefixLift 2553984
  have htrace : WordTrace (prefixWord ++ tailWord_2553984) baseStart_2553984 baseEnd_2553984 := by
    simpa [prefixWord, tailWord_2553984, baseEnd_2553984] using wordTrace_append hprefix tailTrace_2553984
  have hstable : (prefixWord ++ tailWord_2553984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553984).length < 2 ^ (prefixWord ++ tailWord_2553984).sum := by decide
  have hdescent : baseEnd_2553984 < baseStart_2553984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553991 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 3, 5]
def baseStart_2553991 : Nat := 118140960795 + 2553991 * 2 ^ 59
def prefixEnd_2553991 : Nat := 4983230072969 + 3 ^ 40 * 2553991 * 2
def baseEnd_2553991 : Nat := 437141656752407410722305

theorem tailTrace_2553991 : CollatzResearch.WordTrace tailWord_2553991 prefixEnd_2553991 437141656752407410722305 := by
  unfold tailWord_2553991
  simp only [CollatzResearch.WordTrace]
  refine ⟨93151704490334268781293827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62101136326889512520862551 93151704490334268781293827)
  ·
    refine ⟨139727556735501403171940741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93151704490334268781293827 139727556735501403171940741)
    ·
      refine ⟨26198916887906513094738889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139727556735501403171940741 26198916887906513094738889)
      ·
        refine ⟨19649187665929884821054167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26198916887906513094738889 19649187665929884821054167)
        ·
          refine ⟨29473781498894827231581251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19649187665929884821054167 29473781498894827231581251)
          ·
            refine ⟨44210672248342240847371877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29473781498894827231581251 44210672248342240847371877)
            ·
              refine ⟨8289501046564170158882227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44210672248342240847371877 8289501046564170158882227)
              ·
                refine ⟨12434251569846255238323341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8289501046564170158882227 12434251569846255238323341)
                ·
                  refine ⟨4662844338692345714371253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12434251569846255238323341 4662844338692345714371253)
                  ·
                    refine ⟨437141656752407410722305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4662844338692345714371253 437141656752407410722305)
                    ·
                      rfl

theorem cell23_2553991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_2553991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2553991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2553991 prefixEnd_2553991 := by exact prefixLift 2553991
  have htrace : WordTrace (prefixWord ++ tailWord_2553991) baseStart_2553991 baseEnd_2553991 := by
    simpa [prefixWord, tailWord_2553991, baseEnd_2553991] using wordTrace_append hprefix tailTrace_2553991
  have hstable : (prefixWord ++ tailWord_2553991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553991).length < 2 ^ (prefixWord ++ tailWord_2553991).sum := by decide
  have hdescent : baseEnd_2553991 < baseStart_2553991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554041 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2554041 : Nat := 118140960795 + 2554041 * 2 ^ 59
def prefixEnd_2554041 : Nat := 4983230072969 + 3 ^ 40 * 2554041 * 2
def baseEnd_2554041 : Nat := 1311450644289947036541685

theorem tailTrace_2554041 : CollatzResearch.WordTrace tailWord_2554041 prefixEnd_2554041 1311450644289947036541685 := by
  unfold tailWord_2554041
  simp only [CollatzResearch.WordTrace]
  refine ⟨93153528140153127320613977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62102352093435418213742651 93153528140153127320613977)
  ·
    refine ⟨69865146105114845490460483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93153528140153127320613977 69865146105114845490460483)
    ·
      refine ⟨104797719157672268235690725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69865146105114845490460483 104797719157672268235690725)
      ·
        refine ⟨19649572342063550294192011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104797719157672268235690725 19649572342063550294192011)
        ·
          refine ⟨29474358513095325441288017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19649572342063550294192011 29474358513095325441288017)
          ·
            refine ⟨22105768884821494080966013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29474358513095325441288017 22105768884821494080966013)
            ·
              refine ⟨8289663331808060280362255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22105768884821494080966013 8289663331808060280362255)
              ·
                refine ⟨12434494997712090420543383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8289663331808060280362255 12434494997712090420543383)
                ·
                  refine ⟨18651742496568135630815075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12434494997712090420543383 18651742496568135630815075)
                  ·
                    refine ⟨27977613744852203446222613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18651742496568135630815075 27977613744852203446222613)
                    ·
                      refine ⟨1311450644289947036541685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27977613744852203446222613 1311450644289947036541685)
                      ·
                        rfl

theorem cell23_2554041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2554041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554041 prefixEnd_2554041 := by exact prefixLift 2554041
  have htrace : WordTrace (prefixWord ++ tailWord_2554041) baseStart_2554041 baseEnd_2554041 := by
    simpa [prefixWord, tailWord_2554041, baseEnd_2554041] using wordTrace_append hprefix tailTrace_2554041
  have hstable : (prefixWord ++ tailWord_2554041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554041).length < 2 ^ (prefixWord ++ tailWord_2554041).sum := by decide
  have hdescent : baseEnd_2554041 < baseStart_2554041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554081 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2554081 : Nat := 118140960795 + 2554081 * 2 ^ 59
def prefixEnd_2554081 : Nat := 4983230072969 + 3 ^ 40 * 2554081 * 2
def baseEnd_2554081 : Nat := 437157061172042293347167

theorem tailTrace_2554081 : CollatzResearch.WordTrace tailWord_2554081 prefixEnd_2554081 437157061172042293347167 := by
  unfold tailWord_2554081
  simp only [CollatzResearch.WordTrace]
  refine ⟨93154987060008214152070097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62103324706672142768046731 93154987060008214152070097)
  ·
    refine ⟨69866240295006160614052573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93154987060008214152070097 69866240295006160614052573)
    ·
      refine ⟨26199840110627310230269715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69866240295006160614052573 26199840110627310230269715)
      ·
        refine ⟨39299760165940965345404573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26199840110627310230269715 39299760165940965345404573)
        ·
          refine ⟨14737410062227862004526715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39299760165940965345404573 14737410062227862004526715)
          ·
            refine ⟨22106115093341793006790073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14737410062227862004526715 22106115093341793006790073)
            ·
              refine ⟨16579586320006344755092555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22106115093341793006790073 16579586320006344755092555)
              ·
                refine ⟨24869379480009517132638833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16579586320006344755092555 24869379480009517132638833)
                ·
                  refine ⟨18652034610007137849479125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24869379480009517132638833 18652034610007137849479125)
                  ·
                    refine ⟨437157061172042293347167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18652034610007137849479125 437157061172042293347167)
                    ·
                      rfl

theorem cell23_2554081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2554081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554081 prefixEnd_2554081 := by exact prefixLift 2554081
  have htrace : WordTrace (prefixWord ++ tailWord_2554081) baseStart_2554081 baseEnd_2554081 := by
    simpa [prefixWord, tailWord_2554081, baseEnd_2554081] using wordTrace_append hprefix tailTrace_2554081
  have hstable : (prefixWord ++ tailWord_2554081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554081).length < 2 ^ (prefixWord ++ tailWord_2554081).sum := by decide
  have hdescent : baseEnd_2554081 < baseStart_2554081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554105 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 1, 3, 2]
def baseStart_2554105 : Nat := 118140960795 + 2554105 * 2 ^ 59
def prefixEnd_2554105 : Nat := 4983230072969 + 3 ^ 40 * 2554105 * 2
def baseEnd_2554105 : Nat := 1311483507051834786141391

theorem tailTrace_2554105 : CollatzResearch.WordTrace tailWord_2554105 prefixEnd_2554105 1311483507051834786141391 := by
  unfold tailWord_2554105
  simp only [CollatzResearch.WordTrace]
  refine ⟨93155862411921266250943769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62103908274614177500629179 93155862411921266250943769)
  ·
    refine ⟨69866896808940949688207827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93155862411921266250943769 69866896808940949688207827)
    ·
      refine ⟨104800345213411424532311741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69866896808940949688207827 104800345213411424532311741)
      ·
        refine ⟨39300129455029284199616903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104800345213411424532311741 39300129455029284199616903)
        ·
          refine ⟨58950194182543926299425355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39300129455029284199616903 58950194182543926299425355)
          ·
            refine ⟨88425291273815889449138033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58950194182543926299425355 88425291273815889449138033)
            ·
              refine ⟨66318968455361917086853525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88425291273815889449138033 66318968455361917086853525)
              ·
                refine ⟨3108701646345089863446259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66318968455361917086853525 3108701646345089863446259)
                ·
                  refine ⟨4663052469517634795169389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108701646345089863446259 4663052469517634795169389)
                  ·
                    refine ⟨1748644676069113048188521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4663052469517634795169389 1748644676069113048188521)
                    ·
                      refine ⟨1311483507051834786141391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748644676069113048188521 1311483507051834786141391)
                      ·
                        rfl

theorem cell23_2554105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_2554105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554105 prefixEnd_2554105 := by exact prefixLift 2554105
  have htrace : WordTrace (prefixWord ++ tailWord_2554105) baseStart_2554105 baseEnd_2554105 := by
    simpa [prefixWord, tailWord_2554105, baseEnd_2554105] using wordTrace_append hprefix tailTrace_2554105
  have hstable : (prefixWord ++ tailWord_2554105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554105).length < 2 ^ (prefixWord ++ tailWord_2554105).sum := by decide
  have hdescent : baseEnd_2554105 < baseStart_2554105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554131 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_2554131 : Nat := 118140960795 + 2554131 * 2 ^ 59
def prefixEnd_2554131 : Nat := 4983230072969 + 3 ^ 40 * 2554131 * 2
def baseEnd_2554131 : Nat := 1311496857548851684416271

theorem tailTrace_2554131 : CollatzResearch.WordTrace tailWord_2554131 prefixEnd_2554131 1311496857548851684416271 := by
  unfold tailWord_2554131
  simp only [CollatzResearch.WordTrace]
  refine ⟨93156810709827072691390247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62104540473218048460926831 93156810709827072691390247)
  ·
    refine ⟨139735216064740609037085371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93156810709827072691390247 139735216064740609037085371)
    ·
      refine ⟨209602824097110913555628057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139735216064740609037085371 209602824097110913555628057)
      ·
        refine ⟨157202118072833185166721043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209602824097110913555628057 157202118072833185166721043)
        ·
          refine ⟨235803177109249777750081565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157202118072833185166721043 235803177109249777750081565)
          ·
            refine ⟨88426191415968666656280587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235803177109249777750081565 88426191415968666656280587)
            ·
              refine ⟨132639287123952999984420881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88426191415968666656280587 132639287123952999984420881)
              ·
                refine ⟨99479465342964749988315661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132639287123952999984420881 99479465342964749988315661)
                ·
                  refine ⟨37304799503611781245618373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99479465342964749988315661 37304799503611781245618373)
                  ·
                    refine ⟨6994649906927208983553445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37304799503611781245618373 6994649906927208983553445)
                    ·
                      refine ⟨1311496857548851684416271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6994649906927208983553445 1311496857548851684416271)
                      ·
                        rfl

theorem cell23_2554131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_2554131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554131 prefixEnd_2554131 := by exact prefixLift 2554131
  have htrace : WordTrace (prefixWord ++ tailWord_2554131) baseStart_2554131 baseEnd_2554131 := by
    simpa [prefixWord, tailWord_2554131, baseEnd_2554131] using wordTrace_append hprefix tailTrace_2554131
  have hstable : (prefixWord ++ tailWord_2554131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554131).length < 2 ^ (prefixWord ++ tailWord_2554131).sum := by decide
  have hdescent : baseEnd_2554131 < baseStart_2554131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554148 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2554148 : Nat := 118140960795 + 2554148 * 2 ^ 59
def prefixEnd_2554148 : Nat := 4983230072969 + 3 ^ 40 * 2554148 * 2
def baseEnd_2554148 : Nat := 1311505586719978117903693

theorem tailTrace_2554148 : CollatzResearch.WordTrace tailWord_2554148 prefixEnd_2554148 1311505586719978117903693 := by
  unfold tailWord_2554148
  simp only [CollatzResearch.WordTrace]
  refine ⟨46578715375382742297379549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62104953833843656396506065 46578715375382742297379549)
  ·
    refine ⟨17467018265768528361517331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46578715375382742297379549 17467018265768528361517331)
    ·
      refine ⟨26200527398652792542275997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17467018265768528361517331 26200527398652792542275997)
      ·
        refine ⟨9825197774494797203353499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26200527398652792542275997 9825197774494797203353499)
        ·
          refine ⟨14737796661742195805030249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825197774494797203353499 14737796661742195805030249)
          ·
            refine ⟨11053347496306646853772687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14737796661742195805030249 11053347496306646853772687)
            ·
              refine ⟨16580021244459970280659031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11053347496306646853772687 16580021244459970280659031)
              ·
                refine ⟨24870031866689955420988547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16580021244459970280659031 24870031866689955420988547)
                ·
                  refine ⟨37305047800034933131482821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24870031866689955420988547 37305047800034933131482821)
                  ·
                    refine ⟨6994696462506549962153029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37305047800034933131482821 6994696462506549962153029)
                    ·
                      refine ⟨1311505586719978117903693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6994696462506549962153029 1311505586719978117903693)
                      ·
                        rfl

theorem cell23_2554148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2554148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554148 prefixEnd_2554148 := by exact prefixLift 2554148
  have htrace : WordTrace (prefixWord ++ tailWord_2554148) baseStart_2554148 baseEnd_2554148 := by
    simpa [prefixWord, tailWord_2554148, baseEnd_2554148] using wordTrace_append hprefix tailTrace_2554148
  have hstable : (prefixWord ++ tailWord_2554148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554148).length < 2 ^ (prefixWord ++ tailWord_2554148).sum := by decide
  have hdescent : baseEnd_2554148 < baseStart_2554148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554175 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 5]
def baseStart_2554175 : Nat := 118140960795 + 2554175 * 2 ^ 59
def prefixEnd_2554175 : Nat := 4983230072969 + 3 ^ 40 * 2554175 * 2
def baseEnd_2554175 : Nat := 145724383410849945807341

theorem tailTrace_2554175 : CollatzResearch.WordTrace tailWord_2554175 prefixEnd_2554175 145724383410849945807341 := by
  unfold tailWord_2554175
  simp only [CollatzResearch.WordTrace]
  refine ⟨93158415521667668205991979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62105610347778445470661319 93158415521667668205991979)
  ·
    refine ⟨139737623282501502308987969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93158415521667668205991979 139737623282501502308987969)
    ·
      refine ⟨104803217461876126731740977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139737623282501502308987969 104803217461876126731740977)
      ·
        refine ⟨78602413096407095048805733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104803217461876126731740977 78602413096407095048805733)
        ·
          refine ⟨14737952455576330321651075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78602413096407095048805733 14737952455576330321651075)
          ·
            refine ⟨22106928683364495482476613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14737952455576330321651075 22106928683364495482476613)
            ·
              refine ⟨4145049128130842902964365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22106928683364495482476613 4145049128130842902964365)
              ·
                refine ⟨1554393423049066088611637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145049128130842902964365 1554393423049066088611637)
                ·
                  refine ⟨145724383410849945807341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554393423049066088611637 145724383410849945807341)
                  ·
                    rfl

theorem cell23_2554175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 5].length) (baseStart_2554175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554175 prefixEnd_2554175 := by exact prefixLift 2554175
  have htrace : WordTrace (prefixWord ++ tailWord_2554175) baseStart_2554175 baseEnd_2554175 := by
    simpa [prefixWord, tailWord_2554175, baseEnd_2554175] using wordTrace_append hprefix tailTrace_2554175
  have hstable : (prefixWord ++ tailWord_2554175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554175).length < 2 ^ (prefixWord ++ tailWord_2554175).sum := by decide
  have hdescent : baseEnd_2554175 < baseStart_2554175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554188 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_2554188 : Nat := 118140960795 + 2554188 * 2 ^ 59
def prefixEnd_2554188 : Nat := 4983230072969 + 3 ^ 40 * 2554188 * 2
def baseEnd_2554188 : Nat := 437175375315385987134503

theorem tailTrace_2554188 : CollatzResearch.WordTrace tailWord_2554188 prefixEnd_2554188 437175375315385987134503 := by
  unfold tailWord_2554188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46579444835310285713107609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62105926447080380950810145 46579444835310285713107609)
  ·
    refine ⟨34934583626482714284830707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46579444835310285713107609 34934583626482714284830707)
    ·
      refine ⟨52401875439724071427246061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34934583626482714284830707 52401875439724071427246061)
      ·
        refine ⟨19650703289896526785217273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52401875439724071427246061 19650703289896526785217273)
        ·
          refine ⟨14738027467422395088912955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19650703289896526785217273 14738027467422395088912955)
          ·
            refine ⟨22107041201133592633369433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14738027467422395088912955 22107041201133592633369433)
            ·
              refine ⟨16580280900850194475027075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22107041201133592633369433 16580280900850194475027075)
              ·
                refine ⟨24870421351275291712540613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16580280900850194475027075 24870421351275291712540613)
                ·
                  refine ⟨4663204003364117196101365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24870421351275291712540613 4663204003364117196101365)
                  ·
                    refine ⟨437175375315385987134503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4663204003364117196101365 437175375315385987134503)
                    ·
                      rfl

theorem cell23_2554188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_2554188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554188 prefixEnd_2554188 := by exact prefixLift 2554188
  have htrace : WordTrace (prefixWord ++ tailWord_2554188) baseStart_2554188 baseEnd_2554188 := by
    simpa [prefixWord, tailWord_2554188, baseEnd_2554188] using wordTrace_append hprefix tailTrace_2554188
  have hstable : (prefixWord ++ tailWord_2554188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554188).length < 2 ^ (prefixWord ++ tailWord_2554188).sum := by decide
  have hdescent : baseEnd_2554188 < baseStart_2554188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
