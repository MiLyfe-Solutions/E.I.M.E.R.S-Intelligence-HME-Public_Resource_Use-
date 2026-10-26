import V185TrunkScan23Chunk0929

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5504542 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5504542 : Nat := 118140960795 + 5504542 * 2 ^ 59
def prefixEnd_5504542 : Nat := 4983230072969 + 3 ^ 40 * 5504542 * 2
def baseEnd_5504542 : Nat := 942158609620435895936693

theorem tailTrace_5504542 : CollatzResearch.WordTrace tailWord_5504542 prefixEnd_5504542 942158609620435895936693 := by
  unfold tailWord_5504542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25095892552998988721681485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133844760282661273182301253 25095892552998988721681485)
  ·
    refine ⟨9410959707374620770630557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25095892552998988721681485 9410959707374620770630557)
    ·
      refine ⟨3529109890265482788986459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9410959707374620770630557 3529109890265482788986459)
      ·
        refine ⟨5293664835398224183479689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529109890265482788986459 5293664835398224183479689)
        ·
          refine ⟨3970248626548668137609767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5293664835398224183479689 3970248626548668137609767)
          ·
            refine ⟨5955372939823002206414651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970248626548668137609767 5955372939823002206414651)
            ·
              refine ⟨8933059409734503309621977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955372939823002206414651 8933059409734503309621977)
              ·
                refine ⟨6699794557300877482216483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933059409734503309621977 6699794557300877482216483)
                ·
                  refine ⟨10049691835951316223324725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699794557300877482216483 10049691835951316223324725)
                  ·
                    refine ⟨942158609620435895936693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10049691835951316223324725 942158609620435895936693)
                    ·
                      rfl

theorem cell23_5504542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5504542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504542 prefixEnd_5504542 := by exact prefixLift 5504542
  have htrace : WordTrace (prefixWord ++ tailWord_5504542) baseStart_5504542 baseEnd_5504542 := by
    simpa [prefixWord, tailWord_5504542, baseEnd_5504542] using wordTrace_append hprefix tailTrace_5504542
  have hstable : (prefixWord ++ tailWord_5504542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504542).length < 2 ^ (prefixWord ++ tailWord_5504542).sum := by decide
  have hdescent : baseEnd_5504542 < baseStart_5504542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504560 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_5504560 : Nat := 118140960795 + 5504560 * 2 ^ 59
def prefixEnd_5504560 : Nat := 4983230072969 + 3 ^ 40 * 5504560 * 2
def baseEnd_5504560 : Nat := 942161690504362872461665

theorem tailTrace_5504560 : CollatzResearch.WordTrace tailWord_5504560 prefixEnd_5504560 942161690504362872461665 := by
  unfold tailWord_5504560
  simp only [CollatzResearch.WordTrace]
  refine ⟨100383898468963349423803567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133845197958617799231738089 100383898468963349423803567)
  ·
    refine ⟨150575847703445024135705351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100383898468963349423803567 150575847703445024135705351)
    ·
      refine ⟨225863771555167536203558027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150575847703445024135705351 225863771555167536203558027)
      ·
        refine ⟨338795657332751304305337041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225863771555167536203558027 338795657332751304305337041)
        ·
          refine ⟨254096742999563478229002781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338795657332751304305337041 254096742999563478229002781)
          ·
            refine ⟨95286278624836304335876043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254096742999563478229002781 95286278624836304335876043)
            ·
              refine ⟨142929417937254456503814065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95286278624836304335876043 142929417937254456503814065)
              ·
                refine ⟨107197063452940842377860549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142929417937254456503814065 107197063452940842377860549)
                ·
                  refine ⟨20099449397426407945848853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107197063452940842377860549 20099449397426407945848853)
                  ·
                    refine ⟨942161690504362872461665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20099449397426407945848853 942161690504362872461665)
                    ·
                      rfl

theorem cell23_5504560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_5504560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504560 prefixEnd_5504560 := by exact prefixLift 5504560
  have htrace : WordTrace (prefixWord ++ tailWord_5504560) baseStart_5504560 baseEnd_5504560 := by
    simpa [prefixWord, tailWord_5504560, baseEnd_5504560] using wordTrace_append hprefix tailTrace_5504560
  have hstable : (prefixWord ++ tailWord_5504560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504560).length < 2 ^ (prefixWord ++ tailWord_5504560).sum := by decide
  have hdescent : baseEnd_5504560 < baseStart_5504560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504577 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5504577 : Nat := 118140960795 + 5504577 * 2 ^ 59
def prefixEnd_5504577 : Nat := 4983230072969 + 3 ^ 40 * 5504577 * 2
def baseEnd_5504577 : Nat := 942164600228071683624139

theorem tailTrace_5504577 : CollatzResearch.WordTrace tailWord_5504577 prefixEnd_5504577 942164600228071683624139 := by
  unfold tailWord_5504577
  simp only [CollatzResearch.WordTrace]
  refine ⟨200768416978865110750975985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133845611319243407167317323 200768416978865110750975985)
  ·
    refine ⟨150576312734148833063231989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200768416978865110750975985 150576312734148833063231989)
    ·
      refine ⟨14116529318826453099677999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150576312734148833063231989 14116529318826453099677999)
      ·
        refine ⟨21174793978239679649516999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14116529318826453099677999 21174793978239679649516999)
        ·
          refine ⟨31762190967359519474275499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21174793978239679649516999 31762190967359519474275499)
          ·
            refine ⟨47643286451039279211413249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31762190967359519474275499 47643286451039279211413249)
            ·
              refine ⟨35732464838279459408559937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47643286451039279211413249 35732464838279459408559937)
              ·
                refine ⟨26799348628709594556419953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35732464838279459408559937 26799348628709594556419953)
                ·
                  refine ⟨20099511471532195917314965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26799348628709594556419953 20099511471532195917314965)
                  ·
                    refine ⟨942164600228071683624139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20099511471532195917314965 942164600228071683624139)
                    ·
                      rfl

theorem cell23_5504577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5504577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504577 prefixEnd_5504577 := by exact prefixLift 5504577
  have htrace : WordTrace (prefixWord ++ tailWord_5504577) baseStart_5504577 baseEnd_5504577 := by
    simpa [prefixWord, tailWord_5504577, baseEnd_5504577] using wordTrace_append hprefix tailTrace_5504577
  have hstable : (prefixWord ++ tailWord_5504577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504577).length < 2 ^ (prefixWord ++ tailWord_5504577).sum := by decide
  have hdescent : baseEnd_5504577 < baseStart_5504577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504622 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_5504622 : Nat := 118140960795 + 5504622 * 2 ^ 59
def prefixEnd_5504622 : Nat := 4983230072969 + 3 ^ 40 * 5504622 * 2
def baseEnd_5504622 : Nat := 2826516907313667374809711

theorem tailTrace_5504622 : CollatzResearch.WordTrace tailWord_5504622 prefixEnd_5504622 2826516907313667374809711 := by
  unfold tailWord_5504622
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096257282962760429545515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133846705509134722290909413 25096257282962760429545515)
  ·
    refine ⟨37644385924444140644318273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25096257282962760429545515 37644385924444140644318273)
    ·
      refine ⟨28233289443333105483238705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37644385924444140644318273 28233289443333105483238705)
      ·
        refine ⟨21174967082499829112429029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28233289443333105483238705 21174967082499829112429029)
        ·
          refine ⟨3970306327968717958580443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21174967082499829112429029 3970306327968717958580443)
          ·
            refine ⟨5955459491953076937870665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970306327968717958580443 5955459491953076937870665)
            ·
              refine ⟨4466594618964807703402999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5955459491953076937870665 4466594618964807703402999)
              ·
                refine ⟨6699891928447211555104499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466594618964807703402999 6699891928447211555104499)
                ·
                  refine ⟨10049837892670817332656749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699891928447211555104499 10049837892670817332656749)
                  ·
                    refine ⟨3768689209751556499746281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10049837892670817332656749 3768689209751556499746281)
                    ·
                      refine ⟨2826516907313667374809711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768689209751556499746281 2826516907313667374809711)
                      ·
                        rfl

theorem cell23_5504622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_5504622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504622 prefixEnd_5504622 := by exact prefixLift 5504622
  have htrace : WordTrace (prefixWord ++ tailWord_5504622) baseStart_5504622 baseEnd_5504622 := by
    simpa [prefixWord, tailWord_5504622, baseEnd_5504622] using wordTrace_append hprefix tailTrace_5504622
  have hstable : (prefixWord ++ tailWord_5504622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504622).length < 2 ^ (prefixWord ++ tailWord_5504622).sum := by decide
  have hdescent : baseEnd_5504622 < baseStart_5504622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504624 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 5]
def baseStart_5504624 : Nat := 118140960795 + 5504624 * 2 ^ 59
def prefixEnd_5504624 : Nat := 4983230072969 + 3 ^ 40 * 5504624 * 2
def baseEnd_5504624 : Nat := 314057548252775151887189

theorem tailTrace_5504624 : CollatzResearch.WordTrace tailWord_5504624 prefixEnd_5504624 314057548252775151887189 := by
  unfold tailWord_5504624
  simp only [CollatzResearch.WordTrace]
  refine ⟨100385065604847418888968463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133846754139796558518624617 100385065604847418888968463)
  ·
    refine ⟨150577598407271128333452695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100385065604847418888968463 150577598407271128333452695)
    ·
      refine ⟨225866397610906692500179043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150577598407271128333452695 225866397610906692500179043)
      ·
        refine ⟨338799596416360038750268565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225866397610906692500179043 338799596416360038750268565)
        ·
          refine ⟨15881231082016876816418839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 338799596416360038750268565 15881231082016876816418839)
          ·
            refine ⟨23821846623025315224628259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15881231082016876816418839 23821846623025315224628259)
            ·
              refine ⟨35732769934537972836942389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23821846623025315224628259 35732769934537972836942389)
              ·
                refine ⟨3349947181362934953463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35732769934537972836942389 3349947181362934953463349)
                ·
                  refine ⟨314057548252775151887189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3349947181362934953463349 314057548252775151887189)
                  ·
                    rfl

theorem cell23_5504624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 5].length) (baseStart_5504624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504624 prefixEnd_5504624 := by exact prefixLift 5504624
  have htrace : WordTrace (prefixWord ++ tailWord_5504624) baseStart_5504624 baseEnd_5504624 := by
    simpa [prefixWord, tailWord_5504624, baseEnd_5504624] using wordTrace_append hprefix tailTrace_5504624
  have hstable : (prefixWord ++ tailWord_5504624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504624).length < 2 ^ (prefixWord ++ tailWord_5504624).sum := by decide
  have hdescent : baseEnd_5504624 < baseStart_5504624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504657 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_5504657 : Nat := 118140960795 + 5504657 * 2 ^ 59
def prefixEnd_5504657 : Nat := 4983230072969 + 3 ^ 40 * 5504657 * 2
def baseEnd_5504657 : Nat := 2826534879136574737872049

theorem tailTrace_5504657 : CollatzResearch.WordTrace tailWord_5504657 prefixEnd_5504657 2826534879136574737872049 := by
  unfold tailWord_5504657
  simp only [CollatzResearch.WordTrace]
  refine ⟨200771334818575284413888225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133847556545716856275925483 200771334818575284413888225)
  ·
    refine ⟨150578501113931463310416169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200771334818575284413888225 150578501113931463310416169)
    ·
      refine ⟨112933875835448597482812127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150578501113931463310416169 112933875835448597482812127)
      ·
        refine ⟨169400813753172896224218191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112933875835448597482812127 169400813753172896224218191)
        ·
          refine ⟨254101220629759344336327287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169400813753172896224218191 254101220629759344336327287)
          ·
            refine ⟨381151830944639016504490931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254101220629759344336327287 381151830944639016504490931)
            ·
              refine ⟨571727746416958524756736397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381151830944639016504490931 571727746416958524756736397)
              ·
                refine ⟨214397904906359446783776149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571727746416958524756736397 214397904906359446783776149)
                ·
                  refine ⟨10049901792485599067989507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214397904906359446783776149 10049901792485599067989507)
                  ·
                    refine ⟨15074852688728398601984261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10049901792485599067989507 15074852688728398601984261)
                    ·
                      refine ⟨2826534879136574737872049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15074852688728398601984261 2826534879136574737872049)
                      ·
                        rfl

theorem cell23_5504657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_5504657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504657 prefixEnd_5504657 := by exact prefixLift 5504657
  have htrace : WordTrace (prefixWord ++ tailWord_5504657) baseStart_5504657 baseEnd_5504657 := by
    simpa [prefixWord, tailWord_5504657, baseEnd_5504657] using wordTrace_append hprefix tailTrace_5504657
  have hstable : (prefixWord ++ tailWord_5504657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504657).length < 2 ^ (prefixWord ++ tailWord_5504657).sum := by decide
  have hdescent : baseEnd_5504657 < baseStart_5504657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504697 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 8]
def baseStart_5504697 : Nat := 118140960795 + 5504697 * 2 ^ 59
def prefixEnd_5504697 : Nat := 4983230072969 + 3 ^ 40 * 5504697 * 2
def baseEnd_5504697 : Nat := 314061713151417175707985

theorem tailTrace_5504697 : CollatzResearch.WordTrace tailWord_5504697 prefixEnd_5504697 314061713151417175707985 := by
  unfold tailWord_5504697
  simp only [CollatzResearch.WordTrace]
  refine ⟨200772793738430371245344345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133848529158953580830229563 200772793738430371245344345)
  ·
    refine ⟨150579595303822778434008259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200772793738430371245344345 150579595303822778434008259)
    ·
      refine ⟨225869392955734167651012389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150579595303822778434008259 225869392955734167651012389)
      ·
        refine ⟨42350511179200156434564823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225869392955734167651012389 42350511179200156434564823)
        ·
          refine ⟨63525766768800234651847235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42350511179200156434564823 63525766768800234651847235)
          ·
            refine ⟨95288650153200351977770853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63525766768800234651847235 95288650153200351977770853)
            ·
              refine ⟨17866621903725065995832035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95288650153200351977770853 17866621903725065995832035)
              ·
                refine ⟨26799932855587598993748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17866621903725065995832035 26799932855587598993748053)
                ·
                  refine ⟨314061713151417175707985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26799932855587598993748053 314061713151417175707985)
                  ·
                    rfl

theorem cell23_5504697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_5504697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504697 prefixEnd_5504697 := by exact prefixLift 5504697
  have htrace : WordTrace (prefixWord ++ tailWord_5504697) baseStart_5504697 baseEnd_5504697 := by
    simpa [prefixWord, tailWord_5504697, baseEnd_5504697] using wordTrace_append hprefix tailTrace_5504697
  have hstable : (prefixWord ++ tailWord_5504697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504697).length < 2 ^ (prefixWord ++ tailWord_5504697).sum := by decide
  have hdescent : baseEnd_5504697 < baseStart_5504697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504751 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 2, 3, 2]
def baseStart_5504751 : Nat := 118140960795 + 5504751 * 2 ^ 59
def prefixEnd_5504751 : Nat := 4983230072969 + 3 ^ 40 * 5504751 * 2
def baseEnd_5504751 : Nat := 2826583146318097370096617

theorem tailTrace_5504751 : CollatzResearch.WordTrace tailWord_5504751 prefixEnd_5504751 2826583146318097370096617 := by
  unfold tailWord_5504751
  simp only [CollatzResearch.WordTrace]
  refine ⟨200774763280234738467810107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133849842186823158978540071 200774763280234738467810107)
  ·
    refine ⟨301162144920352107701715161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200774763280234738467810107 301162144920352107701715161)
    ·
      refine ⟨225871608690264080776286371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301162144920352107701715161 225871608690264080776286371)
      ·
        refine ⟨338807413035396121164429557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225871608690264080776286371 338807413035396121164429557)
        ·
          refine ⟨31763194972068386359165271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338807413035396121164429557 31763194972068386359165271)
          ·
            refine ⟨47644792458102579538747907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31763194972068386359165271 47644792458102579538747907)
            ·
              refine ⟨71467188687153869308121861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47644792458102579538747907 71467188687153869308121861)
              ·
                refine ⟨13400097878841350495272849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71467188687153869308121861 13400097878841350495272849)
                ·
                  refine ⟨10050073409131012871454637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13400097878841350495272849 10050073409131012871454637)
                  ·
                    refine ⟨3768777528424129826795489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10050073409131012871454637 3768777528424129826795489)
                    ·
                      refine ⟨2826583146318097370096617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768777528424129826795489 2826583146318097370096617)
                      ·
                        rfl

theorem cell23_5504751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3, 2].length) (baseStart_5504751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504751 prefixEnd_5504751 := by exact prefixLift 5504751
  have htrace : WordTrace (prefixWord ++ tailWord_5504751) baseStart_5504751 baseEnd_5504751 := by
    simpa [prefixWord, tailWord_5504751, baseEnd_5504751] using wordTrace_append hprefix tailTrace_5504751
  have hstable : (prefixWord ++ tailWord_5504751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504751).length < 2 ^ (prefixWord ++ tailWord_5504751).sum := by decide
  have hdescent : baseEnd_5504751 < baseStart_5504751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504764 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_5504764 : Nat := 118140960795 + 5504764 * 2 ^ 59
def prefixEnd_5504764 : Nat := 4983230072969 + 3 ^ 40 * 5504764 * 2
def baseEnd_5504764 : Nat := 2826589821566605819234057

theorem tailTrace_5504764 : CollatzResearch.WordTrace tailWord_5504764 prefixEnd_5504764 2826589821566605819234057 := by
  unfold tailWord_5504764
  simp only [CollatzResearch.WordTrace]
  refine ⟨100387618714593820844016673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133850158286125094458688897 100387618714593820844016673)
  ·
    refine ⟨75290714035945365633012505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100387618714593820844016673 75290714035945365633012505)
    ·
      refine ⟨56468035526959024224759379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75290714035945365633012505 56468035526959024224759379)
      ·
        refine ⟨84702053290438536337139069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56468035526959024224759379 84702053290438536337139069)
        ·
          refine ⟨31763269983914451126427151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84702053290438536337139069 31763269983914451126427151)
          ·
            refine ⟨47644904975871676689640727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31763269983914451126427151 47644904975871676689640727)
            ·
              refine ⟨71467357463807515034461091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47644904975871676689640727 71467357463807515034461091)
              ·
                refine ⟨107201036195711272551691637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71467357463807515034461091 107201036195711272551691637)
                ·
                  refine ⟨10050097143347931801721091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107201036195711272551691637 10050097143347931801721091)
                  ·
                    refine ⟨15075145715021897702581637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10050097143347931801721091 15075145715021897702581637)
                    ·
                      refine ⟨2826589821566605819234057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15075145715021897702581637 2826589821566605819234057)
                      ·
                        rfl

theorem cell23_5504764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_5504764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504764 prefixEnd_5504764 := by exact prefixLift 5504764
  have htrace : WordTrace (prefixWord ++ tailWord_5504764) baseStart_5504764 baseEnd_5504764 := by
    simpa [prefixWord, tailWord_5504764, baseEnd_5504764] using wordTrace_append hprefix tailTrace_5504764
  have hstable : (prefixWord ++ tailWord_5504764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504764).length < 2 ^ (prefixWord ++ tailWord_5504764).sum := by decide
  have hdescent : baseEnd_5504764 < baseStart_5504764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504804 : List Nat := [2, 3, 1, 3, 2, 2, 10]
def baseStart_5504804 : Nat := 118140960795 + 5504804 * 2 ^ 59
def prefixEnd_5504804 : Nat := 4983230072969 + 3 ^ 40 * 5504804 * 2
def baseEnd_5504804 : Nat := 34896424207318341515233

theorem tailTrace_5504804 : CollatzResearch.WordTrace tailWord_5504804 prefixEnd_5504804 34896424207318341515233 := by
  unfold tailWord_5504804
  simp only [CollatzResearch.WordTrace]
  refine ⟨100388348174521364259744733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133851130899361819012992977 100388348174521364259744733)
  ·
    refine ⟨37645630565445511597404275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100388348174521364259744733 37645630565445511597404275)
    ·
      refine ⟨56468445848168267396106413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37645630565445511597404275 56468445848168267396106413)
      ·
        refine ⟨21175667193063100273539905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56468445848168267396106413 21175667193063100273539905)
        ·
          refine ⟨15881750394797325205154929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21175667193063100273539905 15881750394797325205154929)
          ·
            refine ⟨11911312796097993903866197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15881750394797325205154929 11911312796097993903866197)
            ·
              refine ⟨34896424207318341515233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11911312796097993903866197 34896424207318341515233)
              ·
                rfl

theorem cell23_5504804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 10].length) (baseStart_5504804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504804 prefixEnd_5504804 := by exact prefixLift 5504804
  have htrace : WordTrace (prefixWord ++ tailWord_5504804) baseStart_5504804 baseEnd_5504804 := by
    simpa [prefixWord, tailWord_5504804, baseEnd_5504804] using wordTrace_append hprefix tailTrace_5504804
  have hstable : (prefixWord ++ tailWord_5504804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504804).length < 2 ^ (prefixWord ++ tailWord_5504804).sum := by decide
  have hdescent : baseEnd_5504804 < baseStart_5504804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504808 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_5504808 : Nat := 118140960795 + 5504808 * 2 ^ 59
def prefixEnd_5504808 : Nat := 4983230072969 + 3 ^ 40 * 5504808 * 2
def baseEnd_5504808 : Nat := 942204138238467882361285

theorem tailTrace_5504808 : CollatzResearch.WordTrace tailWord_5504808 prefixEnd_5504808 942204138238467882361285 := by
  unfold tailWord_5504808
  simp only [CollatzResearch.WordTrace]
  refine ⟨100388421120514118601317539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133851228160685491468423385 100388421120514118601317539)
  ·
    refine ⟨150582631680771177901976309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100388421120514118601317539 150582631680771177901976309)
    ·
      refine ⟨14117121720072297928310279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150582631680771177901976309 14117121720072297928310279)
      ·
        refine ⟨21175682580108446892465419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14117121720072297928310279 21175682580108446892465419)
        ·
          refine ⟨31763523870162670338698129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21175682580108446892465419 31763523870162670338698129)
          ·
            refine ⟨23822642902622002754023597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31763523870162670338698129 23822642902622002754023597)
            ·
              refine ⟨8933491088483251032758849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23822642902622002754023597 8933491088483251032758849)
              ·
                refine ⟨6700118316362438274569137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933491088483251032758849 6700118316362438274569137)
                ·
                  refine ⟨5025088737271828705926853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6700118316362438274569137 5025088737271828705926853)
                  ·
                    refine ⟨942204138238467882361285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5025088737271828705926853 942204138238467882361285)
                    ·
                      rfl

theorem cell23_5504808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_5504808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504808 prefixEnd_5504808 := by exact prefixLift 5504808
  have htrace : WordTrace (prefixWord ++ tailWord_5504808) baseStart_5504808 baseEnd_5504808 := by
    simpa [prefixWord, tailWord_5504808, baseEnd_5504808] using wordTrace_append hprefix tailTrace_5504808
  have hstable : (prefixWord ++ tailWord_5504808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504808).length < 2 ^ (prefixWord ++ tailWord_5504808).sum := by decide
  have hdescent : baseEnd_5504808 < baseStart_5504808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504825 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 1, 6]
def baseStart_5504825 : Nat := 118140960795 + 5504825 * 2 ^ 59
def prefixEnd_5504825 : Nat := 4983230072969 + 3 ^ 40 * 5504825 * 2
def baseEnd_5504825 : Nat := 942207047962176693523759

theorem tailTrace_5504825 : CollatzResearch.WordTrace tailWord_5504825 prefixEnd_5504825 942207047962176693523759 := by
  unfold tailWord_5504825
  simp only [CollatzResearch.WordTrace]
  refine ⟨200777462281966649106003929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133851641521311099404002619 200777462281966649106003929)
  ·
    refine ⟨150583096711474986829502947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200777462281966649106003929 150583096711474986829502947)
    ·
      refine ⟨225874645067212480244254421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150583096711474986829502947 225874645067212480244254421)
      ·
        refine ⟨5293936993762792505724713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 225874645067212480244254421 5293936993762792505724713)
        ·
          refine ⟨3970452745322094379293535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5293936993762792505724713 3970452745322094379293535)
          ·
            refine ⟨5955679117983141568940303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970452745322094379293535 5955679117983141568940303)
            ·
              refine ⟨8933518676974712353410455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955679117983141568940303 8933518676974712353410455)
              ·
                refine ⟨13400278015462068530115683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8933518676974712353410455 13400278015462068530115683)
                ·
                  refine ⟨20100417023193102795173525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13400278015462068530115683 20100417023193102795173525)
                  ·
                    refine ⟨942207047962176693523759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20100417023193102795173525 942207047962176693523759)
                    ·
                      rfl

theorem cell23_5504825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_5504825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504825 prefixEnd_5504825 := by exact prefixLift 5504825
  have htrace : WordTrace (prefixWord ++ tailWord_5504825) baseStart_5504825 baseEnd_5504825 := by
    simpa [prefixWord, tailWord_5504825, baseEnd_5504825] using wordTrace_append hprefix tailTrace_5504825
  have hstable : (prefixWord ++ tailWord_5504825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504825).length < 2 ^ (prefixWord ++ tailWord_5504825).sum := by decide
  have hdescent : baseEnd_5504825 < baseStart_5504825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504838 : List Nat := [6, 1, 1, 2, 1, 2, 1, 9]
def baseStart_5504838 : Nat := 118140960795 + 5504838 * 2 ^ 59
def prefixEnd_5504838 : Nat := 4983230072969 + 3 ^ 40 * 5504838 * 2
def baseEnd_5504838 : Nat := 104689919227223649248471

theorem tailTrace_5504838 : CollatzResearch.WordTrace tailWord_5504838 prefixEnd_5504838 104689919227223649248471 := by
  unfold tailWord_5504838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274310513466236010194599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133851957620613034884151445 6274310513466236010194599)
  ·
    refine ⟨9411465770199354015291899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6274310513466236010194599 9411465770199354015291899)
    ·
      refine ⟨14117198655299031022937849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9411465770199354015291899 14117198655299031022937849)
      ·
        refine ⟨10587898991474273267203387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14117198655299031022937849 10587898991474273267203387)
        ·
          refine ⟨15881848487211409900805081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587898991474273267203387 15881848487211409900805081)
          ·
            refine ⟨11911386365408557425603811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15881848487211409900805081 11911386365408557425603811)
            ·
              refine ⟨17867079548112836138405717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11911386365408557425603811 17867079548112836138405717)
              ·
                refine ⟨104689919227223649248471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17867079548112836138405717 104689919227223649248471)
                ·
                  rfl

theorem cell23_5504838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_5504838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504838 prefixEnd_5504838 := by exact prefixLift 5504838
  have htrace : WordTrace (prefixWord ++ tailWord_5504838) baseStart_5504838 baseEnd_5504838 := by
    simpa [prefixWord, tailWord_5504838, baseEnd_5504838] using wordTrace_append hprefix tailTrace_5504838
  have hstable : (prefixWord ++ tailWord_5504838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504838).length < 2 ^ (prefixWord ++ tailWord_5504838).sum := by decide
  have hdescent : baseEnd_5504838 < baseStart_5504838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504858 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_5504858 : Nat := 118140960795 + 5504858 * 2 ^ 59
def prefixEnd_5504858 : Nat := 4983230072969 + 3 ^ 40 * 5504858 * 2
def baseEnd_5504858 : Nat := 2826638088748128451458625

theorem tailTrace_5504858 : CollatzResearch.WordTrace tailWord_5504858 prefixEnd_5504858 2826638088748128451458625 := by
  unfold tailWord_5504858
  simp only [CollatzResearch.WordTrace]
  refine ⟨50194666472711773935488807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133852443927231397161303485 50194666472711773935488807)
  ·
    refine ⟨75291999709067660903233211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50194666472711773935488807 75291999709067660903233211)
    ·
      refine ⟨112937999563601491354849817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75291999709067660903233211 112937999563601491354849817)
      ·
        refine ⟨84703499672701118516137363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112937999563601491354849817 84703499672701118516137363)
        ·
          refine ⟨127055249509051677774206045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84703499672701118516137363 127055249509051677774206045)
          ·
            refine ⟨47645718565894379165327267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127055249509051677774206045 47645718565894379165327267)
            ·
              refine ⟨71468577848841568747990901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47645718565894379165327267 71468577848841568747990901)
              ·
                refine ⟨6700179173328897070124147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71468577848841568747990901 6700179173328897070124147)
                ·
                  refine ⟨10050268759993345605186221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6700179173328897070124147 10050268759993345605186221)
                  ·
                    refine ⟨3768850784997504601944833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10050268759993345605186221 3768850784997504601944833)
                    ·
                      refine ⟨2826638088748128451458625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768850784997504601944833 2826638088748128451458625)
                      ·
                        rfl

theorem cell23_5504858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_5504858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504858 prefixEnd_5504858 := by exact prefixLift 5504858
  have htrace : WordTrace (prefixWord ++ tailWord_5504858) baseStart_5504858 baseEnd_5504858 := by
    simpa [prefixWord, tailWord_5504858, baseEnd_5504858] using wordTrace_append hprefix tailTrace_5504858
  have hstable : (prefixWord ++ tailWord_5504858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504858).length < 2 ^ (prefixWord ++ tailWord_5504858).sum := by decide
  have hdescent : baseEnd_5504858 < baseStart_5504858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504922 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5504922 : Nat := 118140960795 + 5504922 * 2 ^ 59
def prefixEnd_5504922 : Nat := 4983230072969 + 3 ^ 40 * 5504922 * 2
def baseEnd_5504922 : Nat := 2826670951510016201058331

theorem tailTrace_5504922 : CollatzResearch.WordTrace tailWord_5504922 prefixEnd_5504922 2826670951510016201058331 := by
  unfold tailWord_5504922
  simp only [CollatzResearch.WordTrace]
  refine ⟨50195250040653808668071255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133854000108410156448190013 50195250040653808668071255)
  ·
    refine ⟨75292875060980713002106883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50195250040653808668071255 75292875060980713002106883)
    ·
      refine ⟨112939312591471069503160325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75292875060980713002106883 112939312591471069503160325)
      ·
        refine ⟨21176121110900825531842561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112939312591471069503160325 21176121110900825531842561)
        ·
          refine ⟨15882090833175619148881921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21176121110900825531842561 15882090833175619148881921)
          ·
            refine ⟨11911568124881714361661441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15882090833175619148881921 11911568124881714361661441)
            ·
              refine ⟨8933676093661285771246081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11911568124881714361661441 8933676093661285771246081)
              ·
                refine ⟨6700257070245964328434561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933676093661285771246081 6700257070245964328434561)
                ·
                  refine ⟨5025192802684473246325921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6700257070245964328434561 5025192802684473246325921)
                  ·
                    refine ⟨3768894602013354934744441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5025192802684473246325921 3768894602013354934744441)
                    ·
                      refine ⟨2826670951510016201058331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768894602013354934744441 2826670951510016201058331)
                      ·
                        rfl

theorem cell23_5504922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5504922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504922 prefixEnd_5504922 := by exact prefixLift 5504922
  have htrace : WordTrace (prefixWord ++ tailWord_5504922) baseStart_5504922 baseEnd_5504922 := by
    simpa [prefixWord, tailWord_5504922, baseEnd_5504922] using wordTrace_append hprefix tailTrace_5504922
  have hstable : (prefixWord ++ tailWord_5504922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504922).length < 2 ^ (prefixWord ++ tailWord_5504922).sum := by decide
  have hdescent : baseEnd_5504922 < baseStart_5504922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504954 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_5504954 : Nat := 118140960795 + 5504954 * 2 ^ 59
def prefixEnd_5504954 : Nat := 4983230072969 + 3 ^ 40 * 5504954 * 2
def baseEnd_5504954 : Nat := 942229127630320025286061

theorem tailTrace_5504954 : CollatzResearch.WordTrace tailWord_5504954 prefixEnd_5504954 942229127630320025286061 := by
  unfold tailWord_5504954
  simp only [CollatzResearch.WordTrace]
  refine ⟨50195541824624826034362479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133854778198999536091633277 50195541824624826034362479)
  ·
    refine ⟨75293312736937239051543719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50195541824624826034362479 75293312736937239051543719)
    ·
      refine ⟨112939969105405858577315579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75293312736937239051543719 112939969105405858577315579)
      ·
        refine ⟨169409953658108787865973369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112939969105405858577315579 169409953658108787865973369)
        ·
          refine ⟨127057465243581590899480027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169409953658108787865973369 127057465243581590899480027)
          ·
            refine ⟨190586197865372386349220041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127057465243581590899480027 190586197865372386349220041)
            ·
              refine ⟨142939648399029289761915031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190586197865372386349220041 142939648399029289761915031)
              ·
                refine ⟨214409472598543934642872547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142939648399029289761915031 214409472598543934642872547)
                ·
                  refine ⟨321614208897815901964308821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214409472598543934642872547 321614208897815901964308821)
                  ·
                    refine ⟨942229127630320025286061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 321614208897815901964308821 942229127630320025286061)
                    ·
                      rfl

theorem cell23_5504954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_5504954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504954 prefixEnd_5504954 := by exact prefixLift 5504954
  have htrace : WordTrace (prefixWord ++ tailWord_5504954) baseStart_5504954 baseEnd_5504954 := by
    simpa [prefixWord, tailWord_5504954, baseEnd_5504954] using wordTrace_append hprefix tailTrace_5504954
  have hstable : (prefixWord ++ tailWord_5504954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504954).length < 2 ^ (prefixWord ++ tailWord_5504954).sum := by decide
  have hdescent : baseEnd_5504954 < baseStart_5504954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504958 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_5504958 : Nat := 118140960795 + 5504958 * 2 ^ 59
def prefixEnd_5504958 : Nat := 4983230072969 + 3 ^ 40 * 5504958 * 2
def baseEnd_5504958 : Nat := 942229812271192686736055

theorem tailTrace_5504958 : CollatzResearch.WordTrace tailWord_5504958 prefixEnd_5504958 942229812271192686736055 := by
  unfold tailWord_5504958
  simp only [CollatzResearch.WordTrace]
  refine ⟨25097789148810601602574441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133854875460323208547063685 25097789148810601602574441)
  ·
    refine ⟨18823341861607951201930831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25097789148810601602574441 18823341861607951201930831)
    ·
      refine ⟨28235012792411926802896247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18823341861607951201930831 28235012792411926802896247)
      ·
        refine ⟨42352519188617890204344371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28235012792411926802896247 42352519188617890204344371)
        ·
          refine ⟨63528778782926835306516557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42352519188617890204344371 63528778782926835306516557)
          ·
            refine ⟨23823292043597563239943709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63528778782926835306516557 23823292043597563239943709)
            ·
              refine ⟨8933734516349086214978891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23823292043597563239943709 8933734516349086214978891)
              ·
                refine ⟨13400601774523629322468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8933734516349086214978891 13400601774523629322468337)
                ·
                  refine ⟨10050451330892721991851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13400601774523629322468337 10050451330892721991851253)
                  ·
                    refine ⟨942229812271192686736055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10050451330892721991851253 942229812271192686736055)
                    ·
                      rfl

theorem cell23_5504958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_5504958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504958 prefixEnd_5504958 := by exact prefixLift 5504958
  have htrace : WordTrace (prefixWord ++ tailWord_5504958) baseStart_5504958 baseEnd_5504958 := by
    simpa [prefixWord, tailWord_5504958, baseEnd_5504958] using wordTrace_append hprefix tailTrace_5504958
  have hstable : (prefixWord ++ tailWord_5504958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504958).length < 2 ^ (prefixWord ++ tailWord_5504958).sum := by decide
  have hdescent : baseEnd_5504958 < baseStart_5504958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504971 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 5, 4]
def baseStart_5504971 : Nat := 118140960795 + 5504971 * 2 ^ 59
def prefixEnd_5504971 : Nat := 4983230072969 + 3 ^ 40 * 5504971 * 2
def baseEnd_5504971 : Nat := 942232037354028836448535

theorem tailTrace_5504971 : CollatzResearch.WordTrace tailWord_5504971 prefixEnd_5504971 942232037354028836448535 := by
  unfold tailWord_5504971
  simp only [CollatzResearch.WordTrace]
  refine ⟨200782787339437716040818767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133855191559625144027212511 200782787339437716040818767)
  ·
    refine ⟨301174181009156574061228151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200782787339437716040818767 301174181009156574061228151)
    ·
      refine ⟨451761271513734861091842227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301174181009156574061228151 451761271513734861091842227)
      ·
        refine ⟨677641907270602291637763341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451761271513734861091842227 677641907270602291637763341)
        ·
          refine ⟨254115715226475859364161253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677641907270602291637763341 254115715226475859364161253)
          ·
            refine ⟨47646696604964223630780235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254115715226475859364161253 47646696604964223630780235)
            ·
              refine ⟨71470044907446335446170353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47646696604964223630780235 71470044907446335446170353)
              ·
                refine ⟨53602533680584751584627765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71470044907446335446170353 53602533680584751584627765)
                ·
                  refine ⟨5025237532554820461058853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53602533680584751584627765 5025237532554820461058853)
                  ·
                    refine ⟨942232037354028836448535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5025237532554820461058853 942232037354028836448535)
                    ·
                      rfl

theorem cell23_5504971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 4].length) (baseStart_5504971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504971 prefixEnd_5504971 := by exact prefixLift 5504971
  have htrace : WordTrace (prefixWord ++ tailWord_5504971) baseStart_5504971 baseEnd_5504971 := by
    simpa [prefixWord, tailWord_5504971, baseEnd_5504971] using wordTrace_append hprefix tailTrace_5504971
  have hstable : (prefixWord ++ tailWord_5504971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504971).length < 2 ^ (prefixWord ++ tailWord_5504971).sum := by decide
  have hdescent : baseEnd_5504971 < baseStart_5504971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505068 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_5505068 : Nat := 118140960795 + 5505068 * 2 ^ 59
def prefixEnd_5505068 : Nat := 4983230072969 + 3 ^ 40 * 5505068 * 2
def baseEnd_5505068 : Nat := 2826745919685572629832659

theorem tailTrace_5505068 : CollatzResearch.WordTrace tailWord_5505068 prefixEnd_5505068 2826745919685572629832659 := by
  unfold tailWord_5505068
  simp only [CollatzResearch.WordTrace]
  refine ⟨100393162610043150803549929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133857550146724201071399905 100393162610043150803549929)
  ·
    refine ⟨75294871957532363102662447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100393162610043150803549929 75294871957532363102662447)
    ·
      refine ⟨112942307936298544653993671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75294871957532363102662447 112942307936298544653993671)
      ·
        refine ⟨169413461904447816980990507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112942307936298544653993671 169413461904447816980990507)
        ·
          refine ⟨254120192856671725471485761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169413461904447816980990507 254120192856671725471485761)
          ·
            refine ⟨190590144642503794103614321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254120192856671725471485761 190590144642503794103614321)
            ·
              refine ⟨142942608481877845577710741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190590144642503794103614321 142942608481877845577710741)
              ·
                refine ⟨6700434772588024011455191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142942608481877845577710741 6700434772588024011455191)
                ·
                  refine ⟨10050652158882036017182787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6700434772588024011455191 10050652158882036017182787)
                  ·
                    refine ⟨15075978238323054025774181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10050652158882036017182787 15075978238323054025774181)
                    ·
                      refine ⟨2826745919685572629832659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15075978238323054025774181 2826745919685572629832659)
                      ·
                        rfl

theorem cell23_5505068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_5505068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505068 prefixEnd_5505068 := by exact prefixLift 5505068
  have htrace : WordTrace (prefixWord ++ tailWord_5505068) baseStart_5505068 baseEnd_5505068 := by
    simpa [prefixWord, tailWord_5505068, baseEnd_5505068] using wordTrace_append hprefix tailTrace_5505068
  have hstable : (prefixWord ++ tailWord_5505068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505068).length < 2 ^ (prefixWord ++ tailWord_5505068).sum := by decide
  have hdescent : baseEnd_5505068 < baseStart_5505068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505088 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_5505088 : Nat := 118140960795 + 5505088 * 2 ^ 59
def prefixEnd_5505088 : Nat := 4983230072969 + 3 ^ 40 * 5505088 * 2
def baseEnd_5505088 : Nat := 2826756189298662551582567

theorem tailTrace_5505088 : CollatzResearch.WordTrace tailWord_5505088 prefixEnd_5505088 2826756189298662551582567 := by
  unfold tailWord_5505088
  simp only [CollatzResearch.WordTrace]
  refine ⟨100393527340006922511413959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133858036453342563348551945 100393527340006922511413959)
  ·
    refine ⟨150590291010010383767120939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100393527340006922511413959 150590291010010383767120939)
    ·
      refine ⟨225885436515015575650681409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150590291010010383767120939 225885436515015575650681409)
      ·
        refine ⟨169414077386261681738011057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225885436515015575650681409 169414077386261681738011057)
        ·
          refine ⟨127060558039696261303508293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169414077386261681738011057 127060558039696261303508293)
          ·
            refine ⟨23823854632443048994407805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127060558039696261303508293 23823854632443048994407805)
            ·
              refine ⟨8933945487166143372902927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23823854632443048994407805 8933945487166143372902927)
              ·
                refine ⟨13400918230749215059354391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8933945487166143372902927 13400918230749215059354391)
                ·
                  refine ⟨20101377346123822589031587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13400918230749215059354391 20101377346123822589031587)
                  ·
                    refine ⟨30152066019185733883547381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20101377346123822589031587 30152066019185733883547381)
                    ·
                      refine ⟨2826756189298662551582567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30152066019185733883547381 2826756189298662551582567)
                      ·
                        rfl

theorem cell23_5505088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_5505088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505088 prefixEnd_5505088 := by exact prefixLift 5505088
  have htrace : WordTrace (prefixWord ++ tailWord_5505088) baseStart_5505088 baseEnd_5505088 := by
    simpa [prefixWord, tailWord_5505088, baseEnd_5505088] using wordTrace_append hprefix tailTrace_5505088
  have hstable : (prefixWord ++ tailWord_5505088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505088).length < 2 ^ (prefixWord ++ tailWord_5505088).sum := by decide
  have hdescent : baseEnd_5505088 < baseStart_5505088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505095 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 2, 4]
def baseStart_5505095 : Nat := 118140960795 + 5505095 * 2 ^ 59
def prefixEnd_5505095 : Nat := 4983230072969 + 3 ^ 40 * 5505095 * 2
def baseEnd_5505095 : Nat := 942253261221081341398345

theorem tailTrace_5505095 : CollatzResearch.WordTrace tailWord_5505095 prefixEnd_5505095 942253261221081341398345 := by
  unfold tailWord_5505095
  simp only [CollatzResearch.WordTrace]
  refine ⟨200787309990988485218332739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133858206660658990145555159 200787309990988485218332739)
  ·
    refine ⟨301180964986482727827499109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200787309990988485218332739 301180964986482727827499109)
    ·
      refine ⟨56471430934965511467656083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301180964986482727827499109 56471430934965511467656083)
      ·
        refine ⟨84707146402448267201484125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56471430934965511467656083 84707146402448267201484125)
        ·
          refine ⟨31765179900918100200556547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84707146402448267201484125 31765179900918100200556547)
          ·
            refine ⟨47647769851377150300834821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31765179900918100200556547 47647769851377150300834821)
            ·
              refine ⟨8933956847133215681406529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47647769851377150300834821 8933956847133215681406529)
              ·
                refine ⟨6700467635349911761054897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8933956847133215681406529 6700467635349911761054897)
                ·
                  refine ⟨5025350726512433820791173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6700467635349911761054897 5025350726512433820791173)
                  ·
                    refine ⟨942253261221081341398345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5025350726512433820791173 942253261221081341398345)
                    ·
                      rfl

theorem cell23_5505095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_5505095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505095 prefixEnd_5505095 := by exact prefixLift 5505095
  have htrace : WordTrace (prefixWord ++ tailWord_5505095) baseStart_5505095 baseEnd_5505095 := by
    simpa [prefixWord, tailWord_5505095, baseEnd_5505095] using wordTrace_append hprefix tailTrace_5505095
  have hstable : (prefixWord ++ tailWord_5505095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505095).length < 2 ^ (prefixWord ++ tailWord_5505095).sum := by decide
  have hdescent : baseEnd_5505095 < baseStart_5505095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505111 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_5505111 : Nat := 118140960795 + 5505111 * 2 ^ 59
def prefixEnd_5505111 : Nat := 4983230072969 + 3 ^ 40 * 5505111 * 2
def baseEnd_5505111 : Nat := 2826767999353715961594961

theorem tailTrace_5505111 : CollatzResearch.WordTrace tailWord_5505111 prefixEnd_5505111 2826767999353715961594961 := by
  unfold tailWord_5505111
  simp only [CollatzResearch.WordTrace]
  refine ⟨200787893558930519950915187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133858595705953679967276791 200787893558930519950915187)
  ·
    refine ⟨301181840338395779926372781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200787893558930519950915187 301181840338395779926372781)
    ·
      refine ⟨112943190126898417472389793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301181840338395779926372781 112943190126898417472389793)
      ·
        refine ⟨84707392595173813104292345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112943190126898417472389793 84707392595173813104292345)
        ·
          refine ⟨63530544446380359828219259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84707392595173813104292345 63530544446380359828219259)
          ·
            refine ⟨95295816669570539742328889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63530544446380359828219259 95295816669570539742328889)
            ·
              refine ⟨71471862502177904806746667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95295816669570539742328889 71471862502177904806746667)
              ·
                refine ⟨107207793753266857210120001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71471862502177904806746667 107207793753266857210120001)
                ·
                  refine ⟨80405845314950142907590001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107207793753266857210120001 80405845314950142907590001)
                  ·
                    refine ⟨60304383986212607180692501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80405845314950142907590001 60304383986212607180692501)
                    ·
                      refine ⟨2826767999353715961594961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60304383986212607180692501 2826767999353715961594961)
                      ·
                        rfl

theorem cell23_5505111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_5505111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505111 prefixEnd_5505111 := by exact prefixLift 5505111
  have htrace : WordTrace (prefixWord ++ tailWord_5505111) baseStart_5505111 baseEnd_5505111 := by
    simpa [prefixWord, tailWord_5505111, baseEnd_5505111] using wordTrace_append hprefix tailTrace_5505111
  have hstable : (prefixWord ++ tailWord_5505111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505111).length < 2 ^ (prefixWord ++ tailWord_5505111).sum := by decide
  have hdescent : baseEnd_5505111 < baseStart_5505111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505121 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_5505121 : Nat := 118140960795 + 5505121 * 2 ^ 59
def prefixEnd_5505121 : Nat := 4983230072969 + 3 ^ 40 * 5505121 * 2
def baseEnd_5505121 : Nat := 942257711386753640823305

theorem tailTrace_5505121 : CollatzResearch.WordTrace tailWord_5505121 prefixEnd_5505121 942257711386753640823305 := by
  unfold tailWord_5505121
  simp only [CollatzResearch.WordTrace]
  refine ⟨200788258288894291658779217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133858838859262861105852811 200788258288894291658779217)
  ·
    refine ⟨150591193716670718744084413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200788258288894291658779217 150591193716670718744084413)
    ·
      refine ⟨56471697643751519529031655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150591193716670718744084413 56471697643751519529031655)
      ·
        refine ⟨84707546465627279293547483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56471697643751519529031655 84707546465627279293547483)
        ·
          refine ⟨127061319698440918940321225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84707546465627279293547483 127061319698440918940321225)
          ·
            refine ⟨95295989773830689205240919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127061319698440918940321225 95295989773830689205240919)
            ·
              refine ⟨142943984660746033807861379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95295989773830689205240919 142943984660746033807861379)
              ·
                refine ⟨214415976991119050711792069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142943984660746033807861379 214415976991119050711792069)
                ·
                  refine ⟨40202995685834822008461013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214415976991119050711792069 40202995685834822008461013)
                  ·
                    refine ⟨942257711386753640823305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40202995685834822008461013 942257711386753640823305)
                    ·
                      rfl

theorem cell23_5505121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_5505121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505121 prefixEnd_5505121 := by exact prefixLift 5505121
  have htrace : WordTrace (prefixWord ++ tailWord_5505121) baseStart_5505121 baseEnd_5505121 := by
    simpa [prefixWord, tailWord_5505121, baseEnd_5505121] using wordTrace_append hprefix tailTrace_5505121
  have hstable : (prefixWord ++ tailWord_5505121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505121).length < 2 ^ (prefixWord ++ tailWord_5505121).sum := by decide
  have hdescent : baseEnd_5505121 < baseStart_5505121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505255 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5505255 : Nat := 118140960795 + 5505255 * 2 ^ 59
def prefixEnd_5505255 : Nat := 4983230072969 + 3 ^ 40 * 5505255 * 2
def baseEnd_5505255 : Nat := 2826841940567963398194299

theorem tailTrace_5505255 : CollatzResearch.WordTrace tailWord_5505255 prefixEnd_5505255 2826841940567963398194299 := by
  unfold tailWord_5505255
  simp only [CollatzResearch.WordTrace]
  refine ⟨200793145670408832544157219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133862097113605888362771479 200793145670408832544157219)
  ·
    refine ⟨301189718505613248816235829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200793145670408832544157219 301189718505613248816235829)
    ·
      refine ⟨28236536109901242076522109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301189718505613248816235829 28236536109901242076522109)
      ·
        refine ⟨10588701041212965778695791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28236536109901242076522109 10588701041212965778695791)
        ·
          refine ⟨15883051561819448668043687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10588701041212965778695791 15883051561819448668043687)
          ·
            refine ⟨23824577342729173002065531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15883051561819448668043687 23824577342729173002065531)
            ·
              refine ⟨35736866014093759503098297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23824577342729173002065531 35736866014093759503098297)
              ·
                refine ⟨26802649510570319627323723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35736866014093759503098297 26802649510570319627323723)
                ·
                  refine ⟨40203974265855479440985585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26802649510570319627323723 40203974265855479440985585)
                  ·
                    refine ⟨30152980699391609580739189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40203974265855479440985585 30152980699391609580739189)
                    ·
                      refine ⟨2826841940567963398194299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30152980699391609580739189 2826841940567963398194299)
                      ·
                        rfl

theorem cell23_5505255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5505255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505255 prefixEnd_5505255 := by exact prefixLift 5505255
  have htrace : WordTrace (prefixWord ++ tailWord_5505255) baseStart_5505255 baseEnd_5505255 := by
    simpa [prefixWord, tailWord_5505255, baseEnd_5505255] using wordTrace_append hprefix tailTrace_5505255
  have hstable : (prefixWord ++ tailWord_5505255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505255).length < 2 ^ (prefixWord ++ tailWord_5505255).sum := by decide
  have hdescent : baseEnd_5505255 < baseStart_5505255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505265 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_5505265 : Nat := 118140960795 + 5505265 * 2 ^ 59
def prefixEnd_5505265 : Nat := 4983230072969 + 3 ^ 40 * 5505265 * 2
def baseEnd_5505265 : Nat := 2826847075374508359069253

theorem tailTrace_5505265 : CollatzResearch.WordTrace tailWord_5505265 prefixEnd_5505265 2826847075374508359069253 := by
  unfold tailWord_5505265
  simp only [CollatzResearch.WordTrace]
  refine ⟨200793510400372604252021249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133862340266915069501347499 200793510400372604252021249)
  ·
    refine ⟨150595132800279453189015937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200793510400372604252021249 150595132800279453189015937)
    ·
      refine ⟨112946349600209589891761953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150595132800279453189015937 112946349600209589891761953)
      ·
        refine ⟨84709762200157192418821465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112946349600209589891761953 84709762200157192418821465)
        ·
          refine ⟨63532321650117894314116099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84709762200157192418821465 63532321650117894314116099)
          ·
            refine ⟨95298482475176841471174149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63532321650117894314116099 95298482475176841471174149)
            ·
              refine ⟨17868465464095657775845153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95298482475176841471174149 17868465464095657775845153)
              ·
                refine ⟨13401349098071743331883865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17868465464095657775845153 13401349098071743331883865)
                ·
                  refine ⟨10051011823553807498912899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13401349098071743331883865 10051011823553807498912899)
                  ·
                    refine ⟨15076517735330711248369349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10051011823553807498912899 15076517735330711248369349)
                    ·
                      refine ⟨2826847075374508359069253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15076517735330711248369349 2826847075374508359069253)
                      ·
                        rfl

theorem cell23_5505265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_5505265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505265 prefixEnd_5505265 := by exact prefixLift 5505265
  have htrace : WordTrace (prefixWord ++ tailWord_5505265) baseStart_5505265 baseEnd_5505265 := by
    simpa [prefixWord, tailWord_5505265, baseEnd_5505265] using wordTrace_append hprefix tailTrace_5505265
  have hstable : (prefixWord ++ tailWord_5505265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505265).length < 2 ^ (prefixWord ++ tailWord_5505265).sum := by decide
  have hdescent : baseEnd_5505265 < baseStart_5505265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505322 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_5505322 : Nat := 118140960795 + 5505322 * 2 ^ 59
def prefixEnd_5505322 : Nat := 4983230072969 + 3 ^ 40 * 5505322 * 2
def baseEnd_5505322 : Nat := 314097371530201626228499

theorem tailTrace_5505322 : CollatzResearch.WordTrace tailWord_5505322 prefixEnd_5505322 314097371530201626228499 := by
  unfold tailWord_5505322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50198897340291525746711555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133863726240777401991230813 50198897340291525746711555)
  ·
    refine ⟨75298346010437288620067333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50198897340291525746711555 75298346010437288620067333)
    ·
      refine ⟨14118439876956991616262625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75298346010437288620067333 14118439876956991616262625)
      ·
        refine ⟨10588829907717743712196969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14118439876956991616262625 10588829907717743712196969)
        ·
          refine ⟨7941622430788307784147727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10588829907717743712196969 7941622430788307784147727)
          ·
            refine ⟨11912433646182461676221591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941622430788307784147727 11912433646182461676221591)
            ·
              refine ⟨17868650469273692514332387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11912433646182461676221591 17868650469273692514332387)
              ·
                refine ⟨26802975703910538771498581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17868650469273692514332387 26802975703910538771498581)
                ·
                  refine ⟨314097371530201626228499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26802975703910538771498581 314097371530201626228499)
                  ·
                    rfl

theorem cell23_5505322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_5505322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505322 prefixEnd_5505322 := by exact prefixLift 5505322
  have htrace : WordTrace (prefixWord ++ tailWord_5505322) baseStart_5505322 baseEnd_5505322 := by
    simpa [prefixWord, tailWord_5505322, baseEnd_5505322] using wordTrace_append hprefix tailTrace_5505322
  have hstable : (prefixWord ++ tailWord_5505322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505322).length < 2 ^ (prefixWord ++ tailWord_5505322).sum := by decide
  have hdescent : baseEnd_5505322 < baseStart_5505322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505326 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_5505326 : Nat := 118140960795 + 5505326 * 2 ^ 59
def prefixEnd_5505326 : Nat := 4983230072969 + 3 ^ 40 * 5505326 * 2
def baseEnd_5505326 : Nat := 942292799231477540135491

theorem tailTrace_5505326 : CollatzResearch.WordTrace tailWord_5505326 prefixEnd_5505326 942292799231477540135491 := by
  unfold tailWord_5505326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25099466906643951458748979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133863823502101074446661221 25099466906643951458748979)
  ·
    refine ⟨37649200359965927188123469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25099466906643951458748979 37649200359965927188123469)
    ·
      refine ⟨14118450134987222695546301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37649200359965927188123469 14118450134987222695546301)
      ·
        refine ⟨5294418800620208510829863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14118450134987222695546301 5294418800620208510829863)
        ·
          refine ⟨7941628200930312766244795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294418800620208510829863 7941628200930312766244795)
          ·
            refine ⟨11912442301395469149367193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941628200930312766244795 11912442301395469149367193)
            ·
              refine ⟨8934331726046601862025395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11912442301395469149367193 8934331726046601862025395)
              ·
                refine ⟨13401497589069902793038093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8934331726046601862025395 13401497589069902793038093)
                ·
                  refine ⟨5025561595901213547389285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13401497589069902793038093 5025561595901213547389285)
                  ·
                    refine ⟨942292799231477540135491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5025561595901213547389285 942292799231477540135491)
                    ·
                      rfl

theorem cell23_5505326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_5505326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505326 prefixEnd_5505326 := by exact prefixLift 5505326
  have htrace : WordTrace (prefixWord ++ tailWord_5505326) baseStart_5505326 baseEnd_5505326 := by
    simpa [prefixWord, tailWord_5505326, baseEnd_5505326] using wordTrace_append hprefix tailTrace_5505326
  have hstable : (prefixWord ++ tailWord_5505326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505326).length < 2 ^ (prefixWord ++ tailWord_5505326).sum := by decide
  have hdescent : baseEnd_5505326 < baseStart_5505326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505328 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_5505328 : Nat := 118140960795 + 5505328 * 2 ^ 59
def prefixEnd_5505328 : Nat := 4983230072969 + 3 ^ 40 * 5505328 * 2
def baseEnd_5505328 : Nat := 2826879424655741612581463

theorem tailTrace_5505328 : CollatzResearch.WordTrace tailWord_5505328 prefixEnd_5505328 2826879424655741612581463 := by
  unfold tailWord_5505328
  simp only [CollatzResearch.WordTrace]
  refine ⟨100397904099572183005782319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133863872132762910674376425 100397904099572183005782319)
  ·
    refine ⟨150596856149358274508673479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100397904099572183005782319 150596856149358274508673479)
    ·
      refine ⟨225895284224037411763010219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150596856149358274508673479 225895284224037411763010219)
      ·
        refine ⟨338842926336056117644515329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225895284224037411763010219 338842926336056117644515329)
        ·
          refine ⟨254132194752042088233386497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338842926336056117644515329 254132194752042088233386497)
          ·
            refine ⟨190599146064031566175039873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254132194752042088233386497 190599146064031566175039873)
            ·
              refine ⟨142949359548023674631279905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190599146064031566175039873 142949359548023674631279905)
              ·
                refine ⟨107212019661017755973459929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142949359548023674631279905 107212019661017755973459929)
                ·
                  refine ⟨80409014745763316980094947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107212019661017755973459929 80409014745763316980094947)
                  ·
                    refine ⟨120613522118644975470142421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80409014745763316980094947 120613522118644975470142421)
                    ·
                      refine ⟨2826879424655741612581463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120613522118644975470142421 2826879424655741612581463)
                      ·
                        rfl

theorem cell23_5505328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_5505328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505328 prefixEnd_5505328 := by exact prefixLift 5505328
  have htrace : WordTrace (prefixWord ++ tailWord_5505328) baseStart_5505328 baseEnd_5505328 := by
    simpa [prefixWord, tailWord_5505328, baseEnd_5505328] using wordTrace_append hprefix tailTrace_5505328
  have hstable : (prefixWord ++ tailWord_5505328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505328).length < 2 ^ (prefixWord ++ tailWord_5505328).sum := by decide
  have hdescent : baseEnd_5505328 < baseStart_5505328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505375 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_5505375 : Nat := 118140960795 + 5505375 * 2 ^ 59
def prefixEnd_5505375 : Nat := 4983230072969 + 3 ^ 40 * 5505375 * 2
def baseEnd_5505375 : Nat := 2826903558246502928693747

theorem tailTrace_5505375 : CollatzResearch.WordTrace tailWord_5505375 prefixEnd_5505375 2826903558246502928693747 := by
  unfold tailWord_5505375
  simp only [CollatzResearch.WordTrace]
  refine ⟨200797522429974093038525579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133865014953316062025683719 200797522429974093038525579)
  ·
    refine ⟨301196283644961139557788369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200797522429974093038525579 301196283644961139557788369)
    ·
      refine ⟨225897212733720854668341277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301196283644961139557788369 225897212733720854668341277)
      ·
        refine ⟨84711454775145320500627979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225897212733720854668341277 84711454775145320500627979)
        ·
          refine ⟨127067182162717980750941969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84711454775145320500627979 127067182162717980750941969)
          ·
            refine ⟨95300386622038485563206477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127067182162717980750941969 95300386622038485563206477)
            ·
              refine ⟨35737644983264432086202429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95300386622038485563206477 35737644983264432086202429)
              ·
                refine ⟨13401616868724162032325911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35737644983264432086202429 13401616868724162032325911)
                ·
                  refine ⟨20102425303086243048488867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13401616868724162032325911 20102425303086243048488867)
                  ·
                    refine ⟨30153637954629364572733301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20102425303086243048488867 30153637954629364572733301)
                    ·
                      refine ⟨2826903558246502928693747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30153637954629364572733301 2826903558246502928693747)
                      ·
                        rfl

theorem cell23_5505375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_5505375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505375 prefixEnd_5505375 := by exact prefixLift 5505375
  have htrace : WordTrace (prefixWord ++ tailWord_5505375) baseStart_5505375 baseEnd_5505375 := by
    simpa [prefixWord, tailWord_5505375, baseEnd_5505375] using wordTrace_append hprefix tailTrace_5505375
  have hstable : (prefixWord ++ tailWord_5505375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505375).length < 2 ^ (prefixWord ++ tailWord_5505375).sum := by decide
  have hdescent : baseEnd_5505375 < baseStart_5505375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505383 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_5505383 : Nat := 118140960795 + 5505383 * 2 ^ 59
def prefixEnd_5505383 : Nat := 4983230072969 + 3 ^ 40 * 5505383 * 2
def baseEnd_5505383 : Nat := 2826907666091738897393711

theorem tailTrace_5505383 : CollatzResearch.WordTrace tailWord_5505383 prefixEnd_5505383 2826907666091738897393711 := by
  unfold tailWord_5505383
  simp only [CollatzResearch.WordTrace]
  refine ⟨200797814213945110404816803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133865209475963406936544535 200797814213945110404816803)
  ·
    refine ⟨301196721320917665607225205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200797814213945110404816803 301196721320917665607225205)
    ·
      refine ⟨28237192623836031150677363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301196721320917665607225205 28237192623836031150677363)
      ·
        refine ⟨42355788935754046726016045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28237192623836031150677363 42355788935754046726016045)
        ·
          refine ⟨15883420850907767522256017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42355788935754046726016045 15883420850907767522256017)
          ·
            refine ⟨11912565638180825641692013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15883420850907767522256017 11912565638180825641692013)
            ·
              refine ⟨4467212114317809615634505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11912565638180825641692013 4467212114317809615634505)
              ·
                refine ⟨3350409085738357211725879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467212114317809615634505 3350409085738357211725879)
                ·
                  refine ⟨5025613628607535817588819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350409085738357211725879 5025613628607535817588819)
                  ·
                    refine ⟨7538420442911303726383229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5025613628607535817588819 7538420442911303726383229)
                    ·
                      refine ⟨2826907666091738897393711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7538420442911303726383229 2826907666091738897393711)
                      ·
                        rfl

theorem cell23_5505383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_5505383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505383 prefixEnd_5505383 := by exact prefixLift 5505383
  have htrace : WordTrace (prefixWord ++ tailWord_5505383) baseStart_5505383 baseEnd_5505383 := by
    simpa [prefixWord, tailWord_5505383, baseEnd_5505383] using wordTrace_append hprefix tailTrace_5505383
  have hstable : (prefixWord ++ tailWord_5505383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505383).length < 2 ^ (prefixWord ++ tailWord_5505383).sum := by decide
  have hdescent : baseEnd_5505383 < baseStart_5505383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505409 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_5505409 : Nat := 118140960795 + 5505409 * 2 ^ 59
def prefixEnd_5505409 : Nat := 4983230072969 + 3 ^ 40 * 5505409 * 2
def baseEnd_5505409 : Nat := 2826921016588755795668591

theorem tailTrace_5505409 : CollatzResearch.WordTrace tailWord_5505409 prefixEnd_5505409 2826921016588755795668591 := by
  unfold tailWord_5505409
  simp only [CollatzResearch.WordTrace]
  refine ⟨200798762511850916845263281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133865841674567277896842187 200798762511850916845263281)
  ·
    refine ⟨150599071883888187633947461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200798762511850916845263281 150599071883888187633947461)
    ·
      refine ⟨28237325978229035181365149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150599071883888187633947461 28237325978229035181365149)
      ·
        refine ⟨10588997241835888193011931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28237325978229035181365149 10588997241835888193011931)
        ·
          refine ⟨15883495862753832289517897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10588997241835888193011931 15883495862753832289517897)
          ·
            refine ⟨11912621897065374217138423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15883495862753832289517897 11912621897065374217138423)
            ·
              refine ⟨17868932845598061325707635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11912621897065374217138423 17868932845598061325707635)
              ·
                refine ⟨26803399268397091988561453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17868932845598061325707635 26803399268397091988561453)
                ·
                  refine ⟨10051274725648909495710545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26803399268397091988561453 10051274725648909495710545)
                  ·
                    refine ⟨7538456044236682121782909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10051274725648909495710545 7538456044236682121782909)
                    ·
                      refine ⟨2826921016588755795668591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7538456044236682121782909 2826921016588755795668591)
                      ·
                        rfl

theorem cell23_5505409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_5505409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505409 prefixEnd_5505409 := by exact prefixLift 5505409
  have htrace : WordTrace (prefixWord ++ tailWord_5505409) baseStart_5505409 baseEnd_5505409 := by
    simpa [prefixWord, tailWord_5505409, baseEnd_5505409] using wordTrace_append hprefix tailTrace_5505409
  have hstable : (prefixWord ++ tailWord_5505409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505409).length < 2 ^ (prefixWord ++ tailWord_5505409).sum := by decide
  have hdescent : baseEnd_5505409 < baseStart_5505409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505440 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 1, 2, 2]
def baseStart_5505440 : Nat := 118140960795 + 5505440 * 2 ^ 59
def prefixEnd_5505440 : Nat := 4983230072969 + 3 ^ 40 * 5505440 * 2
def baseEnd_5505440 : Nat := 2826936934489045174380949

theorem tailTrace_5505440 : CollatzResearch.WordTrace tailWord_5505440 prefixEnd_5505440 2826936934489045174380949 := by
  unfold tailWord_5505440
  simp only [CollatzResearch.WordTrace]
  refine ⟨100399946587369304569820887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133866595449825739426427849 100399946587369304569820887)
  ·
    refine ⟨150599919881053956854731331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100399946587369304569820887 150599919881053956854731331)
    ·
      refine ⟨225899879821580935282096997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150599919881053956854731331 225899879821580935282096997)
      ·
        refine ⟨42356227466546425365393187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225899879821580935282096997 42356227466546425365393187)
        ·
          refine ⟨63534341199819638048089781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42356227466546425365393187 63534341199819638048089781)
          ·
            refine ⟨5956344487483091067008417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63534341199819638048089781 5956344487483091067008417)
            ·
              refine ⟨4467258365612318300256313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956344487483091067008417 4467258365612318300256313)
              ·
                refine ⟨3350443774209238725192235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467258365612318300256313 3350443774209238725192235)
                ·
                  refine ⟨5025665661313858087788353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350443774209238725192235 5025665661313858087788353)
                  ·
                    refine ⟨3769249245985393565841265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5025665661313858087788353 3769249245985393565841265)
                    ·
                      refine ⟨2826936934489045174380949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769249245985393565841265 2826936934489045174380949)
                      ·
                        rfl

theorem cell23_5505440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_5505440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505440 prefixEnd_5505440 := by exact prefixLift 5505440
  have htrace : WordTrace (prefixWord ++ tailWord_5505440) baseStart_5505440 baseEnd_5505440 := by
    simpa [prefixWord, tailWord_5505440, baseEnd_5505440] using wordTrace_append hprefix tailTrace_5505440
  have hstable : (prefixWord ++ tailWord_5505440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505440).length < 2 ^ (prefixWord ++ tailWord_5505440).sum := by decide
  have hdescent : baseEnd_5505440 < baseStart_5505440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505445 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_5505445 : Nat := 118140960795 + 5505445 * 2 ^ 59
def prefixEnd_5505445 : Nat := 4983230072969 + 3 ^ 40 * 5505445 * 2
def baseEnd_5505445 : Nat := 2826939501892317654818425

theorem tailTrace_5505445 : CollatzResearch.WordTrace tailWord_5505445 prefixEnd_5505445 2826939501892317654818425 := by
  unfold tailWord_5505445
  simp only [CollatzResearch.WordTrace]
  refine ⟨200800075539720494993573789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133866717026480329995715859 200800075539720494993573789)
  ·
    refine ⟨75300028327395185622590171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200800075539720494993573789 75300028327395185622590171)
    ·
      refine ⟨112950042491092778433885257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75300028327395185622590171 112950042491092778433885257)
      ·
        refine ⟨84712531868319583825413943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112950042491092778433885257 84712531868319583825413943)
        ·
          refine ⟨127068797802479375738120915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84712531868319583825413943 127068797802479375738120915)
          ·
            refine ⟨190603196703719063607181373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127068797802479375738120915 190603196703719063607181373)
            ·
              refine ⟨71476198763894648852693015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190603196703719063607181373 71476198763894648852693015)
              ·
                refine ⟨107214298145841973279039523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71476198763894648852693015 107214298145841973279039523)
                ·
                  refine ⟨160821447218762959918559285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107214298145841973279039523 160821447218762959918559285)
                  ·
                    refine ⟨15077010676759027492364933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160821447218762959918559285 15077010676759027492364933)
                    ·
                      refine ⟨2826939501892317654818425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15077010676759027492364933 2826939501892317654818425)
                      ·
                        rfl

theorem cell23_5505445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_5505445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505445 prefixEnd_5505445 := by exact prefixLift 5505445
  have htrace : WordTrace (prefixWord ++ tailWord_5505445) baseStart_5505445 baseEnd_5505445 := by
    simpa [prefixWord, tailWord_5505445, baseEnd_5505445] using wordTrace_append hprefix tailTrace_5505445
  have hstable : (prefixWord ++ tailWord_5505445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505445).length < 2 ^ (prefixWord ++ tailWord_5505445).sum := by decide
  have hdescent : baseEnd_5505445 < baseStart_5505445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505475 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_5505475 : Nat := 118140960795 + 5505475 * 2 ^ 59
def prefixEnd_5505475 : Nat := 4983230072969 + 3 ^ 40 * 5505475 * 2
def baseEnd_5505475 : Nat := 2826954906311952537443287

theorem tailTrace_5505475 : CollatzResearch.WordTrace tailWord_5505475 prefixEnd_5505475 2826954906311952537443287 := by
  unfold tailWord_5505475
  simp only [CollatzResearch.WordTrace]
  refine ⟨200801169729611810117165879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133867446486407873411443919 200801169729611810117165879)
  ·
    refine ⟨301201754594417715175748819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200801169729611810117165879 301201754594417715175748819)
    ·
      refine ⟨451802631891626572763623229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301201754594417715175748819 451802631891626572763623229)
      ·
        refine ⟨169425986959359964786358711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451802631891626572763623229 169425986959359964786358711)
        ·
          refine ⟨254138980439039947179538067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169425986959359964786358711 254138980439039947179538067)
          ·
            refine ⟨381208470658559920769307101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254138980439039947179538067 381208470658559920769307101)
            ·
              refine ⟨142953176496959970288490163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381208470658559920769307101 142953176496959970288490163)
              ·
                refine ⟨214429764745439955432735245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142953176496959970288490163 214429764745439955432735245)
                ·
                  refine ⟨80411161779539983287275717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214429764745439955432735245 80411161779539983287275717)
                  ·
                    refine ⟨15077092833663746866364197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80411161779539983287275717 15077092833663746866364197)
                    ·
                      refine ⟨2826954906311952537443287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15077092833663746866364197 2826954906311952537443287)
                      ·
                        rfl

theorem cell23_5505475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_5505475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505475 prefixEnd_5505475 := by exact prefixLift 5505475
  have htrace : WordTrace (prefixWord ++ tailWord_5505475) baseStart_5505475 baseEnd_5505475 := by
    simpa [prefixWord, tailWord_5505475, baseEnd_5505475] using wordTrace_append hprefix tailTrace_5505475
  have hstable : (prefixWord ++ tailWord_5505475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505475).length < 2 ^ (prefixWord ++ tailWord_5505475).sum := by decide
  have hdescent : baseEnd_5505475 < baseStart_5505475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505479 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_5505479 : Nat := 118140960795 + 5505479 * 2 ^ 59
def prefixEnd_5505479 : Nat := 4983230072969 + 3 ^ 40 * 5505479 * 2
def baseEnd_5505479 : Nat := 2826956960234570521793269

theorem tailTrace_5505479 : CollatzResearch.WordTrace tailWord_5505479 prefixEnd_5505479 2826956960234570521793269 := by
  unfold tailWord_5505479
  simp only [CollatzResearch.WordTrace]
  refine ⟨200801315621597318800311491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133867543747731545866874327 200801315621597318800311491)
  ·
    refine ⟨301201973432395978200467237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200801315621597318800311491 301201973432395978200467237)
    ·
      refine ⟨56475370018574245912587607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301201973432395978200467237 56475370018574245912587607)
      ·
        refine ⟨84713055027861368868881411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56475370018574245912587607 84713055027861368868881411)
        ·
          refine ⟨127069582541792053303322117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84713055027861368868881411 127069582541792053303322117)
          ·
            refine ⟨23825546726586009994372897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127069582541792053303322117 23825546726586009994372897)
            ·
              refine ⟨17869160044939507495779673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23825546726586009994372897 17869160044939507495779673)
              ·
                refine ⟨13401870033704630621834755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17869160044939507495779673 13401870033704630621834755)
                ·
                  refine ⟨20102805050556945932752133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13401870033704630621834755 20102805050556945932752133)
                  ·
                    refine ⟨3769275946979427362391025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20102805050556945932752133 3769275946979427362391025)
                    ·
                      refine ⟨2826956960234570521793269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769275946979427362391025 2826956960234570521793269)
                      ·
                        rfl

theorem cell23_5505479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_5505479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505479 prefixEnd_5505479 := by exact prefixLift 5505479
  have htrace : WordTrace (prefixWord ++ tailWord_5505479) baseStart_5505479 baseEnd_5505479 := by
    simpa [prefixWord, tailWord_5505479, baseEnd_5505479] using wordTrace_append hprefix tailTrace_5505479
  have hstable : (prefixWord ++ tailWord_5505479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505479).length < 2 ^ (prefixWord ++ tailWord_5505479).sum := by decide
  have hdescent : baseEnd_5505479 < baseStart_5505479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505490 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5505490 : Nat := 118140960795 + 5505490 * 2 ^ 59
def prefixEnd_5505490 : Nat := 4983230072969 + 3 ^ 40 * 5505490 * 2
def baseEnd_5505490 : Nat := 2826962608521769978755719

theorem tailTrace_5505490 : CollatzResearch.WordTrace tailWord_5505490 prefixEnd_5505490 2826962608521769978755719 := by
  unfold tailWord_5505490
  simp only [CollatzResearch.WordTrace]
  refine ⟨50200429206139366919740481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133867811216371645119307949 50200429206139366919740481)
  ·
    refine ⟨37650321904604525189805361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50200429206139366919740481 37650321904604525189805361)
    ·
      refine ⟨28237741428453393892354021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37650321904604525189805361 28237741428453393892354021)
      ·
        refine ⟨5294576517835011354816379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28237741428453393892354021 5294576517835011354816379)
        ·
          refine ⟨7941864776752517032224569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294576517835011354816379 7941864776752517032224569)
          ·
            refine ⟨5956398582564387774168427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7941864776752517032224569 5956398582564387774168427)
            ·
              refine ⟨8934597873846581661252641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956398582564387774168427 8934597873846581661252641)
              ·
                refine ⟨6700948405384936245939481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8934597873846581661252641 6700948405384936245939481)
                ·
                  refine ⟨5025711304038702184454611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6700948405384936245939481 5025711304038702184454611)
                  ·
                    refine ⟨7538566956058053276681917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5025711304038702184454611 7538566956058053276681917)
                    ·
                      refine ⟨2826962608521769978755719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7538566956058053276681917 2826962608521769978755719)
                      ·
                        rfl

theorem cell23_5505490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5505490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505490 prefixEnd_5505490 := by exact prefixLift 5505490
  have htrace : WordTrace (prefixWord ++ tailWord_5505490) baseStart_5505490 baseEnd_5505490 := by
    simpa [prefixWord, tailWord_5505490, baseEnd_5505490] using wordTrace_append hprefix tailTrace_5505490
  have hstable : (prefixWord ++ tailWord_5505490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505490).length < 2 ^ (prefixWord ++ tailWord_5505490).sum := by decide
  have hdescent : baseEnd_5505490 < baseStart_5505490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505515 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 7]
def baseStart_5505515 : Nat := 118140960795 + 5505515 * 2 ^ 59
def prefixEnd_5505515 : Nat := 4983230072969 + 3 ^ 40 * 5505515 * 2
def baseEnd_5505515 : Nat := 942325148512710793647701

theorem tailTrace_5505515 : CollatzResearch.WordTrace tailWord_5505515 prefixEnd_5505515 942325148512710793647701 := by
  unfold tailWord_5505515
  simp only [CollatzResearch.WordTrace]
  refine ⟨200802628649466896948621999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133868419099644597965747999 200802628649466896948621999)
  ·
    refine ⟨301203942974200345422932999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200802628649466896948621999 301203942974200345422932999)
    ·
      refine ⟨451805914461300518134399499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301203942974200345422932999 451805914461300518134399499)
      ·
        refine ⟨677708871691950777201599249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451805914461300518134399499 677708871691950777201599249)
        ·
          refine ⟨508281653768963082901199437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677708871691950777201599249 508281653768963082901199437)
          ·
            refine ⟨190605620163361156087949789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 508281653768963082901199437 190605620163361156087949789)
            ·
              refine ⟨71477107561260433532981171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190605620163361156087949789 71477107561260433532981171)
              ·
                refine ⟨107215661341890650299471757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71477107561260433532981171 107215661341890650299471757)
                ·
                  refine ⟨40205873003208993862301909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107215661341890650299471757 40205873003208993862301909)
                  ·
                    refine ⟨942325148512710793647701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40205873003208993862301909 942325148512710793647701)
                    ·
                      rfl

theorem cell23_5505515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_5505515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505515 prefixEnd_5505515 := by exact prefixLift 5505515
  have htrace : WordTrace (prefixWord ++ tailWord_5505515) baseStart_5505515 baseEnd_5505515 := by
    simpa [prefixWord, tailWord_5505515, baseEnd_5505515] using wordTrace_append hprefix tailTrace_5505515
  have hstable : (prefixWord ++ tailWord_5505515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505515).length < 2 ^ (prefixWord ++ tailWord_5505515).sum := by decide
  have hdescent : baseEnd_5505515 < baseStart_5505515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505532 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_5505532 : Nat := 118140960795 + 5505532 * 2 ^ 59
def prefixEnd_5505532 : Nat := 4983230072969 + 3 ^ 40 * 5505532 * 2
def baseEnd_5505532 : Nat := 942328058236419604810175

theorem tailTrace_5505532 : CollatzResearch.WordTrace tailWord_5505532 prefixEnd_5505532 942328058236419604810175 := by
  unfold tailWord_5505532
  simp only [CollatzResearch.WordTrace]
  refine ⟨100401624345202654425995425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133868832460270205901327233 100401624345202654425995425)
  ·
    refine ⟨75301218258901990819496569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100401624345202654425995425 75301218258901990819496569)
    ·
      refine ⟨56475913694176493114622427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75301218258901990819496569 56475913694176493114622427)
      ·
        refine ⟨84713870541264739671933641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56475913694176493114622427 84713870541264739671933641)
        ·
          refine ⟨63535402905948554753950231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84713870541264739671933641 63535402905948554753950231)
          ·
            refine ⟨95303104358922832130925347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63535402905948554753950231 95303104358922832130925347)
            ·
              refine ⟨142954656538384248196388021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95303104358922832130925347 142954656538384248196388021)
              ·
                refine ⟨13401999050473523268411377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142954656538384248196388021 13401999050473523268411377)
                ·
                  refine ⟨10051499287855142451308533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13401999050473523268411377 10051499287855142451308533)
                  ·
                    refine ⟨942328058236419604810175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10051499287855142451308533 942328058236419604810175)
                    ·
                      rfl

theorem cell23_5505532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_5505532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505532 prefixEnd_5505532 := by exact prefixLift 5505532
  have htrace : WordTrace (prefixWord ++ tailWord_5505532) baseStart_5505532 baseEnd_5505532 := by
    simpa [prefixWord, tailWord_5505532, baseEnd_5505532] using wordTrace_append hprefix tailTrace_5505532
  have hstable : (prefixWord ++ tailWord_5505532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505532).length < 2 ^ (prefixWord ++ tailWord_5505532).sum := by decide
  have hdescent : baseEnd_5505532 < baseStart_5505532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505569 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5505569 : Nat := 118140960795 + 5505569 * 2 ^ 59
def prefixEnd_5505569 : Nat := 4983230072969 + 3 ^ 40 * 5505569 * 2
def baseEnd_5505569 : Nat := 2827003173493475169667855

theorem tailTrace_5505569 : CollatzResearch.WordTrace tailWord_5505569 prefixEnd_5505569 2827003173493475169667855 := by
  unfold tailWord_5505569
  simp only [CollatzResearch.WordTrace]
  refine ⟨200804598191271264171087761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133869732127514176114058507 200804598191271264171087761)
  ·
    refine ⟨150603448643453448128315821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200804598191271264171087761 150603448643453448128315821)
    ·
      refine ⟨56476293241295043048118433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150603448643453448128315821 56476293241295043048118433)
      ·
        refine ⟨42357219930971282286088825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56476293241295043048118433 42357219930971282286088825)
        ·
          refine ⟨31767914948228461714566619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42357219930971282286088825 31767914948228461714566619)
          ·
            refine ⟨47651872422342692571849929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31767914948228461714566619 47651872422342692571849929)
            ·
              refine ⟨35738904316757019428887447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47651872422342692571849929 35738904316757019428887447)
              ·
                refine ⟨53608356475135529143331171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35738904316757019428887447 53608356475135529143331171)
                ·
                  refine ⟨80412534712703293714996757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53608356475135529143331171 80412534712703293714996757)
                  ·
                    refine ⟨3769337564657966892890473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80412534712703293714996757 3769337564657966892890473)
                    ·
                      refine ⟨2827003173493475169667855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769337564657966892890473 2827003173493475169667855)
                      ·
                        rfl

theorem cell23_5505569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5505569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505569 prefixEnd_5505569 := by exact prefixLift 5505569
  have htrace : WordTrace (prefixWord ++ tailWord_5505569) baseStart_5505569 baseEnd_5505569 := by
    simpa [prefixWord, tailWord_5505569, baseEnd_5505569] using wordTrace_append hprefix tailTrace_5505569
  have hstable : (prefixWord ++ tailWord_5505569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505569).length < 2 ^ (prefixWord ++ tailWord_5505569).sum := by decide
  have hdescent : baseEnd_5505569 < baseStart_5505569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505604 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 5]
def baseStart_5505604 : Nat := 118140960795 + 5505604 * 2 ^ 59
def prefixEnd_5505604 : Nat := 4983230072969 + 3 ^ 40 * 5505604 * 2
def baseEnd_5505604 : Nat := 314113460590709170303355

theorem tailTrace_5505604 : CollatzResearch.WordTrace tailWord_5505604 prefixEnd_5505604 314113460590709170303355 := by
  unfold tailWord_5505604
  simp only [CollatzResearch.WordTrace]
  refine ⟨100402937373072232574305933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133870583164096310099074577 100402937373072232574305933)
  ·
    refine ⟨37651101514902087215364725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100402937373072232574305933 37651101514902087215364725)
    ·
      refine ⟨3529790767022070676440443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37651101514902087215364725 3529790767022070676440443)
      ·
        refine ⟨5294686150533106014660665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529790767022070676440443 5294686150533106014660665)
        ·
          refine ⟨3971014612899829510995499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5294686150533106014660665 3971014612899829510995499)
          ·
            refine ⟨5956521919349744266493249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971014612899829510995499 5956521919349744266493249)
            ·
              refine ⟨4467391439512308199869937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956521919349744266493249 4467391439512308199869937)
              ·
                refine ⟨3350543579634231149902453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467391439512308199869937 3350543579634231149902453)
                ·
                  refine ⟨314113460590709170303355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3350543579634231149902453 314113460590709170303355)
                  ·
                    rfl

theorem cell23_5505604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_5505604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505604 prefixEnd_5505604 := by exact prefixLift 5505604
  have htrace : WordTrace (prefixWord ++ tailWord_5505604) baseStart_5505604 baseEnd_5505604 := by
    simpa [prefixWord, tailWord_5505604, baseEnd_5505604] using wordTrace_append hprefix tailTrace_5505604
  have hstable : (prefixWord ++ tailWord_5505604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505604).length < 2 ^ (prefixWord ++ tailWord_5505604).sum := by decide
  have hdescent : baseEnd_5505604 < baseStart_5505604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505612 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5505612 : Nat := 118140960795 + 5505612 * 2 ^ 59
def prefixEnd_5505612 : Nat := 4983230072969 + 3 ^ 40 * 5505612 * 2
def baseEnd_5505612 : Nat := 2827025253161618501430157

theorem tailTrace_5505612 : CollatzResearch.WordTrace tailWord_5505612 prefixEnd_5505612 2827025253161618501430157 := by
  unfold tailWord_5505612
  simp only [CollatzResearch.WordTrace]
  refine ⟨100403083265057741257451545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133870777686743655009935393 100403083265057741257451545)
  ·
    refine ⟨75302312448793305943088659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100403083265057741257451545 75302312448793305943088659)
    ·
      refine ⟨112953468673189958914632989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75302312448793305943088659 112953468673189958914632989)
      ·
        refine ⟨42357550752446234592987371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112953468673189958914632989 42357550752446234592987371)
        ·
          refine ⟨63536326128669351889481057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42357550752446234592987371 63536326128669351889481057)
          ·
            refine ⟨47652244596502013917110793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63536326128669351889481057 47652244596502013917110793)
            ·
              refine ⟨35739183447376510437833095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47652244596502013917110793 35739183447376510437833095)
              ·
                refine ⟨53608775171064765656749643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35739183447376510437833095 53608775171064765656749643)
                ·
                  refine ⟨80413162756597148485124465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53608775171064765656749643 80413162756597148485124465)
                  ·
                    refine ⟨60309872067447861363843349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80413162756597148485124465 60309872067447861363843349)
                    ·
                      refine ⟨2827025253161618501430157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60309872067447861363843349 2827025253161618501430157)
                      ·
                        rfl

theorem cell23_5505612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5505612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505612 prefixEnd_5505612 := by exact prefixLift 5505612
  have htrace : WordTrace (prefixWord ++ tailWord_5505612) baseStart_5505612 baseEnd_5505612 := by
    simpa [prefixWord, tailWord_5505612, baseEnd_5505612] using wordTrace_append hprefix tailTrace_5505612
  have hstable : (prefixWord ++ tailWord_5505612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505612).length < 2 ^ (prefixWord ++ tailWord_5505612).sum := by decide
  have hdescent : baseEnd_5505612 < baseStart_5505612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505636 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_5505636 : Nat := 118140960795 + 5505636 * 2 ^ 59
def prefixEnd_5505636 : Nat := 4983230072969 + 3 ^ 40 * 5505636 * 2
def baseEnd_5505636 : Nat := 2827037576697326407530047

theorem tailTrace_5505636 : CollatzResearch.WordTrace tailWord_5505636 prefixEnd_5505636 2827037576697326407530047 := by
  unfold tailWord_5505636
  simp only [CollatzResearch.WordTrace]
  refine ⟨100403520941014267306888381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133871361254685689742517841 100403520941014267306888381)
  ·
    refine ⟨37651320352880350240083143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100403520941014267306888381 37651320352880350240083143)
    ·
      refine ⟨56476980529320525360124715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37651320352880350240083143 56476980529320525360124715)
      ·
        refine ⟨84715470793980788040187073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56476980529320525360124715 84715470793980788040187073)
        ·
          refine ⟨63536603095485591030140305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84715470793980788040187073 63536603095485591030140305)
          ·
            refine ⟨47652452321614193272605229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63536603095485591030140305 47652452321614193272605229)
            ·
              refine ⟨17869669620605322477226961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47652452321614193272605229 17869669620605322477226961)
              ·
                refine ⟨13402252215453991857920221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17869669620605322477226961 13402252215453991857920221)
                ·
                  refine ⟨5025844580795246946720083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13402252215453991857920221 5025844580795246946720083)
                  ·
                    refine ⟨7538766871192870420080125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5025844580795246946720083 7538766871192870420080125)
                    ·
                      refine ⟨2827037576697326407530047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7538766871192870420080125 2827037576697326407530047)
                      ·
                        rfl

theorem cell23_5505636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_5505636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505636 prefixEnd_5505636 := by exact prefixLift 5505636
  have htrace : WordTrace (prefixWord ++ tailWord_5505636) baseStart_5505636 baseEnd_5505636 := by
    simpa [prefixWord, tailWord_5505636, baseEnd_5505636] using wordTrace_append hprefix tailTrace_5505636
  have hstable : (prefixWord ++ tailWord_5505636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505636).length < 2 ^ (prefixWord ++ tailWord_5505636).sum := by decide
  have hdescent : baseEnd_5505636 < baseStart_5505636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505639 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 1, 5]
def baseStart_5505639 : Nat := 118140960795 + 5505639 * 2 ^ 59
def prefixEnd_5505639 : Nat := 4983230072969 + 3 ^ 40 * 5505639 * 2
def baseEnd_5505639 : Nat := 942346372379763298597511

theorem tailTrace_5505639 : CollatzResearch.WordTrace tailWord_5505639 prefixEnd_5505639 942346372379763298597511 := by
  unfold tailWord_5505639
  simp only [CollatzResearch.WordTrace]
  refine ⟨200807151301017666126135971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133871434200678444084090647 200807151301017666126135971)
  ·
    refine ⟨301210726951526499189203957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200807151301017666126135971 301210726951526499189203957)
    ·
      refine ⟨28238505651705609298987871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301210726951526499189203957 28238505651705609298987871)
      ·
        refine ⟨42357758477558413948481807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28238505651705609298987871 42357758477558413948481807)
        ·
          refine ⟨63536637716337620922722711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42357758477558413948481807 63536637716337620922722711)
          ·
            refine ⟨95304956574506431384084067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63536637716337620922722711 95304956574506431384084067)
            ·
              refine ⟨142957434861759647076126101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95304956574506431384084067 142957434861759647076126101)
              ·
                refine ⟨6701129759144983456693411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142957434861759647076126101 6701129759144983456693411)
                ·
                  refine ⟨10051694638717475185040117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701129759144983456693411 10051694638717475185040117)
                  ·
                    refine ⟨942346372379763298597511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10051694638717475185040117 942346372379763298597511)
                    ·
                      rfl

theorem cell23_5505639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_5505639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505639 prefixEnd_5505639 := by exact prefixLift 5505639
  have htrace : WordTrace (prefixWord ++ tailWord_5505639) baseStart_5505639 baseEnd_5505639 := by
    simpa [prefixWord, tailWord_5505639, baseEnd_5505639] using wordTrace_append hprefix tailTrace_5505639
  have hstable : (prefixWord ++ tailWord_5505639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505639).length < 2 ^ (prefixWord ++ tailWord_5505639).sum := by decide
  have hdescent : baseEnd_5505639 < baseStart_5505639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505640 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5505640 : Nat := 118140960795 + 5505640 * 2 ^ 59
def prefixEnd_5505640 : Nat := 4983230072969 + 3 ^ 40 * 5505640 * 2
def baseEnd_5505640 : Nat := 2827039630619944391880029

theorem tailTrace_5505640 : CollatzResearch.WordTrace tailWord_5505640 prefixEnd_5505640 2827039630619944391880029 := by
  unfold tailWord_5505640
  simp only [CollatzResearch.WordTrace]
  refine ⟨100403593887007021648461187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133871458516009362197948249 100403593887007021648461187)
  ·
    refine ⟨150605390830510532472691781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100403593887007021648461187 150605390830510532472691781)
    ·
      refine ⟨28238510780720724838629709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150605390830510532472691781 28238510780720724838629709)
      ·
        refine ⟨10589441542770271814486141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28238510780720724838629709 10589441542770271814486141)
        ·
          refine ⟨3971040578538851930432303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10589441542770271814486141 3971040578538851930432303)
          ·
            refine ⟨5956560867808277895648455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971040578538851930432303 5956560867808277895648455)
            ·
              refine ⟨8934841301712416843472683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956560867808277895648455 8934841301712416843472683)
              ·
                refine ⟨13402261952568625265209025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8934841301712416843472683 13402261952568625265209025)
                ·
                  refine ⟨10051696464426468948906769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13402261952568625265209025 10051696464426468948906769)
                  ·
                    refine ⟨7538772348319851711680077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10051696464426468948906769 7538772348319851711680077)
                    ·
                      refine ⟨2827039630619944391880029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7538772348319851711680077 2827039630619944391880029)
                      ·
                        rfl

theorem cell23_5505640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5505640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505640 prefixEnd_5505640 := by exact prefixLift 5505640
  have htrace : WordTrace (prefixWord ++ tailWord_5505640) baseStart_5505640 baseEnd_5505640 := by
    simpa [prefixWord, tailWord_5505640, baseEnd_5505640] using wordTrace_append hprefix tailTrace_5505640
  have hstable : (prefixWord ++ tailWord_5505640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505640).length < 2 ^ (prefixWord ++ tailWord_5505640).sum := by decide
  have hdescent : baseEnd_5505640 < baseStart_5505640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505693 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_5505693 : Nat := 118140960795 + 5505693 * 2 ^ 59
def prefixEnd_5505693 : Nat := 4983230072969 + 3 ^ 40 * 5505693 * 2
def baseEnd_5505693 : Nat := 2827066845094632684517285

theorem tailTrace_5505693 : CollatzResearch.WordTrace tailWord_5505693 prefixEnd_5505693 2827066845094632684517285 := by
  unfold tailWord_5505693
  simp only [CollatzResearch.WordTrace]
  refine ⟨200809120842822033348601733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133872747228548022232401155 200809120842822033348601733)
  ·
    refine ⟨37651710158029131252862825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200809120842822033348601733 37651710158029131252862825)
    ·
      refine ⟨28238782618521848439647119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37651710158029131252862825 28238782618521848439647119)
      ·
        refine ⟨42358173927782772659470679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28238782618521848439647119 42358173927782772659470679)
        ·
          refine ⟨63537260891674158989206019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42358173927782772659470679 63537260891674158989206019)
          ·
            refine ⟨95305891337511238483809029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63537260891674158989206019 95305891337511238483809029)
            ·
              refine ⟨17869854625783357215714193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95305891337511238483809029 17869854625783357215714193)
              ·
                refine ⟨13402390969337517911785645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17869854625783357215714193 13402390969337517911785645)
                ·
                  refine ⟨5025896613501569216919617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13402390969337517911785645 5025896613501569216919617)
                  ·
                    refine ⟨3769422460126176912689713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5025896613501569216919617 3769422460126176912689713)
                    ·
                      refine ⟨2827066845094632684517285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769422460126176912689713 2827066845094632684517285)
                      ·
                        rfl

theorem cell23_5505693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_5505693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505693 prefixEnd_5505693 := by exact prefixLift 5505693
  have htrace : WordTrace (prefixWord ++ tailWord_5505693) baseStart_5505693 baseEnd_5505693 := by
    simpa [prefixWord, tailWord_5505693, baseEnd_5505693] using wordTrace_append hprefix tailTrace_5505693
  have hstable : (prefixWord ++ tailWord_5505693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505693).length < 2 ^ (prefixWord ++ tailWord_5505693).sum := by decide
  have hdescent : baseEnd_5505693 < baseStart_5505693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505712 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_5505712 : Nat := 118140960795 + 5505712 * 2 ^ 59
def prefixEnd_5505712 : Nat := 4983230072969 + 3 ^ 40 * 5505712 * 2
def baseEnd_5505712 : Nat := 942358867075689370059899

theorem tailTrace_5505712 : CollatzResearch.WordTrace tailWord_5505712 prefixEnd_5505712 942358867075689370059899 := by
  unfold tailWord_5505712
  simp only [CollatzResearch.WordTrace]
  refine ⟨100404906914876599796771695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133873209219835466395695593 100404906914876599796771695)
  ·
    refine ⟨150607360372314899695157543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100404906914876599796771695 150607360372314899695157543)
    ·
      refine ⟨225911040558472349542736315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150607360372314899695157543 225911040558472349542736315)
      ·
        refine ⟨338866560837708524314104473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225911040558472349542736315 338866560837708524314104473)
        ·
          refine ⟨254149920628281393235578355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338866560837708524314104473 254149920628281393235578355)
          ·
            refine ⟨381224880942422089853367533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254149920628281393235578355 381224880942422089853367533)
            ·
              refine ⟨142959330353408283695012825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381224880942422089853367533 142959330353408283695012825)
              ·
                refine ⟨107219497765056212771259619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142959330353408283695012825 107219497765056212771259619)
                ·
                  refine ⟨160829246647584319156889429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107219497765056212771259619 160829246647584319156889429)
                  ·
                    refine ⟨942358867075689370059899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 160829246647584319156889429 942358867075689370059899)
                    ·
                      rfl

theorem cell23_5505712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_5505712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505712 prefixEnd_5505712 := by exact prefixLift 5505712
  have htrace : WordTrace (prefixWord ++ tailWord_5505712) baseStart_5505712 baseEnd_5505712 := by
    simpa [prefixWord, tailWord_5505712, baseEnd_5505712] using wordTrace_append hprefix tailTrace_5505712
  have hstable : (prefixWord ++ tailWord_5505712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505712).length < 2 ^ (prefixWord ++ tailWord_5505712).sum := by decide
  have hdescent : baseEnd_5505712 < baseStart_5505712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505713 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5505713 : Nat := 118140960795 + 5505713 * 2 ^ 59
def prefixEnd_5505713 : Nat := 4983230072969 + 3 ^ 40 * 5505713 * 2
def baseEnd_5505713 : Nat := 2827077114707722606267193

theorem tailTrace_5505713 : CollatzResearch.WordTrace tailWord_5505713 prefixEnd_5505713 2827077114707722606267193 := by
  unfold tailWord_5505713
  simp only [CollatzResearch.WordTrace]
  refine ⟨200809850302749576764329793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133873233535166384509553195 200809850302749576764329793)
  ·
    refine ⟨150607387727062182573247345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200809850302749576764329793 150607387727062182573247345)
    ·
      refine ⟨112955540795296636929935509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150607387727062182573247345 112955540795296636929935509)
      ·
        refine ⟨5294790974779529856090727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112955540795296636929935509 5294790974779529856090727)
        ·
          refine ⟨7942186462169294784136091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294790974779529856090727 7942186462169294784136091)
          ·
            refine ⟨11913279693253942176204137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942186462169294784136091 11913279693253942176204137)
            ·
              refine ⟨8934959769940456632153103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11913279693253942176204137 8934959769940456632153103)
              ·
                refine ⟨13402439654910684948229655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8934959769940456632153103 13402439654910684948229655)
                ·
                  refine ⟨20103659482366027422344483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13402439654910684948229655 20103659482366027422344483)
                  ·
                    refine ⟨30155489223549041133516725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20103659482366027422344483 30155489223549041133516725)
                    ·
                      refine ⟨2827077114707722606267193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30155489223549041133516725 2827077114707722606267193)
                      ·
                        rfl

theorem cell23_5505713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5505713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505713 prefixEnd_5505713 := by exact prefixLift 5505713
  have htrace : WordTrace (prefixWord ++ tailWord_5505713) baseStart_5505713 baseEnd_5505713 := by
    simpa [prefixWord, tailWord_5505713, baseEnd_5505713] using wordTrace_append hprefix tailTrace_5505713
  have hstable : (prefixWord ++ tailWord_5505713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505713).length < 2 ^ (prefixWord ++ tailWord_5505713).sum := by decide
  have hdescent : baseEnd_5505713 < baseStart_5505713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505727 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 1, 2, 2]
def baseStart_5505727 : Nat := 118140960795 + 5505727 * 2 ^ 59
def prefixEnd_5505727 : Nat := 4983230072969 + 3 ^ 40 * 5505727 * 2
def baseEnd_5505727 : Nat := 2827084303436885551492129

theorem tailTrace_5505727 : CollatzResearch.WordTrace tailWord_5505727 prefixEnd_5505727 2827084303436885551492129 := by
  unfold tailWord_5505727
  simp only [CollatzResearch.WordTrace]
  refine ⟨200810360924698857155339435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133873573949799238103559623 200810360924698857155339435)
  ·
    refine ⟨301215541387048285733009153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200810360924698857155339435 301215541387048285733009153)
    ·
      refine ⟨225911656040286214299756865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301215541387048285733009153 225911656040286214299756865)
      ·
        refine ⟨169433742030214660724817649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225911656040286214299756865 169433742030214660724817649)
        ·
          refine ⟨127075306522660995543613237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169433742030214660724817649 127075306522660995543613237)
          ·
            refine ⟨11913309986499468332213741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127075306522660995543613237 11913309986499468332213741)
            ·
              refine ⟨4467491244937300624580153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11913309986499468332213741 4467491244937300624580153)
              ·
                refine ⟨3350618433702975468435115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467491244937300624580153 3350618433702975468435115)
                ·
                  refine ⟨5025927650554463202652673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350618433702975468435115 5025927650554463202652673)
                  ·
                    refine ⟨3769445737915847401989505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5025927650554463202652673 3769445737915847401989505)
                    ·
                      refine ⟨2827084303436885551492129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769445737915847401989505 2827084303436885551492129)
                      ·
                        rfl

theorem cell23_5505727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_5505727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505727 prefixEnd_5505727 := by exact prefixLift 5505727
  have htrace : WordTrace (prefixWord ++ tailWord_5505727) baseStart_5505727 baseEnd_5505727 := by
    simpa [prefixWord, tailWord_5505727, baseEnd_5505727] using wordTrace_append hprefix tailTrace_5505727
  have hstable : (prefixWord ++ tailWord_5505727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505727).length < 2 ^ (prefixWord ++ tailWord_5505727).sum := by decide
  have hdescent : baseEnd_5505727 < baseStart_5505727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505769 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_5505769 : Nat := 118140960795 + 5505769 * 2 ^ 59
def prefixEnd_5505769 : Nat := 4983230072969 + 3 ^ 40 * 5505769 * 2
def baseEnd_5505769 : Nat := 2827105869624374387166935

theorem tailTrace_5505769 : CollatzResearch.WordTrace tailWord_5505769 prefixEnd_5505769 2827105869624374387166935 := by
  unfold tailWord_5505769
  simp only [CollatzResearch.WordTrace]
  refine ⟨200811892790546698328368361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133874595193697798885578907 200811892790546698328368361)
  ·
    refine ⟨150608919592910023746276271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200811892790546698328368361 150608919592910023746276271)
    ·
      refine ⟨225913379389365035619414407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150608919592910023746276271 225913379389365035619414407)
      ·
        refine ⟨338870069084047553429121611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225913379389365035619414407 338870069084047553429121611)
        ·
          refine ⟨508305103626071330143682417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338870069084047553429121611 508305103626071330143682417)
          ·
            refine ⟨381228827719553497607761813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508305103626071330143682417 381228827719553497607761813)
            ·
              refine ⟨17870101299354070200363835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 381228827719553497607761813 17870101299354070200363835)
              ·
                refine ⟨26805151949031105300545753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17870101299354070200363835 26805151949031105300545753)
                ·
                  refine ⟨20103863961773328975409315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26805151949031105300545753 20103863961773328975409315)
                  ·
                    refine ⟨30155795942659993463113973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20103863961773328975409315 30155795942659993463113973)
                    ·
                      refine ⟨2827105869624374387166935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30155795942659993463113973 2827105869624374387166935)
                      ·
                        rfl

theorem cell23_5505769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_5505769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505769 prefixEnd_5505769 := by exact prefixLift 5505769
  have htrace : WordTrace (prefixWord ++ tailWord_5505769) baseStart_5505769 baseEnd_5505769 := by
    simpa [prefixWord, tailWord_5505769, baseEnd_5505769] using wordTrace_append hprefix tailTrace_5505769
  have hstable : (prefixWord ++ tailWord_5505769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505769).length < 2 ^ (prefixWord ++ tailWord_5505769).sum := by decide
  have hdescent : baseEnd_5505769 < baseStart_5505769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505779 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_5505779 : Nat := 118140960795 + 5505779 * 2 ^ 59
def prefixEnd_5505779 : Nat := 4983230072969 + 3 ^ 40 * 5505779 * 2
def baseEnd_5505779 : Nat := 2827111004430919348041889

theorem tailTrace_5505779 : CollatzResearch.WordTrace tailWord_5505779 prefixEnd_5505779 2827111004430919348041889 := by
  unfold tailWord_5505779
  simp only [CollatzResearch.WordTrace]
  refine ⟨200812257520510470036232391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133874838347006980024154927 200812257520510470036232391)
  ·
    refine ⟨301218386280765705054348587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200812257520510470036232391 301218386280765705054348587)
    ·
      refine ⟨451827579421148557581522881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301218386280765705054348587 451827579421148557581522881)
      ·
        refine ⟨338870684565861418186142161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451827579421148557581522881 338870684565861418186142161)
        ·
          refine ⟨254153013424396063639606621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338870684565861418186142161 254153013424396063639606621)
          ·
            refine ⟨95307380034148523864852483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254153013424396063639606621 95307380034148523864852483)
            ·
              refine ⟨142961070051222785797278725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95307380034148523864852483 142961070051222785797278725)
              ·
                refine ⟨26805200634604272336989761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142961070051222785797278725 26805200634604272336989761)
                ·
                  refine ⟨20103900475953204252742321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26805200634604272336989761 20103900475953204252742321)
                  ·
                    refine ⟨15077925356964903189556741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20103900475953204252742321 15077925356964903189556741)
                    ·
                      refine ⟨2827111004430919348041889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15077925356964903189556741 2827111004430919348041889)
                      ·
                        rfl

theorem cell23_5505779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_5505779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505779 prefixEnd_5505779 := by exact prefixLift 5505779
  have htrace : WordTrace (prefixWord ++ tailWord_5505779) baseStart_5505779 baseEnd_5505779 := by
    simpa [prefixWord, tailWord_5505779, baseEnd_5505779] using wordTrace_append hprefix tailTrace_5505779
  have hstable : (prefixWord ++ tailWord_5505779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505779).length < 2 ^ (prefixWord ++ tailWord_5505779).sum := by decide
  have hdescent : baseEnd_5505779 < baseStart_5505779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505789 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 7]
def baseStart_5505789 : Nat := 118140960795 + 5505789 * 2 ^ 59
def prefixEnd_5505789 : Nat := 4983230072969 + 3 ^ 40 * 5505789 * 2
def baseEnd_5505789 : Nat := 314124015470829367657427

theorem tailTrace_5505789 : CollatzResearch.WordTrace tailWord_5505789 prefixEnd_5505789 314124015470829367657427 := by
  unfold tailWord_5505789
  simp only [CollatzResearch.WordTrace]
  refine ⟨200812622250474241744096421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133875081500316161162730947 200812622250474241744096421)
  ·
    refine ⟨37652366671963920327018079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200812622250474241744096421 37652366671963920327018079)
    ·
      refine ⟨56478550007945880490527119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37652366671963920327018079 56478550007945880490527119)
      ·
        refine ⟨84717825011918820735790679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56478550007945880490527119 84717825011918820735790679)
        ·
          refine ⟨127076737517878231103686019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84717825011918820735790679 127076737517878231103686019)
          ·
            refine ⟨190615106276817346655529029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127076737517878231103686019 190615106276817346655529029)
            ·
              refine ⟨35740332426903252497911693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190615106276817346655529029 35740332426903252497911693)
              ·
                refine ⟨13402624660088719686716885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35740332426903252497911693 13402624660088719686716885)
                ·
                  refine ⟨314124015470829367657427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13402624660088719686716885 314124015470829367657427)
                  ·
                    rfl

theorem cell23_5505789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_5505789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505789 prefixEnd_5505789 := by exact prefixLift 5505789
  have htrace : WordTrace (prefixWord ++ tailWord_5505789) baseStart_5505789 baseEnd_5505789 := by
    simpa [prefixWord, tailWord_5505789, baseEnd_5505789] using wordTrace_append hprefix tailTrace_5505789
  have hstable : (prefixWord ++ tailWord_5505789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505789).length < 2 ^ (prefixWord ++ tailWord_5505789).sum := by decide
  have hdescent : baseEnd_5505789 < baseStart_5505789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505796 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5505796 : Nat := 118140960795 + 5505796 * 2 ^ 59
def prefixEnd_5505796 : Nat := 4983230072969 + 3 ^ 40 * 5505796 * 2
def baseEnd_5505796 : Nat := 2827119733602045781529311

theorem tailTrace_5505796 : CollatzResearch.WordTrace tailWord_5505796 prefixEnd_5505796 2827119733602045781529311 := by
  unfold tailWord_5505796
  simp only [CollatzResearch.WordTrace]
  refine ⟨100406438780724440969800621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133875251707632587959734161 100406438780724440969800621)
  ·
    refine ⟨37652414542771665363675233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100406438780724440969800621 37652414542771665363675233)
    ·
      refine ⟨28239310907078749022756425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37652414542771665363675233 28239310907078749022756425)
      ·
        refine ⟨21179483180309061767067319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28239310907078749022756425 21179483180309061767067319)
        ·
          refine ⟨31769224770463592650600979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21179483180309061767067319 31769224770463592650600979)
          ·
            refine ⟨47653837155695388975901469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31769224770463592650600979 47653837155695388975901469)
            ·
              refine ⟨17870188933385770865963051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47653837155695388975901469 17870188933385770865963051)
              ·
                refine ⟨26805283400078656298944577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17870188933385770865963051 26805283400078656298944577)
                ·
                  refine ⟨20103962550058992224208433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26805283400078656298944577 20103962550058992224208433)
                  ·
                    refine ⟨15077971912544244168156325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20103962550058992224208433 15077971912544244168156325)
                    ·
                      refine ⟨2827119733602045781529311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15077971912544244168156325 2827119733602045781529311)
                      ·
                        rfl

theorem cell23_5505796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5505796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505796 prefixEnd_5505796 := by exact prefixLift 5505796
  have htrace : WordTrace (prefixWord ++ tailWord_5505796) baseStart_5505796 baseEnd_5505796 := by
    simpa [prefixWord, tailWord_5505796, baseEnd_5505796] using wordTrace_append hprefix tailTrace_5505796
  have hstable : (prefixWord ++ tailWord_5505796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505796).length < 2 ^ (prefixWord ++ tailWord_5505796).sum := by decide
  have hdescent : baseEnd_5505796 < baseStart_5505796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505800 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_5505800 : Nat := 118140960795 + 5505800 * 2 ^ 59
def prefixEnd_5505800 : Nat := 4983230072969 + 3 ^ 40 * 5505800 * 2
def baseEnd_5505800 : Nat := 2827121787524663765879293

theorem tailTrace_5505800 : CollatzResearch.WordTrace tailWord_5505800 prefixEnd_5505800 2827121787524663765879293 := by
  unfold tailWord_5505800
  simp only [CollatzResearch.WordTrace]
  refine ⟨100406511726717195311373427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133875348968956260415164569 100406511726717195311373427)
  ·
    refine ⟨150609767590075792967060141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100406511726717195311373427 150609767590075792967060141)
    ·
      refine ⟨56478662846278422362647553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150609767590075792967060141 56478662846278422362647553)
      ·
        refine ⟨42358997134708816771985665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56478662846278422362647553 42358997134708816771985665)
        ·
          refine ⟨31769247851031612578989249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42358997134708816771985665 31769247851031612578989249)
          ·
            refine ⟨23826935888273709434241937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31769247851031612578989249 23826935888273709434241937)
            ·
              refine ⟨17870201916205282075681453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23826935888273709434241937 17870201916205282075681453)
              ·
                refine ⟨6701325718576980778380545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17870201916205282075681453 6701325718576980778380545)
                ·
                  refine ⟨5025994288932735583785409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6701325718576980778380545 5025994288932735583785409)
                  ·
                    refine ⟨3769495716699551687839057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5025994288932735583785409 3769495716699551687839057)
                    ·
                      refine ⟨2827121787524663765879293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769495716699551687839057 2827121787524663765879293)
                      ·
                        rfl

theorem cell23_5505800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_5505800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505800 prefixEnd_5505800 := by exact prefixLift 5505800
  have htrace : WordTrace (prefixWord ++ tailWord_5505800) baseStart_5505800 baseEnd_5505800 := by
    simpa [prefixWord, tailWord_5505800, baseEnd_5505800] using wordTrace_append hprefix tailTrace_5505800
  have hstable : (prefixWord ++ tailWord_5505800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505800).length < 2 ^ (prefixWord ++ tailWord_5505800).sum := by decide
  have hdescent : baseEnd_5505800 < baseStart_5505800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505821 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5505821 : Nat := 118140960795 + 5505821 * 2 ^ 59
def prefixEnd_5505821 : Nat := 4983230072969 + 3 ^ 40 * 5505821 * 2
def baseEnd_5505821 : Nat := 2827132570618408183716697

theorem tailTrace_5505821 : CollatzResearch.WordTrace tailWord_5505821 prefixEnd_5505821 2827132570618408183716697 := by
  unfold tailWord_5505821
  simp only [CollatzResearch.WordTrace]
  refine ⟨200813789386358311209261317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133875859590905540806174211 200813789386358311209261317)
  ·
    refine ⟨37652585509942183351736497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200813789386358311209261317 37652585509942183351736497)
    ·
      refine ⟨28239439132456637513802373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37652585509942183351736497 28239439132456637513802373)
      ·
        refine ⟨5294894837335619533837945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28239439132456637513802373 5294894837335619533837945)
        ·
          refine ⟨3971171128001714650378459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5294894837335619533837945 3971171128001714650378459)
          ·
            refine ⟨5956756692002571975567689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971171128001714650378459 5956756692002571975567689)
            ·
              refine ⟨4467567519001928981675767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956756692002571975567689 4467567519001928981675767)
              ·
                refine ⟨6701351278502893472513651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467567519001928981675767 6701351278502893472513651)
                ·
                  refine ⟨10052026917754340208770477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701351278502893472513651 10052026917754340208770477)
                  ·
                    refine ⟨3769510094157877578288929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10052026917754340208770477 3769510094157877578288929)
                    ·
                      refine ⟨2827132570618408183716697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769510094157877578288929 2827132570618408183716697)
                      ·
                        rfl

theorem cell23_5505821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5505821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505821 prefixEnd_5505821 := by exact prefixLift 5505821
  have htrace : WordTrace (prefixWord ++ tailWord_5505821) baseStart_5505821 baseEnd_5505821 := by
    simpa [prefixWord, tailWord_5505821, baseEnd_5505821] using wordTrace_append hprefix tailTrace_5505821
  have hstable : (prefixWord ++ tailWord_5505821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505821).length < 2 ^ (prefixWord ++ tailWord_5505821).sum := by decide
  have hdescent : baseEnd_5505821 < baseStart_5505821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505823 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 5]
def baseStart_5505823 : Nat := 118140960795 + 5505823 * 2 ^ 59
def prefixEnd_5505823 : Nat := 4983230072969 + 3 ^ 40 * 5505823 * 2
def baseEnd_5505823 : Nat := 314125955286635241765743

theorem tailTrace_5505823 : CollatzResearch.WordTrace tailWord_5505823 prefixEnd_5505823 314125955286635241765743 := by
  unfold tailWord_5505823
  simp only [CollatzResearch.WordTrace]
  refine ⟨200813862332351065550834123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133875908221567377033889415 200813862332351065550834123)
  ·
    refine ⟨301220793498526598326251185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200813862332351065550834123 301220793498526598326251185)
    ·
      refine ⟨225915595123894948744688389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301220793498526598326251185 225915595123894948744688389)
      ·
        refine ⟨42359174085730302889629073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225915595123894948744688389 42359174085730302889629073)
        ·
          refine ⟨31769380564297727167221805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42359174085730302889629073 31769380564297727167221805)
          ·
            refine ⟨11913517711611647687708177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31769380564297727167221805 11913517711611647687708177)
            ·
              refine ⟨8935138283708735765781133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11913517711611647687708177 8935138283708735765781133)
              ·
                refine ⟨3350676856390775912167925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8935138283708735765781133 3350676856390775912167925)
                ·
                  refine ⟨314125955286635241765743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3350676856390775912167925 314125955286635241765743)
                  ·
                    rfl

theorem cell23_5505823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 5].length) (baseStart_5505823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505823 prefixEnd_5505823 := by exact prefixLift 5505823
  have htrace : WordTrace (prefixWord ++ tailWord_5505823) baseStart_5505823 baseEnd_5505823 := by
    simpa [prefixWord, tailWord_5505823, baseEnd_5505823] using wordTrace_append hprefix tailTrace_5505823
  have hstable : (prefixWord ++ tailWord_5505823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505823).length < 2 ^ (prefixWord ++ tailWord_5505823).sum := by decide
  have hdescent : baseEnd_5505823 < baseStart_5505823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505839 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_5505839 : Nat := 118140960795 + 5505839 * 2 ^ 59
def prefixEnd_5505839 : Nat := 4983230072969 + 3 ^ 40 * 5505839 * 2
def baseEnd_5505839 : Nat := 2827141813270189113291613

theorem tailTrace_5505839 : CollatzResearch.WordTrace tailWord_5505839 prefixEnd_5505839 2827141813270189113291613 := by
  unfold tailWord_5505839
  simp only [CollatzResearch.WordTrace]
  refine ⟨200814445900293100283416571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133876297266862066855611047 200814445900293100283416571)
  ·
    refine ⟨301221668850439650425124857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200814445900293100283416571 301221668850439650425124857)
    ·
      refine ⟨225916251637829737818843643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301221668850439650425124857 225916251637829737818843643)
      ·
        refine ⟨338874377456744606728265465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225916251637829737818843643 338874377456744606728265465)
        ·
          refine ⟨254155783092558455046199099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338874377456744606728265465 254155783092558455046199099)
          ·
            refine ⟨381233674638837682569298649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254155783092558455046199099 381233674638837682569298649)
            ·
              refine ⟨285925255979128261926973987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381233674638837682569298649 285925255979128261926973987)
              ·
                refine ⟨428887883968692392890460981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285925255979128261926973987 428887883968692392890460981)
                ·
                  refine ⟨40208239122064911833480717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428887883968692392890460981 40208239122064911833480717)
                  ·
                    refine ⟨15078089670774341937555269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40208239122064911833480717 15078089670774341937555269)
                    ·
                      refine ⟨2827141813270189113291613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15078089670774341937555269 2827141813270189113291613)
                      ·
                        rfl

theorem cell23_5505839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_5505839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505839 prefixEnd_5505839 := by exact prefixLift 5505839
  have htrace : WordTrace (prefixWord ++ tailWord_5505839) baseStart_5505839 baseEnd_5505839 := by
    simpa [prefixWord, tailWord_5505839, baseEnd_5505839] using wordTrace_append hprefix tailTrace_5505839
  have hstable : (prefixWord ++ tailWord_5505839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505839).length < 2 ^ (prefixWord ++ tailWord_5505839).sum := by decide
  have hdescent : baseEnd_5505839 < baseStart_5505839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505866 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_5505866 : Nat := 118140960795 + 5505866 * 2 ^ 59
def prefixEnd_5505866 : Nat := 4983230072969 + 3 ^ 40 * 5505866 * 2
def baseEnd_5505866 : Nat := 942385225749286835884663

theorem tailTrace_5505866 : CollatzResearch.WordTrace tailWord_5505866 prefixEnd_5505866 942385225749286835884663 := by
  unfold tailWord_5505866
  simp only [CollatzResearch.WordTrace]
  refine ⟨50203857667798820973662363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133876953780796855929766301 50203857667798820973662363)
  ·
    refine ⟨75305786501698231460493545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50203857667798820973662363 75305786501698231460493545)
    ·
      refine ⟨56479339876273673595370159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75305786501698231460493545 56479339876273673595370159)
      ·
        refine ⟨84719009814410510393055239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56479339876273673595370159 84719009814410510393055239)
        ·
          refine ⟨127078514721615765589582859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84719009814410510393055239 127078514721615765589582859)
          ·
            refine ⟨190617772082423648384374289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127078514721615765589582859 190617772082423648384374289)
            ·
              refine ⟨142963329061817736288280717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190617772082423648384374289 142963329061817736288280717)
              ·
                refine ⟨53611248398181651108105269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142963329061817736288280717 53611248398181651108105269)
                ·
                  refine ⟨5026054537329529791384869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53611248398181651108105269 5026054537329529791384869)
                  ·
                    refine ⟨942385225749286835884663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5026054537329529791384869 942385225749286835884663)
                    ·
                      rfl

theorem cell23_5505866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_5505866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505866 prefixEnd_5505866 := by exact prefixLift 5505866
  have htrace : WordTrace (prefixWord ++ tailWord_5505866) baseStart_5505866 baseEnd_5505866 := by
    simpa [prefixWord, tailWord_5505866, baseEnd_5505866] using wordTrace_append hprefix tailTrace_5505866
  have hstable : (prefixWord ++ tailWord_5505866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505866).length < 2 ^ (prefixWord ++ tailWord_5505866).sum := by decide
  have hdescent : baseEnd_5505866 < baseStart_5505866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505890 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5505890 : Nat := 118140960795 + 5505890 * 2 ^ 59
def prefixEnd_5505890 : Nat := 4983230072969 + 3 ^ 40 * 5505890 * 2
def baseEnd_5505890 : Nat := 2827168000783568413753879

theorem tailTrace_5505890 : CollatzResearch.WordTrace tailWord_5505890 prefixEnd_5505890 2827168000783568413753879 := by
  unfold tailWord_5505890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50204076505777083998380781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133877537348738890662348749 50204076505777083998380781)
  ·
    refine ⟨18826528689666406499392793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50204076505777083998380781 18826528689666406499392793)
    ·
      refine ⟨14119896517249804874544595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18826528689666406499392793 14119896517249804874544595)
      ·
        refine ⟨21179844775874707311816893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14119896517249804874544595 21179844775874707311816893)
        ·
          refine ⟨7942441790953015241931335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21179844775874707311816893 7942441790953015241931335)
          ·
            refine ⟨11913662686429522862897003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942441790953015241931335 11913662686429522862897003)
            ·
              refine ⟨17870494029644284294345505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11913662686429522862897003 17870494029644284294345505)
              ·
                refine ⟨13402870522233213220759129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17870494029644284294345505 13402870522233213220759129)
                ·
                  refine ⟨10052152891674909915569347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13402870522233213220759129 10052152891674909915569347)
                  ·
                    refine ⟨15078229337512364873354021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10052152891674909915569347 15078229337512364873354021)
                    ·
                      refine ⟨2827168000783568413753879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15078229337512364873354021 2827168000783568413753879)
                      ·
                        rfl

theorem cell23_5505890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5505890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505890 prefixEnd_5505890 := by exact prefixLift 5505890
  have htrace : WordTrace (prefixWord ++ tailWord_5505890) baseStart_5505890 baseEnd_5505890 := by
    simpa [prefixWord, tailWord_5505890, baseEnd_5505890] using wordTrace_append hprefix tailTrace_5505890
  have hstable : (prefixWord ++ tailWord_5505890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505890).length < 2 ^ (prefixWord ++ tailWord_5505890).sum := by decide
  have hdescent : baseEnd_5505890 < baseStart_5505890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505896 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 8]
def baseStart_5505896 : Nat := 118140960795 + 5505896 * 2 ^ 59
def prefixEnd_5505896 : Nat := 4983230072969 + 3 ^ 40 * 5505896 * 2
def baseEnd_5505896 : Nat := 314130120185277265586539

theorem tailTrace_5505896 : CollatzResearch.WordTrace tailWord_5505896 prefixEnd_5505896 314130120185277265586539 := by
  unfold tailWord_5505896
  simp only [CollatzResearch.WordTrace]
  refine ⟨100408262430543299509120771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133877683240724399345494361 100408262430543299509120771)
  ·
    refine ⟨150612393645814949263681157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100408262430543299509120771 150612393645814949263681157)
    ·
      refine ⟨28239823808590302986940217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150612393645814949263681157 28239823808590302986940217)
      ·
        refine ⟨21179867856442727240205163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28239823808590302986940217 21179867856442727240205163)
        ·
          refine ⟨31769801784664090860307745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21179867856442727240205163 31769801784664090860307745)
          ·
            refine ⟨23827351338498068145230809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31769801784664090860307745 23827351338498068145230809)
            ·
              refine ⟨17870513503873551108923107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23827351338498068145230809 17870513503873551108923107)
              ·
                refine ⟨26805770255810326663384661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17870513503873551108923107 26805770255810326663384661)
                ·
                  refine ⟨314130120185277265586539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26805770255810326663384661 314130120185277265586539)
                  ·
                    rfl

theorem cell23_5505896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_5505896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505896 prefixEnd_5505896 := by exact prefixLift 5505896
  have htrace : WordTrace (prefixWord ++ tailWord_5505896) baseStart_5505896 baseEnd_5505896 := by
    simpa [prefixWord, tailWord_5505896, baseEnd_5505896] using wordTrace_append hprefix tailTrace_5505896
  have hstable : (prefixWord ++ tailWord_5505896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505896).length < 2 ^ (prefixWord ++ tailWord_5505896).sum := by decide
  have hdescent : baseEnd_5505896 < baseStart_5505896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505899 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_5505899 : Nat := 118140960795 + 5505899 * 2 ^ 59
def prefixEnd_5505899 : Nat := 4983230072969 + 3 ^ 40 * 5505899 * 2
def baseEnd_5505899 : Nat := 2827172622109458878541337

theorem tailTrace_5505899 : CollatzResearch.WordTrace tailWord_5505899 prefixEnd_5505899 2827172622109458878541337 := by
  unfold tailWord_5505899
  simp only [CollatzResearch.WordTrace]
  refine ⟨200816634280075730530600751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133877756186717153687067167 200816634280075730530600751)
  ·
    refine ⟨301224951420113595795901127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200816634280075730530600751 301224951420113595795901127)
    ·
      refine ⟨451837427130170393693851691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301224951420113595795901127 451837427130170393693851691)
      ·
        refine ⟨677756140695255590540777537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451837427130170393693851691 677756140695255590540777537)
        ·
          refine ⟨508317105521441692905583153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677756140695255590540777537 508317105521441692905583153)
          ·
            refine ⟨381237829141081269679187365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508317105521441692905583153 381237829141081269679187365)
            ·
              refine ⟨71482092963952738064847631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 381237829141081269679187365 71482092963952738064847631)
              ·
                refine ⟨107223139445929107097271447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71482092963952738064847631 107223139445929107097271447)
                ·
                  refine ⟨160834709168893660645907171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107223139445929107097271447 160834709168893660645907171)
                  ·
                    refine ⟨241252063753340490968860757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160834709168893660645907171 241252063753340490968860757)
                    ·
                      refine ⟨2827172622109458878541337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241252063753340490968860757 2827172622109458878541337)
                      ·
                        rfl

theorem cell23_5505899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_5505899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505899 prefixEnd_5505899 := by exact prefixLift 5505899
  have htrace : WordTrace (prefixWord ++ tailWord_5505899) baseStart_5505899 baseEnd_5505899 := by
    simpa [prefixWord, tailWord_5505899, baseEnd_5505899] using wordTrace_append hprefix tailTrace_5505899
  have hstable : (prefixWord ++ tailWord_5505899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505899).length < 2 ^ (prefixWord ++ tailWord_5505899).sum := by decide
  have hdescent : baseEnd_5505899 < baseStart_5505899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505913 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 6]
def baseStart_5505913 : Nat := 118140960795 + 5505913 * 2 ^ 59
def prefixEnd_5505913 : Nat := 4983230072969 + 3 ^ 40 * 5505913 * 2
def baseEnd_5505913 : Nat := 314131090093180202640697

theorem tailTrace_5505913 : CollatzResearch.WordTrace tailWord_5505913 prefixEnd_5505913 314131090093180202640697 := by
  unfold tailWord_5505913
  simp only [CollatzResearch.WordTrace]
  refine ⟨200817144902025010921610393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133878096601350007281073595 200817144902025010921610393)
  ·
    refine ⟨150612858676518758191207795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200817144902025010921610393 150612858676518758191207795)
    ·
      refine ⟨225919288014778137286811693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150612858676518758191207795 225919288014778137286811693)
      ·
        refine ⟨84719733005541801482554385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225919288014778137286811693 84719733005541801482554385)
        ·
          refine ⟨63539799754156351111915789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84719733005541801482554385 63539799754156351111915789)
          ·
            refine ⟨23827424907808631666968421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63539799754156351111915789 23827424907808631666968421)
            ·
              refine ⟨4467642170214118437556579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23827424907808631666968421 4467642170214118437556579)
              ·
                refine ⟨6701463255321177656334869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467642170214118437556579 6701463255321177656334869)
                ·
                  refine ⟨314131090093180202640697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6701463255321177656334869 314131090093180202640697)
                  ·
                    rfl

theorem cell23_5505913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 6].length) (baseStart_5505913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505913 prefixEnd_5505913 := by exact prefixLift 5505913
  have htrace : WordTrace (prefixWord ++ tailWord_5505913) baseStart_5505913 baseEnd_5505913 := by
    simpa [prefixWord, tailWord_5505913, baseEnd_5505913] using wordTrace_append hprefix tailTrace_5505913
  have hstable : (prefixWord ++ tailWord_5505913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505913).length < 2 ^ (prefixWord ++ tailWord_5505913).sum := by decide
  have hdescent : baseEnd_5505913 < baseStart_5505913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505923 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 3]
def baseStart_5505923 : Nat := 118140960795 + 5505923 * 2 ^ 59
def prefixEnd_5505923 : Nat := 4983230072969 + 3 ^ 40 * 5505923 * 2
def baseEnd_5505923 : Nat := 2827184945645166784641227

theorem tailTrace_5505923 : CollatzResearch.WordTrace tailWord_5505923 prefixEnd_5505923 2827184945645166784641227 := by
  unfold tailWord_5505923
  simp only [CollatzResearch.WordTrace]
  refine ⟨200817509631988782629474423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133878339754659188419649615 200817509631988782629474423)
  ·
    refine ⟨301226264447983173944211635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200817509631988782629474423 301226264447983173944211635)
    ·
      refine ⟨451839396671974760916317453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301226264447983173944211635 451839396671974760916317453)
      ·
        refine ⟨169439773751990535343619045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451839396671974760916317453 169439773751990535343619045)
        ·
          refine ⟨31769957578498225376928571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169439773751990535343619045 31769957578498225376928571)
          ·
            refine ⟨47654936367747338065392857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31769957578498225376928571 47654936367747338065392857)
            ·
              refine ⟨35741202275810503549044643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47654936367747338065392857 35741202275810503549044643)
              ·
                refine ⟨53611803413715755323566965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35741202275810503549044643 53611803413715755323566965)
                ·
                  refine ⟨5026106570035852061584403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53611803413715755323566965 5026106570035852061584403)
                  ·
                    refine ⟨7539159855053778092376605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5026106570035852061584403 7539159855053778092376605)
                    ·
                      refine ⟨2827184945645166784641227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7539159855053778092376605 2827184945645166784641227)
                      ·
                        rfl

theorem cell23_5505923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_5505923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505923 prefixEnd_5505923 := by exact prefixLift 5505923
  have htrace : WordTrace (prefixWord ++ tailWord_5505923) baseStart_5505923 baseEnd_5505923 := by
    simpa [prefixWord, tailWord_5505923, baseEnd_5505923] using wordTrace_append hprefix tailTrace_5505923
  have hstable : (prefixWord ++ tailWord_5505923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505923).length < 2 ^ (prefixWord ++ tailWord_5505923).sum := by decide
  have hdescent : baseEnd_5505923 < baseStart_5505923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505956 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_5505956 : Nat := 118140960795 + 5505956 * 2 ^ 59
def prefixEnd_5505956 : Nat := 4983230072969 + 3 ^ 40 * 5505956 * 2
def baseEnd_5505956 : Nat := 942400630168921718509525

theorem tailTrace_5505956 : CollatzResearch.WordTrace tailWord_5505956 prefixEnd_5505956 942400630168921718509525 := by
  unfold tailWord_5505956
  simp only [CollatzResearch.WordTrace]
  refine ⟨100409356620434614632712861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133879142160579486176950481 100409356620434614632712861)
  ·
    refine ⟨37653508732662980487267323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100409356620434614632712861 37653508732662980487267323)
    ·
      refine ⟨56480263098994470730900985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37653508732662980487267323 56480263098994470730900985)
      ·
        refine ⟨42360197324245853048175739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56480263098994470730900985 42360197324245853048175739)
        ·
          refine ⟨63540295986368779572263609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42360197324245853048175739 63540295986368779572263609)
          ·
            refine ⟨47655221989776584679197707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63540295986368779572263609 47655221989776584679197707)
            ·
              refine ⟨71482832984664877018796561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47655221989776584679197707 71482832984664877018796561)
              ·
                refine ⟨53612124738498657764097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71482832984664877018796561 53612124738498657764097421)
                ·
                  refine ⟨20104546776936996661536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53612124738498657764097421 20104546776936996661536533)
                  ·
                    refine ⟨942400630168921718509525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20104546776936996661536533 942400630168921718509525)
                    ·
                      rfl

theorem cell23_5505956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_5505956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505956 prefixEnd_5505956 := by exact prefixLift 5505956
  have htrace : WordTrace (prefixWord ++ tailWord_5505956) baseStart_5505956 baseEnd_5505956 := by
    simpa [prefixWord, tailWord_5505956, baseEnd_5505956] using wordTrace_append hprefix tailTrace_5505956
  have hstable : (prefixWord ++ tailWord_5505956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505956).length < 2 ^ (prefixWord ++ tailWord_5505956).sum := by decide
  have hdescent : baseEnd_5505956 < baseStart_5505956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5505973 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_5505973 : Nat := 118140960795 + 5505973 * 2 ^ 59
def prefixEnd_5505973 : Nat := 4983230072969 + 3 ^ 40 * 5505973 * 2
def baseEnd_5505973 : Nat := 942403539892630529671999

theorem tailTrace_5505973 : CollatzResearch.WordTrace tailWord_5505973 prefixEnd_5505973 942403539892630529671999 := by
  unfold tailWord_5505973
  simp only [CollatzResearch.WordTrace]
  refine ⟨200819333281807641168794573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133879555521205094112529715 200819333281807641168794573)
  ·
    refine ⟨75307249980677865438297965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200819333281807641168794573 75307249980677865438297965)
    ·
      refine ⟨28240218742754199539361737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75307249980677865438297965 28240218742754199539361737)
      ·
        refine ⟨21180164057065649654521303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28240218742754199539361737 21180164057065649654521303)
        ·
          refine ⟨31770246085598474481781955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21180164057065649654521303 31770246085598474481781955)
          ·
            refine ⟨47655369128397711722672933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31770246085598474481781955 47655369128397711722672933)
            ·
              refine ⟨8935381711574570948001175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47655369128397711722672933 8935381711574570948001175)
              ·
                refine ⟨13403072567361856422001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8935381711574570948001175 13403072567361856422001763)
                ·
                  refine ⟨20104608851042784633002645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13403072567361856422001763 20104608851042784633002645)
                  ·
                    refine ⟨942403539892630529671999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20104608851042784633002645 942403539892630529671999)
                    ·
                      rfl

theorem cell23_5505973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_5505973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5505973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5505973 prefixEnd_5505973 := by exact prefixLift 5505973
  have htrace : WordTrace (prefixWord ++ tailWord_5505973) baseStart_5505973 baseEnd_5505973 := by
    simpa [prefixWord, tailWord_5505973, baseEnd_5505973] using wordTrace_append hprefix tailTrace_5505973
  have hstable : (prefixWord ++ tailWord_5505973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5505973).length < 2 ^ (prefixWord ++ tailWord_5505973).sum := by decide
  have hdescent : baseEnd_5505973 < baseStart_5505973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5505973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506034 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5506034 : Nat := 118140960795 + 5506034 * 2 ^ 59
def prefixEnd_5506034 : Nat := 4983230072969 + 3 ^ 40 * 5506034 * 2
def baseEnd_5506034 : Nat := 2827241941997815850353217

theorem tailTrace_5506034 : CollatzResearch.WordTrace tailWord_5506034 prefixEnd_5506034 2827241941997815850353217 := by
  unfold tailWord_5506034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50205389533646662146691289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133881038756391099057843437 50205389533646662146691289)
  ·
    refine ⟨37654042150234996610018467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50205389533646662146691289 37654042150234996610018467)
    ·
      refine ⟨56481063225352494915027701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37654042150234996610018467 56481063225352494915027701)
      ·
        refine ⟨5295099677376796398283847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56481063225352494915027701 5295099677376796398283847)
        ·
          refine ⟨7942649516065194597425771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295099677376796398283847 7942649516065194597425771)
          ·
            refine ⟨11913974274097791896138657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942649516065194597425771 11913974274097791896138657)
            ·
              refine ⟨8935480705573343922103993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11913974274097791896138657 8935480705573343922103993)
              ·
                refine ⟨6701610529180007941577995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8935480705573343922103993 6701610529180007941577995)
                ·
                  refine ⟨10052415793770011912366993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701610529180007941577995 10052415793770011912366993)
                  ·
                    refine ⟨7539311845327508934275245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10052415793770011912366993 7539311845327508934275245)
                    ·
                      refine ⟨2827241941997815850353217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7539311845327508934275245 2827241941997815850353217)
                      ·
                        rfl

theorem cell23_5506034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5506034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506034 prefixEnd_5506034 := by exact prefixLift 5506034
  have htrace : WordTrace (prefixWord ++ tailWord_5506034) baseStart_5506034 baseEnd_5506034 := by
    simpa [prefixWord, tailWord_5506034, baseEnd_5506034] using wordTrace_append hprefix tailTrace_5506034
  have hstable : (prefixWord ++ tailWord_5506034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506034).length < 2 ^ (prefixWord ++ tailWord_5506034).sum := by decide
  have hdescent : baseEnd_5506034 < baseStart_5506034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506103 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_5506103 : Nat := 118140960795 + 5506103 * 2 ^ 59
def prefixEnd_5506103 : Nat := 4983230072969 + 3 ^ 40 * 5506103 * 2
def baseEnd_5506103 : Nat := 2827277372162976080390399

theorem tailTrace_5506103 : CollatzResearch.WordTrace tailWord_5506103 prefixEnd_5506103 2827277372162976080390399 := by
  unfold tailWord_5506103
  simp only [CollatzResearch.WordTrace]
  refine ⟨200824074771336673371026963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133882716514224448914017975 200824074771336673371026963)
  ·
    refine ⟨301236112157005010056540445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200824074771336673371026963 301236112157005010056540445)
    ·
      refine ⟨112963542058876878771202667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301236112157005010056540445 112963542058876878771202667)
      ·
        refine ⟨169445313088315318156804001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112963542058876878771202667 169445313088315318156804001)
        ·
          refine ⟨127083984816236488617603001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169445313088315318156804001 127083984816236488617603001)
          ·
            refine ⟨95312988612177366463202251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127083984816236488617603001 95312988612177366463202251)
            ·
              refine ⟨142969482918266049694803377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95312988612177366463202251 142969482918266049694803377)
              ·
                refine ⟨107227112188699537271102533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142969482918266049694803377 107227112188699537271102533)
                ·
                  refine ⟨20105083535381163238331725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107227112188699537271102533 20105083535381163238331725)
                  ·
                    refine ⟨7539406325767936214374397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20105083535381163238331725 7539406325767936214374397)
                    ·
                      refine ⟨2827277372162976080390399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7539406325767936214374397 2827277372162976080390399)
                      ·
                        rfl

theorem cell23_5506103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_5506103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506103 prefixEnd_5506103 := by exact prefixLift 5506103
  have htrace : WordTrace (prefixWord ++ tailWord_5506103) baseStart_5506103 baseEnd_5506103 := by
    simpa [prefixWord, tailWord_5506103, baseEnd_5506103] using wordTrace_append hprefix tailTrace_5506103
  have hstable : (prefixWord ++ tailWord_5506103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506103).length < 2 ^ (prefixWord ++ tailWord_5506103).sum := by decide
  have hdescent : baseEnd_5506103 < baseStart_5506103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506133 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5506133 : Nat := 118140960795 + 5506133 * 2 ^ 59
def prefixEnd_5506133 : Nat := 4983230072969 + 3 ^ 40 * 5506133 * 2
def baseEnd_5506133 : Nat := 2827292776582610963015261

theorem tailTrace_5506133 : CollatzResearch.WordTrace tailWord_5506133 prefixEnd_5506133 2827292776582610963015261 := by
  unfold tailWord_5506133
  simp only [CollatzResearch.WordTrace]
  refine ⟨200825168961227988494619053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133883445974151992329746035 200825168961227988494619053)
  ·
    refine ⟨75309438360460495685482145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200825168961227988494619053 75309438360460495685482145)
    ·
      refine ⟨56482078770345371764111609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75309438360460495685482145 56482078770345371764111609)
      ·
        refine ⟨42361559077759028823083707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56482078770345371764111609 42361559077759028823083707)
        ·
          refine ⟨63542338616638543234625561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42361559077759028823083707 63542338616638543234625561)
          ·
            refine ⟨47656753962478907425969171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63542338616638543234625561 47656753962478907425969171)
            ·
              refine ⟨71485130943718361138953757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47656753962478907425969171 71485130943718361138953757)
              ·
                refine ⟨26806924103894385427107659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71485130943718361138953757 26806924103894385427107659)
                ·
                  refine ⟨40210386155841578140661489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26806924103894385427107659 40210386155841578140661489)
                  ·
                    refine ⟨30157789616881183605496117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40210386155841578140661489 30157789616881183605496117)
                    ·
                      refine ⟨2827292776582610963015261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30157789616881183605496117 2827292776582610963015261)
                      ·
                        rfl

theorem cell23_5506133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5506133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506133 prefixEnd_5506133 := by exact prefixLift 5506133
  have htrace : WordTrace (prefixWord ++ tailWord_5506133) baseStart_5506133 baseEnd_5506133 := by
    simpa [prefixWord, tailWord_5506133, baseEnd_5506133] using wordTrace_append hprefix tailTrace_5506133
  have hstable : (prefixWord ++ tailWord_5506133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506133).length < 2 ^ (prefixWord ++ tailWord_5506133).sum := by decide
  have hdescent : baseEnd_5506133 < baseStart_5506133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506134 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5506134 : Nat := 118140960795 + 5506134 * 2 ^ 59
def prefixEnd_5506134 : Nat := 4983230072969 + 3 ^ 40 * 5506134 * 2
def baseEnd_5506134 : Nat := 2827293290063265459102757

theorem tailTrace_5506134 : CollatzResearch.WordTrace tailWord_5506134 prefixEnd_5506134 2827293290063265459102757 := by
  unfold tailWord_5506134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551575339639022854087841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133883470289482910443603637 12551575339639022854087841)
  ·
    refine ⟨9413681504729267140565881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12551575339639022854087841 9413681504729267140565881)
    ·
      refine ⟨7060261128546950355424411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9413681504729267140565881 7060261128546950355424411)
      ·
        refine ⟨10590391692820425533136617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7060261128546950355424411 10590391692820425533136617)
        ·
          refine ⟨7942793769615319149852463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10590391692820425533136617 7942793769615319149852463)
          ·
            refine ⟨11914190654422978724778695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942793769615319149852463 11914190654422978724778695)
            ·
              refine ⟨17871285981634468087168043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11914190654422978724778695 17871285981634468087168043)
              ·
                refine ⟨26806928972451702130752065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17871285981634468087168043 26806928972451702130752065)
                ·
                  refine ⟨20105196729338776598064049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26806928972451702130752065 20105196729338776598064049)
                  ·
                    refine ⟨15078897547004082448548037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20105196729338776598064049 15078897547004082448548037)
                    ·
                      refine ⟨2827293290063265459102757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15078897547004082448548037 2827293290063265459102757)
                      ·
                        rfl

theorem cell23_5506134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5506134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506134 prefixEnd_5506134 := by exact prefixLift 5506134
  have htrace : WordTrace (prefixWord ++ tailWord_5506134) baseStart_5506134 baseEnd_5506134 := by
    simpa [prefixWord, tailWord_5506134, baseEnd_5506134] using wordTrace_append hprefix tailTrace_5506134
  have hstable : (prefixWord ++ tailWord_5506134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506134).length < 2 ^ (prefixWord ++ tailWord_5506134).sum := by decide
  have hdescent : baseEnd_5506134 < baseStart_5506134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506143 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_5506143 : Nat := 118140960795 + 5506143 * 2 ^ 59
def prefixEnd_5506143 : Nat := 4983230072969 + 3 ^ 40 * 5506143 * 2
def baseEnd_5506143 : Nat := 2827297911389155923890215

theorem tailTrace_5506143 : CollatzResearch.WordTrace tailWord_5506143 prefixEnd_5506143 2827297911389155923890215 := by
  unfold tailWord_5506143
  simp only [CollatzResearch.WordTrace]
  refine ⟨200825533691191760202483083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133883689127461173468322055 200825533691191760202483083)
  ·
    refine ⟨301238300536787640303724625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200825533691191760202483083 301238300536787640303724625)
    ·
      refine ⟨225928725402590730227793469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301238300536787640303724625 225928725402590730227793469)
      ·
        refine ⟨84723272025971523835422551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225928725402590730227793469 84723272025971523835422551)
        ·
          refine ⟨127084908038957285753133827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84723272025971523835422551 127084908038957285753133827)
          ·
            refine ⟨190627362058435928629700741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127084908038957285753133827 190627362058435928629700741)
            ·
              refine ⟨35742630385956736618068889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190627362058435928629700741 35742630385956736618068889)
              ·
                refine ⟨26806972789467552463551667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35742630385956736618068889 26806972789467552463551667)
                ·
                  refine ⟨40210459184201328695327501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26806972789467552463551667 40210459184201328695327501)
                  ·
                    refine ⟨15078922194075498260747813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40210459184201328695327501 15078922194075498260747813)
                    ·
                      refine ⟨2827297911389155923890215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15078922194075498260747813 2827297911389155923890215)
                      ·
                        rfl

theorem cell23_5506143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_5506143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506143 prefixEnd_5506143 := by exact prefixLift 5506143
  have htrace : WordTrace (prefixWord ++ tailWord_5506143) baseStart_5506143 baseEnd_5506143 := by
    simpa [prefixWord, tailWord_5506143, baseEnd_5506143] using wordTrace_append hprefix tailTrace_5506143
  have hstable : (prefixWord ++ tailWord_5506143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506143).length < 2 ^ (prefixWord ++ tailWord_5506143).sum := by decide
  have hdescent : baseEnd_5506143 < baseStart_5506143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506157 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_5506157 : Nat := 118140960795 + 5506157 * 2 ^ 59
def prefixEnd_5506157 : Nat := 4983230072969 + 3 ^ 40 * 5506157 * 2
def baseEnd_5506157 : Nat := 942435033372772956371717

theorem tailTrace_5506157 : CollatzResearch.WordTrace tailWord_5506157 prefixEnd_5506157 942435033372772956371717 := by
  unfold tailWord_5506157
  simp only [CollatzResearch.WordTrace]
  refine ⟨200826044313141040593492725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133884029542094027062328483 200826044313141040593492725)
  ·
    refine ⟨18827441654356972555639943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200826044313141040593492725 18827441654356972555639943)
    ·
      refine ⟨28241162481535458833459915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18827441654356972555639943 28241162481535458833459915)
      ·
        refine ⟨42361743722303188250189873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28241162481535458833459915 42361743722303188250189873)
        ·
          refine ⟨31771307791727391187642405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42361743722303188250189873 31771307791727391187642405)
          ·
            refine ⟨5957120210948885847682951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31771307791727391187642405 5957120210948885847682951)
            ·
              refine ⟨8935680316423328771524427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957120210948885847682951 8935680316423328771524427)
              ·
                refine ⟨13403520474634993157286641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8935680316423328771524427 13403520474634993157286641)
                ·
                  refine ⟨10052640355976244867964981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13403520474634993157286641 10052640355976244867964981)
                  ·
                    refine ⟨942435033372772956371717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10052640355976244867964981 942435033372772956371717)
                    ·
                      rfl

theorem cell23_5506157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_5506157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506157 prefixEnd_5506157 := by exact prefixLift 5506157
  have htrace : WordTrace (prefixWord ++ tailWord_5506157) baseStart_5506157 baseEnd_5506157 := by
    simpa [prefixWord, tailWord_5506157, baseEnd_5506157] using wordTrace_append hprefix tailTrace_5506157
  have hstable : (prefixWord ++ tailWord_5506157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506157).length < 2 ^ (prefixWord ++ tailWord_5506157).sum := by decide
  have hdescent : baseEnd_5506157 < baseStart_5506157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506160 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2]
def baseStart_5506160 : Nat := 118140960795 + 5506160 * 2 ^ 59
def prefixEnd_5506160 : Nat := 4983230072969 + 3 ^ 40 * 5506160 * 2
def baseEnd_5506160 : Nat := 2827306640560282357377637

theorem tailTrace_5506160 : CollatzResearch.WordTrace tailWord_5506160 prefixEnd_5506160 2827306640560282357377637 := by
  unfold tailWord_5506160
  simp only [CollatzResearch.WordTrace]
  refine ⟨100413076866065086052925967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133884102488086781403901289 100413076866065086052925967)
  ·
    refine ⟨150619615299097629079388951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100413076866065086052925967 150619615299097629079388951)
    ·
      refine ⟨225929422948646443619083427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150619615299097629079388951 225929422948646443619083427)
      ·
        refine ⟨338894134422969665428625141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225929422948646443619083427 338894134422969665428625141)
        ·
          refine ⟨31771325102153406133933607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338894134422969665428625141 31771325102153406133933607)
          ·
            refine ⟨47656987653230109200900411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31771325102153406133933607 47656987653230109200900411)
            ·
              refine ⟨71485481479845163801350617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47656987653230109200900411 71485481479845163801350617)
              ·
                refine ⟨53614111109883872851012963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71485481479845163801350617 53614111109883872851012963)
                ·
                  refine ⟨80421166664825809276519445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53614111109883872851012963 80421166664825809276519445)
                  ·
                    refine ⟨3769742187413709809836849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80421166664825809276519445 3769742187413709809836849)
                    ·
                      refine ⟨2827306640560282357377637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769742187413709809836849 2827306640560282357377637)
                      ·
                        rfl

theorem cell23_5506160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2].length) (baseStart_5506160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506160 prefixEnd_5506160 := by exact prefixLift 5506160
  have htrace : WordTrace (prefixWord ++ tailWord_5506160) baseStart_5506160 baseEnd_5506160 := by
    simpa [prefixWord, tailWord_5506160, baseEnd_5506160] using wordTrace_append hprefix tailTrace_5506160
  have hstable : (prefixWord ++ tailWord_5506160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506160).length < 2 ^ (prefixWord ++ tailWord_5506160).sum := by decide
  have hdescent : baseEnd_5506160 < baseStart_5506160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506173 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_5506173 : Nat := 118140960795 + 5506173 * 2 ^ 59
def prefixEnd_5506173 : Nat := 4983230072969 + 3 ^ 40 * 5506173 * 2
def baseEnd_5506173 : Nat := 2827313315808790806515077

theorem tailTrace_5506173 : CollatzResearch.WordTrace tailWord_5506173 prefixEnd_5506173 2827313315808790806515077 := by
  unfold tailWord_5506173
  simp only [CollatzResearch.WordTrace]
  refine ⟨200826627881083075326075173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133884418587388716884050115 200826627881083075326075173)
  ·
    refine ⟨37654992727703076623639095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200826627881083075326075173 37654992727703076623639095)
    ·
      refine ⟨56482489091554614935458643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37654992727703076623639095 56482489091554614935458643)
      ·
        refine ⟨84723733637331922403187965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56482489091554614935458643 84723733637331922403187965)
        ·
          refine ⟨31771400113999470901195487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84723733637331922403187965 31771400113999470901195487)
          ·
            refine ⟨47657100170999206351793231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31771400113999470901195487 47657100170999206351793231)
            ·
              refine ⟨71485650256498809527689847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47657100170999206351793231 71485650256498809527689847)
              ·
                refine ⟨107228475384748214291534771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71485650256498809527689847 107228475384748214291534771)
                ·
                  refine ⟨160842713077122321437302157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107228475384748214291534771 160842713077122321437302157)
                  ·
                    refine ⟨60316017403920870538988309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160842713077122321437302157 60316017403920870538988309)
                    ·
                      refine ⟨2827313315808790806515077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60316017403920870538988309 2827313315808790806515077)
                      ·
                        rfl

theorem cell23_5506173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_5506173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506173 prefixEnd_5506173 := by exact prefixLift 5506173
  have htrace : WordTrace (prefixWord ++ tailWord_5506173) baseStart_5506173 baseEnd_5506173 := by
    simpa [prefixWord, tailWord_5506173, baseEnd_5506173] using wordTrace_append hprefix tailTrace_5506173
  have hstable : (prefixWord ++ tailWord_5506173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506173).length < 2 ^ (prefixWord ++ tailWord_5506173).sum := by decide
  have hdescent : baseEnd_5506173 < baseStart_5506173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506177 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_5506177 : Nat := 118140960795 + 5506177 * 2 ^ 59
def prefixEnd_5506177 : Nat := 4983230072969 + 3 ^ 40 * 5506177 * 2
def baseEnd_5506177 : Nat := 2827315369731408790865059

theorem tailTrace_5506177 : CollatzResearch.WordTrace tailWord_5506177 prefixEnd_5506177 2827315369731408790865059 := by
  unfold tailWord_5506177
  simp only [CollatzResearch.WordTrace]
  refine ⟨200826773773068584009220785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133884515848712389339480523 200826773773068584009220785)
  ·
    refine ⟨150620080329801438006915589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200826773773068584009220785 150620080329801438006915589)
    ·
      refine ⟨28241265061837769626296673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150620080329801438006915589 28241265061837769626296673)
      ·
        refine ⟨21180948796378327219722505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28241265061837769626296673 21180948796378327219722505)
        ·
          refine ⟨15885711597283745414791879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21180948796378327219722505 15885711597283745414791879)
          ·
            refine ⟨23828567395925618122187819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15885711597283745414791879 23828567395925618122187819)
            ·
              refine ⟨35742851093888427183281729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23828567395925618122187819 35742851093888427183281729)
              ·
                refine ⟨26807138320416320387461297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35742851093888427183281729 26807138320416320387461297)
                ·
                  refine ⟨20105353740312240290595973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26807138320416320387461297 20105353740312240290595973)
                  ·
                    refine ⟨3769753826308545054486745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20105353740312240290595973 3769753826308545054486745)
                    ·
                      refine ⟨2827315369731408790865059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769753826308545054486745 2827315369731408790865059)
                      ·
                        rfl

theorem cell23_5506177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_5506177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506177 prefixEnd_5506177 := by exact prefixLift 5506177
  have htrace : WordTrace (prefixWord ++ tailWord_5506177) baseStart_5506177 baseEnd_5506177 := by
    simpa [prefixWord, tailWord_5506177, baseEnd_5506177] using wordTrace_append hprefix tailTrace_5506177
  have hstable : (prefixWord ++ tailWord_5506177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506177).length < 2 ^ (prefixWord ++ tailWord_5506177).sum := by decide
  have hdescent : baseEnd_5506177 < baseStart_5506177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506237 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_5506237 : Nat := 118140960795 + 5506237 * 2 ^ 59
def prefixEnd_5506237 : Nat := 4983230072969 + 3 ^ 40 * 5506237 * 2
def baseEnd_5506237 : Nat := 2827346178570678556114783

theorem tailTrace_5506237 : CollatzResearch.WordTrace tailWord_5506237 prefixEnd_5506237 2827346178570678556114783 := by
  unfold tailWord_5506237
  simp only [CollatzResearch.WordTrace]
  refine ⟨200828962152851214256404965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133885974768567476170936643 200828962152851214256404965)
  ·
    refine ⟨37655430403659602673075931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200828962152851214256404965 37655430403659602673075931)
    ·
      refine ⟨56483145605489404009613897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37655430403659602673075931 56483145605489404009613897)
      ·
        refine ⟨42362359204117053007210423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56483145605489404009613897 42362359204117053007210423)
        ·
          refine ⟨63543538806175579510815635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42362359204117053007210423 63543538806175579510815635)
          ·
            refine ⟨95315308209263369266223453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63543538806175579510815635 95315308209263369266223453)
            ·
              refine ⟨35743240578473763474833795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95315308209263369266223453 35743240578473763474833795)
              ·
                refine ⟨53614860867710645212250693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35743240578473763474833795 53614860867710645212250693)
                ·
                  refine ⟨10052786412695745977297005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53614860867710645212250693 10052786412695745977297005)
                  ·
                    refine ⟨3769794904760904741486377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10052786412695745977297005 3769794904760904741486377)
                    ·
                      refine ⟨2827346178570678556114783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769794904760904741486377 2827346178570678556114783)
                      ·
                        rfl

theorem cell23_5506237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_5506237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506237 prefixEnd_5506237 := by exact prefixLift 5506237
  have htrace : WordTrace (prefixWord ++ tailWord_5506237) baseStart_5506237 baseEnd_5506237 := by
    simpa [prefixWord, tailWord_5506237, baseEnd_5506237] using wordTrace_append hprefix tailTrace_5506237
  have hstable : (prefixWord ++ tailWord_5506237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506237).length < 2 ^ (prefixWord ++ tailWord_5506237).sum := by decide
  have hdescent : baseEnd_5506237 < baseStart_5506237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 5, 6]
def baseStart_5506243 : Nat := 118140960795 + 5506243 * 2 ^ 59
def prefixEnd_5506243 : Nat := 4983230072969 + 3 ^ 40 * 5506243 * 2
def baseEnd_5506243 : Nat := 942449753151535177546585

theorem tailTrace_5506243 : CollatzResearch.WordTrace tailWord_5506243 prefixEnd_5506243 942449753151535177546585 := by
  unfold tailWord_5506243
  simp only [CollatzResearch.WordTrace]
  refine ⟨200829180990829477281123383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133886120660552984854082255 200829180990829477281123383)
  ·
    refine ⟨301243771486244215921685075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200829180990829477281123383 301243771486244215921685075)
    ·
      refine ⟨451865657229366323882527613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301243771486244215921685075 451865657229366323882527613)
      ·
        refine ⟨169449621461012371455947855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451865657229366323882527613 169449621461012371455947855)
        ·
          refine ⟨254174432191518557183921783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169449621461012371455947855 254174432191518557183921783)
          ·
            refine ⟨381261648287277835775882675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254174432191518557183921783 381261648287277835775882675)
            ·
              refine ⟨571892472430916753663824013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381261648287277835775882675 571892472430916753663824013)
              ·
                refine ⟨214459677161593782623934005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571892472430916753663824013 214459677161593782623934005)
                ·
                  refine ⟨20105594733899417120993813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214459677161593782623934005 20105594733899417120993813)
                  ·
                    refine ⟨942449753151535177546585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20105594733899417120993813 942449753151535177546585)
                    ·
                      rfl

theorem cell23_5506243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_5506243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506243 prefixEnd_5506243 := by exact prefixLift 5506243
  have htrace : WordTrace (prefixWord ++ tailWord_5506243) baseStart_5506243 baseEnd_5506243 := by
    simpa [prefixWord, tailWord_5506243, baseEnd_5506243] using wordTrace_append hprefix tailTrace_5506243
  have hstable : (prefixWord ++ tailWord_5506243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506243).length < 2 ^ (prefixWord ++ tailWord_5506243).sum := by decide
  have hdescent : baseEnd_5506243 < baseStart_5506243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506264 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_5506264 : Nat := 118140960795 + 5506264 * 2 ^ 59
def prefixEnd_5506264 : Nat := 4983230072969 + 3 ^ 40 * 5506264 * 2
def baseEnd_5506264 : Nat := 942453347516116650159053

theorem tailTrace_5506264 : CollatzResearch.WordTrace tailWord_5506264 prefixEnd_5506264 942453347516116650159053 := by
  unfold tailWord_5506264
  simp only [CollatzResearch.WordTrace]
  refine ⟨100414973461876698933818923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133886631282502265245091897 100414973461876698933818923)
  ·
    refine ⟨150622460192815048400728385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100414973461876698933818923 150622460192815048400728385)
    ·
      refine ⟨112966845144611286300546289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150622460192815048400728385 112966845144611286300546289)
      ·
        refine ⟨84725133858458464725409717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112966845144611286300546289 84725133858458464725409717)
        ·
          refine ⟨7942981299230481068007161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84725133858458464725409717 7942981299230481068007161)
          ·
            refine ⟨5957235974422860801005371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7942981299230481068007161 5957235974422860801005371)
            ·
              refine ⟨8935853961634291201508057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957235974422860801005371 8935853961634291201508057)
              ·
                refine ⟨6701890471225718401131043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8935853961634291201508057 6701890471225718401131043)
                ·
                  refine ⟨10052835706838577601696565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701890471225718401131043 10052835706838577601696565)
                  ·
                    refine ⟨942453347516116650159053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10052835706838577601696565 942453347516116650159053)
                    ·
                      rfl

theorem cell23_5506264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_5506264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506264 prefixEnd_5506264 := by exact prefixLift 5506264
  have htrace : WordTrace (prefixWord ++ tailWord_5506264) baseStart_5506264 baseEnd_5506264 := by
    simpa [prefixWord, tailWord_5506264, baseEnd_5506264] using wordTrace_append hprefix tailTrace_5506264
  have hstable : (prefixWord ++ tailWord_5506264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506264).length < 2 ^ (prefixWord ++ tailWord_5506264).sum := by decide
  have hdescent : baseEnd_5506264 < baseStart_5506264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506277 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_5506277 : Nat := 118140960795 + 5506277 * 2 ^ 59
def prefixEnd_5506277 : Nat := 4983230072969 + 3 ^ 40 * 5506277 * 2
def baseEnd_5506277 : Nat := 942455572598952799871533

theorem tailTrace_5506277 : CollatzResearch.WordTrace tailWord_5506277 prefixEnd_5506277 942455572598952799871533 := by
  unfold tailWord_5506277
  simp only [CollatzResearch.WordTrace]
  refine ⟨200830421072706301087861085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133886947381804200725240723 200830421072706301087861085)
  ·
    refine ⟨75311407902264862907947907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200830421072706301087861085 75311407902264862907947907)
    ·
      refine ⟨112967111853397294361921861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75311407902264862907947907 112967111853397294361921861)
      ·
        refine ⟨21181333472511992692860349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112967111853397294361921861 21181333472511992692860349)
        ·
          refine ⟨7943000052191997259822631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21181333472511992692860349 7943000052191997259822631)
          ·
            refine ⟨11914500078287995889733947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943000052191997259822631 11914500078287995889733947)
            ·
              refine ⟨17871750117431993834600921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11914500078287995889733947 17871750117431993834600921)
              ·
                refine ⟨13403812588073995375950691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17871750117431993834600921 13403812588073995375950691)
                ·
                  refine ⟨20105718882110993063926037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13403812588073995375950691 20105718882110993063926037)
                  ·
                    refine ⟨942455572598952799871533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20105718882110993063926037 942455572598952799871533)
                    ·
                      rfl

theorem cell23_5506277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_5506277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506277 prefixEnd_5506277 := by exact prefixLift 5506277
  have htrace : WordTrace (prefixWord ++ tailWord_5506277) baseStart_5506277 baseEnd_5506277 := by
    simpa [prefixWord, tailWord_5506277, baseEnd_5506277] using wordTrace_append hprefix tailTrace_5506277
  have hstable : (prefixWord ++ tailWord_5506277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506277).length < 2 ^ (prefixWord ++ tailWord_5506277).sum := by decide
  have hdescent : baseEnd_5506277 < baseStart_5506277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506284 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_5506284 : Nat := 118140960795 + 5506284 * 2 ^ 59
def prefixEnd_5506284 : Nat := 4983230072969 + 3 ^ 40 * 5506284 * 2
def baseEnd_5506284 : Nat := 2827370312161439872227067

theorem tailTrace_5506284 : CollatzResearch.WordTrace tailWord_5506284 prefixEnd_5506284 2827370312161439872227067 := by
  unfold tailWord_5506284
  simp only [CollatzResearch.WordTrace]
  refine ⟨100415338191840470641682953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133887117589120627522243937 100415338191840470641682953)
  ·
    refine ⟨75311503643880352981262215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100415338191840470641682953 75311503643880352981262215)
    ·
      refine ⟨112967255465820529471893323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75311503643880352981262215 112967255465820529471893323)
      ·
        refine ⟨169450883198730794207839985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112967255465820529471893323 169450883198730794207839985)
        ·
          refine ⟨127088162399048095655879989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169450883198730794207839985 127088162399048095655879989)
          ·
            refine ⟨11914515224910758967738749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127088162399048095655879989 11914515224910758967738749)
            ·
              refine ⟨4467943209341534612902031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11914515224910758967738749 4467943209341534612902031)
              ·
                refine ⟨6701914814012301919353047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467943209341534612902031 6701914814012301919353047)
                ·
                  refine ⟨10052872221018452879029571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701914814012301919353047 10052872221018452879029571)
                  ·
                    refine ⟨15079308331527679318544357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10052872221018452879029571 15079308331527679318544357)
                    ·
                      refine ⟨2827370312161439872227067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15079308331527679318544357 2827370312161439872227067)
                      ·
                        rfl

theorem cell23_5506284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_5506284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506284 prefixEnd_5506284 := by exact prefixLift 5506284
  have htrace : WordTrace (prefixWord ++ tailWord_5506284) baseStart_5506284 baseEnd_5506284 := by
    simpa [prefixWord, tailWord_5506284, baseEnd_5506284] using wordTrace_append hprefix tailTrace_5506284
  have hstable : (prefixWord ++ tailWord_5506284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506284).length < 2 ^ (prefixWord ++ tailWord_5506284).sum := by decide
  have hdescent : baseEnd_5506284 < baseStart_5506284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506290 : List Nat := [3, 2, 1, 3, 3, 11]
def baseStart_5506290 : Nat := 118140960795 + 5506290 * 2 ^ 59
def prefixEnd_5506290 : Nat := 4983230072969 + 3 ^ 40 * 5506290 * 2
def baseEnd_5506290 : Nat := 11635281452861591970173

theorem tailTrace_5506290 : CollatzResearch.WordTrace tailWord_5506290 prefixEnd_5506290 11635281452861591970173 := by
  unfold tailWord_5506290
  simp only [CollatzResearch.WordTrace]
  refine ⟨50207723805414801077021081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133887263481106136205389549 50207723805414801077021081)
  ·
    refine ⟨37655792854061100807765811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50207723805414801077021081 37655792854061100807765811)
    ·
      refine ⟨56483689281091651211648717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37655792854061100807765811 56483689281091651211648717)
      ·
        refine ⟨21181383480409369204368269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56483689281091651211648717 21181383480409369204368269)
        ·
          refine ⟨7943018805153513451638101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21181383480409369204368269 7943018805153513451638101)
          ·
            refine ⟨11635281452861591970173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7943018805153513451638101 11635281452861591970173)
            ·
              rfl

theorem cell23_5506290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 11].length) (baseStart_5506290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506290 prefixEnd_5506290 := by exact prefixLift 5506290
  have htrace : WordTrace (prefixWord ++ tailWord_5506290) baseStart_5506290 baseEnd_5506290 := by
    simpa [prefixWord, tailWord_5506290, baseEnd_5506290] using wordTrace_append hprefix tailTrace_5506290
  have hstable : (prefixWord ++ tailWord_5506290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506290).length < 2 ^ (prefixWord ++ tailWord_5506290).sum := by decide
  have hdescent : baseEnd_5506290 < baseStart_5506290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506338 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_5506338 : Nat := 118140960795 + 5506338 * 2 ^ 59
def prefixEnd_5506338 : Nat := 4983230072969 + 3 ^ 40 * 5506338 * 2
def baseEnd_5506338 : Nat := 2827398040116782660951819

theorem tailTrace_5506338 : CollatzResearch.WordTrace tailWord_5506338 prefixEnd_5506338 2827398040116782660951819 := by
  unfold tailWord_5506338
  simp only [CollatzResearch.WordTrace]
  refine ⟨50208161481371327126457917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133888430616990205670554445 50208161481371327126457917)
  ·
    refine ⟨18828060555514247672421719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50208161481371327126457917 18828060555514247672421719)
    ·
      refine ⟨28242090833271371508632579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18828060555514247672421719 28242090833271371508632579)
      ·
        refine ⟨42363136249907057262948869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28242090833271371508632579 42363136249907057262948869)
        ·
          refine ⟨7943088046857573236802913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42363136249907057262948869 7943088046857573236802913)
          ·
            refine ⟨5957316035143179927602185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7943088046857573236802913 5957316035143179927602185)
            ·
              refine ⟨4467987026357384945701639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5957316035143179927602185 4467987026357384945701639)
              ·
                refine ⟨6701980539536077418552459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4467987026357384945701639 6701980539536077418552459)
                ·
                  refine ⟨10052970809304116127828689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6701980539536077418552459 10052970809304116127828689)
                  ·
                    refine ⟨7539728106978087095871517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10052970809304116127828689 7539728106978087095871517)
                    ·
                      refine ⟨2827398040116782660951819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7539728106978087095871517 2827398040116782660951819)
                      ·
                        rfl

theorem cell23_5506338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_5506338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506338 prefixEnd_5506338 := by exact prefixLift 5506338
  have htrace : WordTrace (prefixWord ++ tailWord_5506338) baseStart_5506338 baseEnd_5506338 := by
    simpa [prefixWord, tailWord_5506338, baseEnd_5506338] using wordTrace_append hprefix tailTrace_5506338
  have hstable : (prefixWord ++ tailWord_5506338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506338).length < 2 ^ (prefixWord ++ tailWord_5506338).sum := by decide
  have hdescent : baseEnd_5506338 < baseStart_5506338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506360 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_5506360 : Nat := 118140960795 + 5506360 * 2 ^ 59
def prefixEnd_5506360 : Nat := 4983230072969 + 3 ^ 40 * 5506360 * 2
def baseEnd_5506360 : Nat := 2827409336691181574876717

theorem tailTrace_5506360 : CollatzResearch.WordTrace tailWord_5506360 prefixEnd_5506360 2827409336691181574876717 := by
  unfold tailWord_5506360
  simp only [CollatzResearch.WordTrace]
  refine ⟨100416724165702803131566267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133888965554270404175421689 100416724165702803131566267)
  ·
    refine ⟨150625086248554204697349401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100416724165702803131566267 150625086248554204697349401)
    ·
      refine ⟨112968814686415653523012051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150625086248554204697349401 112968814686415653523012051)
      ·
        refine ⟨169453222029623480284518077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112968814686415653523012051 169453222029623480284518077)
        ·
          refine ⟨63544958261108805106694279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169453222029623480284518077 63544958261108805106694279)
          ·
            refine ⟨95317437391663207660041419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63544958261108805106694279 95317437391663207660041419)
            ·
              refine ⟨142976156087494811490062129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95317437391663207660041419 142976156087494811490062129)
              ·
                refine ⟨107232117065621108617546597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142976156087494811490062129 107232117065621108617546597)
                ·
                  refine ⟨20106021949803957865789987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107232117065621108617546597 20106021949803957865789987)
                  ·
                    refine ⟨30159032924705936798684981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20106021949803957865789987 30159032924705936798684981)
                    ·
                      refine ⟨2827409336691181574876717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30159032924705936798684981 2827409336691181574876717)
                      ·
                        rfl

theorem cell23_5506360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_5506360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506360 prefixEnd_5506360 := by exact prefixLift 5506360
  have htrace : WordTrace (prefixWord ++ tailWord_5506360) baseStart_5506360 baseEnd_5506360 := by
    simpa [prefixWord, tailWord_5506360, baseEnd_5506360] using wordTrace_append hprefix tailTrace_5506360
  have hstable : (prefixWord ++ tailWord_5506360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506360).length < 2 ^ (prefixWord ++ tailWord_5506360).sum := by decide
  have hdescent : baseEnd_5506360 < baseStart_5506360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506464 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2]
def baseStart_5506464 : Nat := 118140960795 + 5506464 * 2 ^ 59
def prefixEnd_5506464 : Nat := 4983230072969 + 3 ^ 40 * 5506464 * 2
def baseEnd_5506464 : Nat := 2827462738679249167976239

theorem tailTrace_5506464 : CollatzResearch.WordTrace tailWord_5506464 prefixEnd_5506464 2827462738679249167976239 := by
  unfold tailWord_5506464
  simp only [CollatzResearch.WordTrace]
  refine ⟨100418620761514416012459223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133891494348685888016612297 100418620761514416012459223)
  ·
    refine ⟨150627931142271624018688835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100418620761514416012459223 150627931142271624018688835)
    ·
      refine ⟨225941896713407436028033253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150627931142271624018688835 225941896713407436028033253)
      ·
        refine ⟨42364105633763894255256235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225941896713407436028033253 42364105633763894255256235)
        ·
          refine ⟨63546158450645841382884353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42364105633763894255256235 63546158450645841382884353)
          ·
            refine ⟨47659618837984381037163265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63546158450645841382884353 47659618837984381037163265)
            ·
              refine ⟨35744714128488285777872449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47659618837984381037163265 35744714128488285777872449)
              ·
                refine ⟨26808535596366214333404337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35744714128488285777872449 26808535596366214333404337)
                ·
                  refine ⟨20106401697274660750053253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26808535596366214333404337 20106401697274660750053253)
                  ·
                    refine ⟨3769950318238998890634985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20106401697274660750053253 3769950318238998890634985)
                    ·
                      refine ⟨2827462738679249167976239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3769950318238998890634985 2827462738679249167976239)
                      ·
                        rfl

theorem cell23_5506464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_5506464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506464 prefixEnd_5506464 := by exact prefixLift 5506464
  have htrace : WordTrace (prefixWord ++ tailWord_5506464) baseStart_5506464 baseEnd_5506464 := by
    simpa [prefixWord, tailWord_5506464, baseEnd_5506464] using wordTrace_append hprefix tailTrace_5506464
  have hstable : (prefixWord ++ tailWord_5506464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506464).length < 2 ^ (prefixWord ++ tailWord_5506464).sum := by decide
  have hdescent : baseEnd_5506464 < baseStart_5506464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506487 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 6]
def baseStart_5506487 : Nat := 118140960795 + 5506487 * 2 ^ 59
def prefixEnd_5506487 : Nat := 4983230072969 + 3 ^ 40 * 5506487 * 2
def baseEnd_5506487 : Nat := 314163838748255841998737

theorem tailTrace_5506487 : CollatzResearch.WordTrace tailWord_5506487 prefixEnd_5506487 314163838748255841998737 := by
  unfold tailWord_5506487
  simp only [CollatzResearch.WordTrace]
  refine ⟨200838080401945506953005715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133892053601297004635337143 200838080401945506953005715)
  ·
    refine ⟨301257120602918260429508573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200838080401945506953005715 301257120602918260429508573)
    ·
      refine ⟨112971420226094347661065715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301257120602918260429508573 112971420226094347661065715)
      ·
        refine ⟨169457130339141521491598573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112971420226094347661065715 169457130339141521491598573)
        ·
          refine ⟨63546423877178070559349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169457130339141521491598573 63546423877178070559349465)
          ·
            refine ⟨47659817907883552919512099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63546423877178070559349465 47659817907883552919512099)
            ·
              refine ⟨71489726861825329379268149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47659817907883552919512099 71489726861825329379268149)
              ·
                refine ⟨6702161893296124629306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71489726861825329379268149 6702161893296124629306389)
                ·
                  refine ⟨314163838748255841998737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6702161893296124629306389 314163838748255841998737)
                  ·
                    rfl

theorem cell23_5506487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 6].length) (baseStart_5506487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506487 prefixEnd_5506487 := by exact prefixLift 5506487
  have htrace : WordTrace (prefixWord ++ tailWord_5506487) baseStart_5506487 baseEnd_5506487 := by
    simpa [prefixWord, tailWord_5506487, baseEnd_5506487] using wordTrace_append hprefix tailTrace_5506487
  have hstable : (prefixWord ++ tailWord_5506487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506487).length < 2 ^ (prefixWord ++ tailWord_5506487).sum := by decide
  have hdescent : baseEnd_5506487 < baseStart_5506487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506508 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_5506508 : Nat := 118140960795 + 5506508 * 2 ^ 59
def prefixEnd_5506508 : Nat := 4983230072969 + 3 ^ 40 * 5506508 * 2
def baseEnd_5506508 : Nat := 942495110609348998608679

theorem tailTrace_5506508 : CollatzResearch.WordTrace tailWord_5506508 prefixEnd_5506508 942495110609348998608679 := by
  unfold tailWord_5506508
  simp only [CollatzResearch.WordTrace]
  refine ⟨100419423167434713769760089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133892564223246285026346785 100419423167434713769760089)
  ·
    refine ⟨75314567375576035327320067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100419423167434713769760089 75314567375576035327320067)
    ·
      refine ⟨112971851063364052990980101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75314567375576035327320067 112971851063364052990980101)
      ·
        refine ⟨21182222074380759935808769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112971851063364052990980101 21182222074380759935808769)
        ·
          refine ⟨15886666555785569951856577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21182222074380759935808769 15886666555785569951856577)
          ·
            refine ⟨11914999916839177463892433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15886666555785569951856577 11914999916839177463892433)
            ·
              refine ⟨8936249937629383097919325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11914999916839177463892433 8936249937629383097919325)
              ·
                refine ⟨3351093726611018661719747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8936249937629383097919325 3351093726611018661719747)
                ·
                  refine ⟨5026640589916527992579621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351093726611018661719747 5026640589916527992579621)
                  ·
                    refine ⟨942495110609348998608679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5026640589916527992579621 942495110609348998608679)
                    ·
                      rfl

theorem cell23_5506508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_5506508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506508 prefixEnd_5506508 := by exact prefixLift 5506508
  have htrace : WordTrace (prefixWord ++ tailWord_5506508) baseStart_5506508 baseEnd_5506508 := by
    simpa [prefixWord, tailWord_5506508, baseEnd_5506508] using wordTrace_append hprefix tailTrace_5506508
  have hstable : (prefixWord ++ tailWord_5506508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506508).length < 2 ^ (prefixWord ++ tailWord_5506508).sum := by decide
  have hdescent : baseEnd_5506508 < baseStart_5506508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506531 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 3]
def baseStart_5506531 : Nat := 118140960795 + 5506531 * 2 ^ 59
def prefixEnd_5506531 : Nat := 4983230072969 + 3 ^ 40 * 5506531 * 2
def baseEnd_5506531 : Nat := 2827497141883100405838431

theorem tailTrace_5506531 : CollatzResearch.WordTrace tailWord_5506531 prefixEnd_5506531 2827497141883100405838431 := by
  unfold tailWord_5506531
  simp only [CollatzResearch.WordTrace]
  refine ⟨200839685213786102467607447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133893123475857401645071631 200839685213786102467607447)
  ·
    refine ⟨301259527820679153701411171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200839685213786102467607447 301259527820679153701411171)
    ·
      refine ⟨451889291731018730552116757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301259527820679153701411171 451889291731018730552116757)
      ·
        refine ⟨21182310549891502994630473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 451889291731018730552116757 21182310549891502994630473)
        ·
          refine ⟨15886732912418627245972855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21182310549891502994630473 15886732912418627245972855)
          ·
            refine ⟨23830099368627940868959283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15886732912418627245972855 23830099368627940868959283)
            ·
              refine ⟨35745149052941911303438925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23830099368627940868959283 35745149052941911303438925)
              ·
                refine ⟨13404430894853216738789597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35745149052941911303438925 13404430894853216738789597)
                ·
                  refine ⟨5026661585569956277046099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13404430894853216738789597 5026661585569956277046099)
                  ·
                    refine ⟨7539992378354934415569149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5026661585569956277046099 7539992378354934415569149)
                    ·
                      refine ⟨2827497141883100405838431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7539992378354934415569149 2827497141883100405838431)
                      ·
                        rfl

theorem cell23_5506531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_5506531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506531 prefixEnd_5506531 := by exact prefixLift 5506531
  have htrace : WordTrace (prefixWord ++ tailWord_5506531) baseStart_5506531 baseEnd_5506531 := by
    simpa [prefixWord, tailWord_5506531, baseEnd_5506531] using wordTrace_append hprefix tailTrace_5506531
  have hstable : (prefixWord ++ tailWord_5506531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506531).length < 2 ^ (prefixWord ++ tailWord_5506531).sum := by decide
  have hdescent : baseEnd_5506531 < baseStart_5506531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506547 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 1, 6]
def baseStart_5506547 : Nat := 118140960795 + 5506547 * 2 ^ 59
def prefixEnd_5506547 : Nat := 4983230072969 + 3 ^ 40 * 5506547 * 2
def baseEnd_5506547 : Nat := 942501785857857447746119

theorem tailTrace_5506547 : CollatzResearch.WordTrace tailWord_5506547 prefixEnd_5506547 942501785857857447746119 := by
  unfold tailWord_5506547
  simp only [CollatzResearch.WordTrace]
  refine ⟨200840268781728137200189895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133893512521152091466793263 200840268781728137200189895)
  ·
    refine ⟨301260403172592205800284843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200840268781728137200189895 301260403172592205800284843)
    ·
      refine ⟨451890604758888308700427265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301260403172592205800284843 451890604758888308700427265)
      ·
        refine ⟨338917953569166231525320449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451890604758888308700427265 338917953569166231525320449)
        ·
          refine ⟨254188465176874673643990337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338917953569166231525320449 254188465176874673643990337)
          ·
            refine ⟨190641348882656005232992753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254188465176874673643990337 190641348882656005232992753)
            ·
              refine ⟨142981011661992003924744565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190641348882656005232992753 142981011661992003924744565)
              ·
                refine ⟨13404469843311750367944803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142981011661992003924744565 13404469843311750367944803)
                ·
                  refine ⟨20106704764967625551917205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13404469843311750367944803 20106704764967625551917205)
                  ·
                    refine ⟨942501785857857447746119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20106704764967625551917205 942501785857857447746119)
                    ·
                      rfl

theorem cell23_5506547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 6].length) (baseStart_5506547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506547 prefixEnd_5506547 := by exact prefixLift 5506547
  have htrace : WordTrace (prefixWord ++ tailWord_5506547) baseStart_5506547 baseEnd_5506547 := by
    simpa [prefixWord, tailWord_5506547, baseEnd_5506547] using wordTrace_append hprefix tailTrace_5506547
  have hstable : (prefixWord ++ tailWord_5506547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506547).length < 2 ^ (prefixWord ++ tailWord_5506547).sum := by decide
  have hdescent : baseEnd_5506547 < baseStart_5506547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506554 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_5506554 : Nat := 118140960795 + 5506554 * 2 ^ 59
def prefixEnd_5506554 : Nat := 4983230072969 + 3 ^ 40 * 5506554 * 2
def baseEnd_5506554 : Nat := 2827508951938153815850825

theorem tailTrace_5506554 : CollatzResearch.WordTrace tailWord_5506554 prefixEnd_5506554 2827508951938153815850825 := by
  unfold tailWord_5506554
  simp only [CollatzResearch.WordTrace]
  refine ⟨50210131023175694348923679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133893682728468518263796477 50210131023175694348923679)
  ·
    refine ⟨75315196534763541523385519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50210131023175694348923679 75315196534763541523385519)
    ·
      refine ⟨112972794802145312285078279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75315196534763541523385519 112972794802145312285078279)
      ·
        refine ⟨169459192203217968427617419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112972794802145312285078279 169459192203217968427617419)
        ·
          refine ⟨254188788304826952641426129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169459192203217968427617419 254188788304826952641426129)
          ·
            refine ⟨190641591228620214481069597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254188788304826952641426129 190641591228620214481069597)
            ·
              refine ⟨71490596710732580430401099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190641591228620214481069597 71490596710732580430401099)
              ·
                refine ⟨107235895066098870645601649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71490596710732580430401099 107235895066098870645601649)
                ·
                  refine ⟨80426921299574152984201237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107235895066098870645601649 80426921299574152984201237)
                  ·
                    refine ⟨3770011935917538421134433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80426921299574152984201237 3770011935917538421134433)
                    ·
                      refine ⟨2827508951938153815850825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770011935917538421134433 2827508951938153815850825)
                      ·
                        rfl

theorem cell23_5506554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_5506554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506554 prefixEnd_5506554 := by exact prefixLift 5506554
  have htrace : WordTrace (prefixWord ++ tailWord_5506554) baseStart_5506554 baseEnd_5506554 := by
    simpa [prefixWord, tailWord_5506554, baseEnd_5506554] using wordTrace_append hprefix tailTrace_5506554
  have hstable : (prefixWord ++ tailWord_5506554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506554).length < 2 ^ (prefixWord ++ tailWord_5506554).sum := by decide
  have hdescent : baseEnd_5506554 < baseStart_5506554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_5506597 : Nat := 118140960795 + 5506597 * 2 ^ 59
def prefixEnd_5506597 : Nat := 4983230072969 + 3 ^ 40 * 5506597 * 2
def baseEnd_5506597 : Nat := 2827531031606297147613127

theorem tailTrace_5506597 : CollatzResearch.WordTrace tailWord_5506597 prefixEnd_5506597 2827531031606297147613127 := by
  unfold tailWord_5506597
  simp only [CollatzResearch.WordTrace]
  refine ⟨200842092431546995739510045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133894728287697997159673363 200842092431546995739510045)
  ·
    refine ⟨75315784661830123402316267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200842092431546995739510045 75315784661830123402316267)
    ·
      refine ⟨112973676992745185103474401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75315784661830123402316267 112973676992745185103474401)
      ·
        refine ⟨84730257744558888827605801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112973676992745185103474401 84730257744558888827605801)
        ·
          refine ⟨63547693308419166620704351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84730257744558888827605801 63547693308419166620704351)
          ·
            refine ⟨95321539962628749931056527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63547693308419166620704351 95321539962628749931056527)
            ·
              refine ⟨142982309943943124896584791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95321539962628749931056527 142982309943943124896584791)
              ·
                refine ⟨214473464915914687344877187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142982309943943124896584791 214473464915914687344877187)
                ·
                  refine ⟨321710197373872031017315781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214473464915914687344877187 321710197373872031017315781)
                  ·
                    refine ⟨60320662007601005815746709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321710197373872031017315781 60320662007601005815746709)
                    ·
                      refine ⟨2827531031606297147613127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60320662007601005815746709 2827531031606297147613127)
                      ·
                        rfl

theorem cell23_5506597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_5506597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506597 prefixEnd_5506597 := by exact prefixLift 5506597
  have htrace : WordTrace (prefixWord ++ tailWord_5506597) baseStart_5506597 baseEnd_5506597 := by
    simpa [prefixWord, tailWord_5506597, baseEnd_5506597] using wordTrace_append hprefix tailTrace_5506597
  have hstable : (prefixWord ++ tailWord_5506597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506597).length < 2 ^ (prefixWord ++ tailWord_5506597).sum := by decide
  have hdescent : baseEnd_5506597 < baseStart_5506597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506644 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_5506644 : Nat := 118140960795 + 5506644 * 2 ^ 59
def prefixEnd_5506644 : Nat := 4983230072969 + 3 ^ 40 * 5506644 * 2
def baseEnd_5506644 : Nat := 2827555165197058463725411

theorem tailTrace_5506644 : CollatzResearch.WordTrace tailWord_5506644 prefixEnd_5506644 2827555165197058463725411 := by
  unfold tailWord_5506644
  simp only [CollatzResearch.WordTrace]
  refine ⟨100421903331188361383235493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133895871108251148510980657 100421903331188361383235493)
  ·
    refine ⟨18829106874597817759356655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100421903331188361383235493 18829106874597817759356655)
    ·
      refine ⟨28243660311896726639034983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18829106874597817759356655 28243660311896726639034983)
      ·
        refine ⟨42365490467845089958552475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28243660311896726639034983 42365490467845089958552475)
        ·
          refine ⟨63548235701767634937828713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42365490467845089958552475 63548235701767634937828713)
          ·
            refine ⟨47661176776325726203371535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63548235701767634937828713 47661176776325726203371535)
            ·
              refine ⟨71491765164488589305057303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47661176776325726203371535 71491765164488589305057303)
              ·
                refine ⟨107237647746732883957585955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71491765164488589305057303 107237647746732883957585955)
                ·
                  refine ⟨160856471620099325936378933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107237647746732883957585955 160856471620099325936378933)
                  ·
                    refine ⟨15080294214384311806535525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160856471620099325936378933 15080294214384311806535525)
                    ·
                      refine ⟨2827555165197058463725411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15080294214384311806535525 2827555165197058463725411)
                      ·
                        rfl

theorem cell23_5506644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_5506644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506644 prefixEnd_5506644 := by exact prefixLift 5506644
  have htrace : WordTrace (prefixWord ++ tailWord_5506644) baseStart_5506644 baseEnd_5506644 := by
    simpa [prefixWord, tailWord_5506644, baseEnd_5506644] using wordTrace_append hprefix tailTrace_5506644
  have hstable : (prefixWord ++ tailWord_5506644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506644).length < 2 ^ (prefixWord ++ tailWord_5506644).sum := by decide
  have hdescent : baseEnd_5506644 < baseStart_5506644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506695 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_5506695 : Nat := 118140960795 + 5506695 * 2 ^ 59
def prefixEnd_5506695 : Nat := 4983230072969 + 3 ^ 40 * 5506695 * 2
def baseEnd_5506695 : Nat := 2827581352710437764187677

theorem tailTrace_5506695 : CollatzResearch.WordTrace tailWord_5506695 prefixEnd_5506695 2827581352710437764187677 := by
  unfold tailWord_5506695
  simp only [CollatzResearch.WordTrace]
  refine ⟨200845666785191958476577539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133897111190127972317718359 200845666785191958476577539)
  ·
    refine ⟨301268500177787937714866309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200845666785191958476577539 301268500177787937714866309)
    ·
      refine ⟨56487843783335238321537433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301268500177787937714866309 56487843783335238321537433)
      ·
        refine ⟨42365882837501428741153075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56487843783335238321537433 42365882837501428741153075)
        ·
          refine ⟨63548824256252143111729613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42365882837501428741153075 63548824256252143111729613)
          ·
            refine ⟨23830809096094553666898605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63548824256252143111729613 23830809096094553666898605)
            ·
              refine ⟨8936553411035457625086977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23830809096094553666898605 8936553411035457625086977)
              ·
                refine ⟨6702415058276593218815233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8936553411035457625086977 6702415058276593218815233)
                ·
                  refine ⟨5026811293707444914111425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6702415058276593218815233 5026811293707444914111425)
                  ·
                    refine ⟨3770108470280583685583569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5026811293707444914111425 3770108470280583685583569)
                    ·
                      refine ⟨2827581352710437764187677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770108470280583685583569 2827581352710437764187677)
                      ·
                        rfl

theorem cell23_5506695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_5506695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506695 prefixEnd_5506695 := by exact prefixLift 5506695
  have htrace : WordTrace (prefixWord ++ tailWord_5506695) baseStart_5506695 baseEnd_5506695 := by
    simpa [prefixWord, tailWord_5506695, baseEnd_5506695] using wordTrace_append hprefix tailTrace_5506695
  have hstable : (prefixWord ++ tailWord_5506695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506695).length < 2 ^ (prefixWord ++ tailWord_5506695).sum := by decide
  have hdescent : baseEnd_5506695 < baseStart_5506695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506711 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_5506711 : Nat := 118140960795 + 5506711 * 2 ^ 59
def prefixEnd_5506711 : Nat := 4983230072969 + 3 ^ 40 * 5506711 * 2
def baseEnd_5506711 : Nat := 2827589568400909701587603

theorem tailTrace_5506711 : CollatzResearch.WordTrace tailWord_5506711 prefixEnd_5506711 2827589568400909701587603 := by
  unfold tailWord_5506711
  simp only [CollatzResearch.WordTrace]
  refine ⟨200846250353133993209159987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133897500235422662139439991 200846250353133993209159987)
  ·
    refine ⟨301269375529700989813739981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200846250353133993209159987 301269375529700989813739981)
    ·
      refine ⟨112976015823637871180152493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301269375529700989813739981 112976015823637871180152493)
      ·
        refine ⟨42366005933864201692557185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112976015823637871180152493 42366005933864201692557185)
        ·
          refine ⟨31774504450398151269417889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42366005933864201692557185 31774504450398151269417889)
          ·
            refine ⟨23830878337798613452063417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31774504450398151269417889 23830878337798613452063417)
            ·
              refine ⟨17873158753348960089047563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23830878337798613452063417 17873158753348960089047563)
              ·
                refine ⟨26809738130023440133571345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17873158753348960089047563 26809738130023440133571345)
                ·
                  refine ⟨20107303597517580100178509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26809738130023440133571345 20107303597517580100178509)
                  ·
                    refine ⟨7540238849069092537566941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20107303597517580100178509 7540238849069092537566941)
                    ·
                      refine ⟨2827589568400909701587603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540238849069092537566941 2827589568400909701587603)
                      ·
                        rfl

theorem cell23_5506711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_5506711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506711 prefixEnd_5506711 := by exact prefixLift 5506711
  have htrace : WordTrace (prefixWord ++ tailWord_5506711) baseStart_5506711 baseEnd_5506711 := by
    simpa [prefixWord, tailWord_5506711, baseEnd_5506711] using wordTrace_append hprefix tailTrace_5506711
  have hstable : (prefixWord ++ tailWord_5506711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506711).length < 2 ^ (prefixWord ++ tailWord_5506711).sum := by decide
  have hdescent : baseEnd_5506711 < baseStart_5506711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506712 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5506712 : Nat := 118140960795 + 5506712 * 2 ^ 59
def prefixEnd_5506712 : Nat := 4983230072969 + 3 ^ 40 * 5506712 * 2
def baseEnd_5506712 : Nat := 2827590081881564197675099

theorem tailTrace_5506712 : CollatzResearch.WordTrace tailWord_5506712 prefixEnd_5506712 2827590081881564197675099 := by
  unfold tailWord_5506712
  simp only [CollatzResearch.WordTrace]
  refine ⟨100423143413065185189973195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133897524550753580253297593 100423143413065185189973195)
  ·
    refine ⟨150634715119597777784959793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100423143413065185189973195 150634715119597777784959793)
    ·
      refine ⟨112976036339698333338719845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150634715119597777784959793 112976036339698333338719845)
      ·
        refine ⟨21183006813693437501009971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112976036339698333338719845 21183006813693437501009971)
        ·
          refine ⟨31774510220540156251514957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21183006813693437501009971 31774510220540156251514957)
          ·
            refine ⟨11915441332702558594318109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31774510220540156251514957 11915441332702558594318109)
            ·
              refine ⟨4468290499763459472869291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11915441332702558594318109 4468290499763459472869291)
              ·
                refine ⟨6702435749645189209303937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468290499763459472869291 6702435749645189209303937)
                ·
                  refine ⟨5026826812233891906977953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6702435749645189209303937 5026826812233891906977953)
                  ·
                    refine ⟨3770120109175418930233465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5026826812233891906977953 3770120109175418930233465)
                    ·
                      refine ⟨2827590081881564197675099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770120109175418930233465 2827590081881564197675099)
                      ·
                        rfl

theorem cell23_5506712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5506712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506712 prefixEnd_5506712 := by exact prefixLift 5506712
  have htrace : WordTrace (prefixWord ++ tailWord_5506712) baseStart_5506712 baseEnd_5506712 := by
    simpa [prefixWord, tailWord_5506712, baseEnd_5506712] using wordTrace_append hprefix tailTrace_5506712
  have hstable : (prefixWord ++ tailWord_5506712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506712).length < 2 ^ (prefixWord ++ tailWord_5506712).sum := by decide
  have hdescent : baseEnd_5506712 < baseStart_5506712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506751 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_5506751 : Nat := 118140960795 + 5506751 * 2 ^ 59
def prefixEnd_5506751 : Nat := 4983230072969 + 3 ^ 40 * 5506751 * 2
def baseEnd_5506751 : Nat := 2827610107627089545087419

theorem tailTrace_5506751 : CollatzResearch.WordTrace tailWord_5506751 prefixEnd_5506751 2827610107627089545087419 := by
  unfold tailWord_5506751
  simp only [CollatzResearch.WordTrace]
  refine ⟨200847709272989080040616107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133898472848659386693744071 200847709272989080040616107)
  ·
    refine ⟨301271563909483620060924161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200847709272989080040616107 301271563909483620060924161)
    ·
      refine ⟨225953672932112715045693121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301271563909483620060924161 225953672932112715045693121)
      ·
        refine ⟨169465254699084536284269841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225953672932112715045693121 169465254699084536284269841)
        ·
          refine ⟨127098941024313402213202381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169465254699084536284269841 127098941024313402213202381)
          ·
            refine ⟨47662102884117525829950893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127098941024313402213202381 47662102884117525829950893)
            ·
              refine ⟨17873288581544072186231585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47662102884117525829950893 17873288581544072186231585)
              ·
                refine ⟨13404966436158054139673689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17873288581544072186231585 13404966436158054139673689)
                ·
                  refine ⟨10053724827118540604755267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13404966436158054139673689 10053724827118540604755267)
                  ·
                    refine ⟨15080587240677810907132901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10053724827118540604755267 15080587240677810907132901)
                    ·
                      refine ⟨2827610107627089545087419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15080587240677810907132901 2827610107627089545087419)
                      ·
                        rfl

theorem cell23_5506751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_5506751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506751 prefixEnd_5506751 := by exact prefixLift 5506751
  have htrace : WordTrace (prefixWord ++ tailWord_5506751) baseStart_5506751 baseEnd_5506751 := by
    simpa [prefixWord, tailWord_5506751, baseEnd_5506751] using wordTrace_append hprefix tailTrace_5506751
  have hstable : (prefixWord ++ tailWord_5506751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506751).length < 2 ^ (prefixWord ++ tailWord_5506751).sum := by decide
  have hdescent : baseEnd_5506751 < baseStart_5506751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506788 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_5506788 : Nat := 118140960795 + 5506788 * 2 ^ 59
def prefixEnd_5506788 : Nat := 4983230072969 + 3 ^ 40 * 5506788 * 2
def baseEnd_5506788 : Nat := 2827629106411305900324749

theorem tailTrace_5506788 : CollatzResearch.WordTrace tailWord_5506788 prefixEnd_5506788 2827629106411305900324749 := by
  unfold tailWord_5506788
  simp only [CollatzResearch.WordTrace]
  refine ⟨100424529386927517679856509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133899372515903356906475345 100424529386927517679856509)
  ·
    refine ⟨37659198520097819129946191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100424529386927517679856509 37659198520097819129946191)
    ·
      refine ⟨56488797780146728694919287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37659198520097819129946191 56488797780146728694919287)
      ·
        refine ⟨84733196670220093042378931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56488797780146728694919287 84733196670220093042378931)
        ·
          refine ⟨127099795005330139563568397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84733196670220093042378931 127099795005330139563568397)
          ·
            refine ⟨47662423126998802336338149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127099795005330139563568397 47662423126998802336338149)
            ·
              refine ⟨8936704336312275438063403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47662423126998802336338149 8936704336312275438063403)
              ·
                refine ⟨13405056504468413157095105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8936704336312275438063403 13405056504468413157095105)
                ·
                  refine ⟨10053792378351309867821329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13405056504468413157095105 10053792378351309867821329)
                  ·
                    refine ⟨7540344283763482400865997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10053792378351309867821329 7540344283763482400865997)
                    ·
                      refine ⟨2827629106411305900324749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540344283763482400865997 2827629106411305900324749)
                      ·
                        rfl

theorem cell23_5506788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_5506788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506788 prefixEnd_5506788 := by exact prefixLift 5506788
  have htrace : WordTrace (prefixWord ++ tailWord_5506788) baseStart_5506788 baseEnd_5506788 := by
    simpa [prefixWord, tailWord_5506788, baseEnd_5506788] using wordTrace_append hprefix tailTrace_5506788
  have hstable : (prefixWord ++ tailWord_5506788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506788).length < 2 ^ (prefixWord ++ tailWord_5506788).sum := by decide
  have hdescent : baseEnd_5506788 < baseStart_5506788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506828 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_5506828 : Nat := 118140960795 + 5506828 * 2 ^ 59
def prefixEnd_5506828 : Nat := 4983230072969 + 3 ^ 40 * 5506828 * 2
def baseEnd_5506828 : Nat := 2827649645637485743824565

theorem tailTrace_5506828 : CollatzResearch.WordTrace tailWord_5506828 prefixEnd_5506828 2827649645637485743824565 := by
  unfold tailWord_5506828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100425258846855061095584569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133900345129140081460779425 100425258846855061095584569)
  ·
    refine ⟨75318944135141295821688427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100425258846855061095584569 75318944135141295821688427)
    ·
      refine ⟨112978416202711943732532641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75318944135141295821688427 112978416202711943732532641)
      ·
        refine ⟨84733812152033957799399481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112978416202711943732532641 84733812152033957799399481)
        ·
          refine ⟨63550359114025468349549611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84733812152033957799399481 63550359114025468349549611)
          ·
            refine ⟨95325538671038202524324417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63550359114025468349549611 95325538671038202524324417)
            ·
              refine ⟨71494154003278651893243313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95325538671038202524324417 71494154003278651893243313)
              ·
                refine ⟨53620615502458988919932485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71494154003278651893243313 53620615502458988919932485)
                ·
                  refine ⟨10053865406711060422487341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53620615502458988919932485 10053865406711060422487341)
                  ·
                    refine ⟨3770199527516647658432753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10053865406711060422487341 3770199527516647658432753)
                    ·
                      refine ⟨2827649645637485743824565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770199527516647658432753 2827649645637485743824565)
                      ·
                        rfl

theorem cell23_5506828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_5506828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506828 prefixEnd_5506828 := by exact prefixLift 5506828
  have htrace : WordTrace (prefixWord ++ tailWord_5506828) baseStart_5506828 baseEnd_5506828 := by
    simpa [prefixWord, tailWord_5506828, baseEnd_5506828] using wordTrace_append hprefix tailTrace_5506828
  have hstable : (prefixWord ++ tailWord_5506828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506828).length < 2 ^ (prefixWord ++ tailWord_5506828).sum := by decide
  have hdescent : baseEnd_5506828 < baseStart_5506828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506836 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5506836 : Nat := 118140960795 + 5506836 * 2 ^ 59
def prefixEnd_5506836 : Nat := 4983230072969 + 3 ^ 40 * 5506836 * 2
def baseEnd_5506836 : Nat := 2827653753482721712524529

theorem tailTrace_5506836 : CollatzResearch.WordTrace tailWord_5506836 prefixEnd_5506836 2827653753482721712524529 := by
  unfold tailWord_5506836
  simp only [CollatzResearch.WordTrace]
  refine ⟨100425404738840569778730181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133900539651787426371640241 100425404738840569778730181)
  ·
    refine ⟨18829763388532606833511909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100425404738840569778730181 18829763388532606833511909)
    ·
      refine ⟨3530580635349863781283483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18829763388532606833511909 3530580635349863781283483)
      ·
        refine ⟨5295870953024795671925225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530580635349863781283483 5295870953024795671925225)
        ·
          refine ⟨3971903214768596753943919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5295870953024795671925225 3971903214768596753943919)
          ·
            refine ⟨5957854822152895130915879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971903214768596753943919 5957854822152895130915879)
            ·
              refine ⟨8936782233229342696373819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957854822152895130915879 8936782233229342696373819)
              ·
                refine ⟨13405173349844014044560729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8936782233229342696373819 13405173349844014044560729)
                ·
                  refine ⟨10053880012383010533420547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13405173349844014044560729 10053880012383010533420547)
                  ·
                    refine ⟨15080820018574515800130821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10053880012383010533420547 15080820018574515800130821)
                    ·
                      refine ⟨2827653753482721712524529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15080820018574515800130821 2827653753482721712524529)
                      ·
                        rfl

theorem cell23_5506836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5506836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506836 prefixEnd_5506836 := by exact prefixLift 5506836
  have htrace : WordTrace (prefixWord ++ tailWord_5506836) baseStart_5506836 baseEnd_5506836 := by
    simpa [prefixWord, tailWord_5506836, baseEnd_5506836] using wordTrace_append hprefix tailTrace_5506836
  have hstable : (prefixWord ++ tailWord_5506836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506836).length < 2 ^ (prefixWord ++ tailWord_5506836).sum := by decide
  have hdescent : baseEnd_5506836 < baseStart_5506836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506846 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5506846 : Nat := 118140960795 + 5506846 * 2 ^ 59
def prefixEnd_5506846 : Nat := 4983230072969 + 3 ^ 40 * 5506846 * 2
def baseEnd_5506846 : Nat := 942552962763088891133161

theorem tailTrace_5506846 : CollatzResearch.WordTrace tailWord_5506846 prefixEnd_5506846 942552962763088891133161 := by
  unfold tailWord_5506846
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106396775955613908165549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133900782805096607510216261 25106396775955613908165549)
  ·
    refine ⟨9414898790983355215562081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25106396775955613908165549 9414898790983355215562081)
    ·
      refine ⟨7061174093237516411671561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9414898790983355215562081 7061174093237516411671561)
      ·
        refine ⟨5295880569928137308753671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7061174093237516411671561 5295880569928137308753671)
        ·
          refine ⟨7943820854892205963130507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295880569928137308753671 7943820854892205963130507)
          ·
            refine ⟨11915731282338308944695761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943820854892205963130507 11915731282338308944695761)
            ·
              refine ⟨8936798461753731708521821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11915731282338308944695761 8936798461753731708521821)
              ·
                refine ⟨3351299423157649390695683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8936798461753731708521821 3351299423157649390695683)
                ·
                  refine ⟨5026949134736474086043525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351299423157649390695683 5026949134736474086043525)
                  ·
                    refine ⟨942552962763088891133161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5026949134736474086043525 942552962763088891133161)
                    ·
                      rfl

theorem cell23_5506846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5506846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506846 prefixEnd_5506846 := by exact prefixLift 5506846
  have htrace : WordTrace (prefixWord ++ tailWord_5506846) baseStart_5506846 baseEnd_5506846 := by
    simpa [prefixWord, tailWord_5506846, baseEnd_5506846] using wordTrace_append hprefix tailTrace_5506846
  have hstable : (prefixWord ++ tailWord_5506846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506846).length < 2 ^ (prefixWord ++ tailWord_5506846).sum := by decide
  have hdescent : baseEnd_5506846 < baseStart_5506846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506851 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 1, 6]
def baseStart_5506851 : Nat := 118140960795 + 5506851 * 2 ^ 59
def prefixEnd_5506851 : Nat := 4983230072969 + 3 ^ 40 * 5506851 * 2
def baseEnd_5506851 : Nat := 942553818564179717945653

theorem tailTrace_5506851 : CollatzResearch.WordTrace tailWord_5506851 prefixEnd_5506851 942553818564179717945653 := by
  unfold tailWord_5506851
  simp only [CollatzResearch.WordTrace]
  refine ⟨200851356572626797119256407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133900904381751198079504271 200851356572626797119256407)
  ·
    refine ⟨301277034858940195678884611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200851356572626797119256407 301277034858940195678884611)
    ·
      refine ⟨451915552288410293518326917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301277034858940195678884611 451915552288410293518326917)
      ·
        refine ⟨84734166054076930034686297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 451915552288410293518326917 84734166054076930034686297)
        ·
          refine ⟨63550624540557697526014723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84734166054076930034686297 63550624540557697526014723)
          ·
            refine ⟨95325936810836546289022085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63550624540557697526014723 95325936810836546289022085)
            ·
              refine ⟨17873613152031852429191641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95325936810836546289022085 17873613152031852429191641)
              ·
                refine ⟨13405209864023889321893731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17873613152031852429191641 13405209864023889321893731)
                ·
                  refine ⟨20107814796035833982840597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13405209864023889321893731 20107814796035833982840597)
                  ·
                    refine ⟨942553818564179717945653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20107814796035833982840597 942553818564179717945653)
                    ·
                      rfl

theorem cell23_5506851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 6].length) (baseStart_5506851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506851 prefixEnd_5506851 := by exact prefixLift 5506851
  have htrace : WordTrace (prefixWord ++ tailWord_5506851) baseStart_5506851 baseEnd_5506851 := by
    simpa [prefixWord, tailWord_5506851, baseEnd_5506851] using wordTrace_append hprefix tailTrace_5506851
  have hstable : (prefixWord ++ tailWord_5506851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506851).length < 2 ^ (prefixWord ++ tailWord_5506851).sum := by decide
  have hdescent : baseEnd_5506851 < baseStart_5506851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506852 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_5506852 : Nat := 118140960795 + 5506852 * 2 ^ 59
def prefixEnd_5506852 : Nat := 4983230072969 + 3 ^ 40 * 5506852 * 2
def baseEnd_5506852 : Nat := 2827661969173193649924455

theorem tailTrace_5506852 : CollatzResearch.WordTrace tailWord_5506852 prefixEnd_5506852 2827661969173193649924455 := by
  unfold tailWord_5506852
  simp only [CollatzResearch.WordTrace]
  refine ⟨100425696522811587145021405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133900928697082116193361873 100425696522811587145021405)
  ·
    refine ⟨37659636196054345179383027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100425696522811587145021405 37659636196054345179383027)
    ·
      refine ⟨56489454294081517769074541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37659636196054345179383027 56489454294081517769074541)
      ·
        refine ⟨21183545360280569163402953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56489454294081517769074541 21183545360280569163402953)
        ·
          refine ⟨15887659020210426872552215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21183545360280569163402953 15887659020210426872552215)
          ·
            refine ⟨23831488530315640308828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15887659020210426872552215 23831488530315640308828323)
            ·
              refine ⟨35747232795473460463242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23831488530315640308828323 35747232795473460463242485)
              ·
                refine ⟨3351303074575636918428983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35747232795473460463242485 3351303074575636918428983)
                ·
                  refine ⟨5026954611863455377643475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351303074575636918428983 5026954611863455377643475)
                  ·
                    refine ⟨7540431917795183066465213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5026954611863455377643475 7540431917795183066465213)
                    ·
                      refine ⟨2827661969173193649924455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540431917795183066465213 2827661969173193649924455)
                      ·
                        rfl

theorem cell23_5506852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_5506852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506852 prefixEnd_5506852 := by exact prefixLift 5506852
  have htrace : WordTrace (prefixWord ++ tailWord_5506852) baseStart_5506852 baseEnd_5506852 := by
    simpa [prefixWord, tailWord_5506852, baseEnd_5506852] using wordTrace_append hprefix tailTrace_5506852
  have hstable : (prefixWord ++ tailWord_5506852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506852).length < 2 ^ (prefixWord ++ tailWord_5506852).sum := by decide
  have hdescent : baseEnd_5506852 < baseStart_5506852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506878 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5506878 : Nat := 118140960795 + 5506878 * 2 ^ 59
def prefixEnd_5506878 : Nat := 4983230072969 + 3 ^ 40 * 5506878 * 2
def baseEnd_5506878 : Nat := 2827675319670210548199335

theorem tailTrace_5506878 : CollatzResearch.WordTrace tailWord_5506878 prefixEnd_5506878 2827675319670210548199335 := by
  unfold tailWord_5506878
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106542667941122591311161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133901560895685987153659525 25106542667941122591311161)
  ·
    refine ⟨18829907000955841943483371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25106542667941122591311161 18829907000955841943483371)
    ·
      refine ⟨28244860501433762915225057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18829907000955841943483371 28244860501433762915225057)
      ·
        refine ⟨21183645376075322186418793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28244860501433762915225057 21183645376075322186418793)
        ·
          refine ⟨15887734032056491639814095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21183645376075322186418793 15887734032056491639814095)
          ·
            refine ⟨23831601048084737459721143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15887734032056491639814095 23831601048084737459721143)
            ·
              refine ⟨35747401572127106189581715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23831601048084737459721143 35747401572127106189581715)
              ·
                refine ⟨53621102358190659284372573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35747401572127106189581715 53621102358190659284372573)
                ·
                  refine ⟨20107913384321497231639715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53621102358190659284372573 20107913384321497231639715)
                  ·
                    refine ⟨30161870076482245847459573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20107913384321497231639715 30161870076482245847459573)
                    ·
                      refine ⟨2827675319670210548199335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30161870076482245847459573 2827675319670210548199335)
                      ·
                        rfl

theorem cell23_5506878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5506878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506878 prefixEnd_5506878 := by exact prefixLift 5506878
  have htrace : WordTrace (prefixWord ++ tailWord_5506878) baseStart_5506878 baseEnd_5506878 := by
    simpa [prefixWord, tailWord_5506878, baseEnd_5506878] using wordTrace_append hprefix tailTrace_5506878
  have hstable : (prefixWord ++ tailWord_5506878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506878).length < 2 ^ (prefixWord ++ tailWord_5506878).sum := by decide
  have hdescent : baseEnd_5506878 < baseStart_5506878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506885 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_5506885 : Nat := 118140960795 + 5506885 * 2 ^ 59
def prefixEnd_5506885 : Nat := 4983230072969 + 3 ^ 40 * 5506885 * 2
def baseEnd_5506885 : Nat := 942559638011597340270601

theorem tailTrace_5506885 : CollatzResearch.WordTrace tailWord_5506885 prefixEnd_5506885 942559638011597340270601 := by
  unfold tailWord_5506885
  simp only [CollatzResearch.WordTrace]
  refine ⟨200852596654503620925994109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133901731103002413950662739 200852596654503620925994109)
  ·
    refine ⟨75319723745438857847247791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200852596654503620925994109 75319723745438857847247791)
    ·
      refine ⟨112979585618158286770871687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75319723745438857847247791 112979585618158286770871687)
      ·
        refine ⟨169469378427237430156307531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112979585618158286770871687 169469378427237430156307531)
        ·
          refine ⟨254204067640856145234461297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169469378427237430156307531 254204067640856145234461297)
          ·
            refine ⟨190653050730642108925845973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254204067640856145234461297 190653050730642108925845973)
            ·
              refine ⟨4468430876499424427949515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190653050730642108925845973 4468430876499424427949515)
              ·
                refine ⟨6702646314749136641924273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468430876499424427949515 6702646314749136641924273)
                ·
                  refine ⟨5026984736061852481443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6702646314749136641924273 5026984736061852481443205)
                  ·
                    refine ⟨942559638011597340270601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5026984736061852481443205 942559638011597340270601)
                    ·
                      rfl

theorem cell23_5506885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_5506885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506885 prefixEnd_5506885 := by exact prefixLift 5506885
  have htrace : WordTrace (prefixWord ++ tailWord_5506885) baseStart_5506885 baseEnd_5506885 := by
    simpa [prefixWord, tailWord_5506885, baseEnd_5506885] using wordTrace_append hprefix tailTrace_5506885
  have hstable : (prefixWord ++ tailWord_5506885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506885).length < 2 ^ (prefixWord ++ tailWord_5506885).sum := by decide
  have hdescent : baseEnd_5506885 < baseStart_5506885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506888 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_5506888 : Nat := 118140960795 + 5506888 * 2 ^ 59
def prefixEnd_5506888 : Nat := 4983230072969 + 3 ^ 40 * 5506888 * 2
def baseEnd_5506888 : Nat := 2827680454476755509074289

theorem tailTrace_5506888 : CollatzResearch.WordTrace tailWord_5506888 prefixEnd_5506888 2827680454476755509074289 := by
  unfold tailWord_5506888
  simp only [CollatzResearch.WordTrace]
  refine ⟨100426353036746376219176659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133901804048995168292235545 100426353036746376219176659)
  ·
    refine ⟨150639529555119564328764989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100426353036746376219176659 150639529555119564328764989)
    ·
      refine ⟨56489823583169836623286871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150639529555119564328764989 56489823583169836623286871)
      ·
        refine ⟨84734735374754754934930307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56489823583169836623286871 84734735374754754934930307)
        ·
          refine ⟨127102103062132132402395461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84734735374754754934930307 127102103062132132402395461)
          ·
            refine ⟨23831644324149774825449149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127102103062132132402395461 23831644324149774825449149)
            ·
              refine ⟨8936866621556165559543431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23831644324149774825449149 8936866621556165559543431)
              ·
                refine ⟨13405299932334248339315147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8936866621556165559543431 13405299932334248339315147)
                ·
                  refine ⟨20107949898501372508972721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13405299932334248339315147 20107949898501372508972721)
                  ·
                    refine ⟨15080962423876029381729541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20107949898501372508972721 15080962423876029381729541)
                    ·
                      refine ⟨2827680454476755509074289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15080962423876029381729541 2827680454476755509074289)
                      ·
                        rfl

theorem cell23_5506888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_5506888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506888 prefixEnd_5506888 := by exact prefixLift 5506888
  have htrace : WordTrace (prefixWord ++ tailWord_5506888) baseStart_5506888 baseEnd_5506888 := by
    simpa [prefixWord, tailWord_5506888, baseEnd_5506888] using wordTrace_append hprefix tailTrace_5506888
  have hstable : (prefixWord ++ tailWord_5506888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506888).length < 2 ^ (prefixWord ++ tailWord_5506888).sum := by decide
  have hdescent : baseEnd_5506888 < baseStart_5506888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506898 : List Nat := [3, 2, 2, 1, 1, 3, 4, 7]
def baseStart_5506898 : Nat := 118140960795 + 5506898 * 2 ^ 59
def prefixEnd_5506898 : Nat := 4983230072969 + 3 ^ 40 * 5506898 * 2
def baseEnd_5506898 : Nat := 104729095899381498887009

theorem tailTrace_5506898 : CollatzResearch.WordTrace tailWord_5506898 prefixEnd_5506898 104729095899381498887009 := by
  unfold tailWord_5506898
  simp only [CollatzResearch.WordTrace]
  refine ⟨50213267700864131036554337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133902047202304349430811565 50213267700864131036554337)
  ·
    refine ⟨37659950775648098277415753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50213267700864131036554337 37659950775648098277415753)
    ·
      refine ⟨28244963081736073708061815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37659950775648098277415753 28244963081736073708061815)
      ·
        refine ⟨42367444622604110562092723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28244963081736073708061815 42367444622604110562092723)
        ·
          refine ⟨63551166933906165843139085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42367444622604110562092723 63551166933906165843139085)
          ·
            refine ⟨23831687600214812191177157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63551166933906165843139085 23831687600214812191177157)
            ·
              refine ⟨4468441425040277285845717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23831687600214812191177157 4468441425040277285845717)
              ·
                refine ⟨104729095899381498887009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4468441425040277285845717 104729095899381498887009)
                ·
                  rfl

theorem cell23_5506898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_5506898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506898 prefixEnd_5506898 := by exact prefixLift 5506898
  have htrace : WordTrace (prefixWord ++ tailWord_5506898) baseStart_5506898 baseEnd_5506898 := by
    simpa [prefixWord, tailWord_5506898, baseEnd_5506898] using wordTrace_append hprefix tailTrace_5506898
  have hstable : (prefixWord ++ tailWord_5506898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506898).length < 2 ^ (prefixWord ++ tailWord_5506898).sum := by decide
  have hdescent : baseEnd_5506898 < baseStart_5506898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506925 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5506925 : Nat := 118140960795 + 5506925 * 2 ^ 59
def prefixEnd_5506925 : Nat := 4983230072969 + 3 ^ 40 * 5506925 * 2
def baseEnd_5506925 : Nat := 2827699453260971864311619

theorem tailTrace_5506925 : CollatzResearch.WordTrace tailWord_5506925 prefixEnd_5506925 2827699453260971864311619 := by
  unfold tailWord_5506925
  simp only [CollatzResearch.WordTrace]
  refine ⟨200854055574358707757450229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133902703716239138504966819 200854055574358707757450229)
  ·
    refine ⟨18830067710096128852260959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200854055574358707757450229 18830067710096128852260959)
    ·
      refine ⟨28245101565144193278391439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18830067710096128852260959 28245101565144193278391439)
      ·
        refine ⟨42367652347716289917587159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28245101565144193278391439 42367652347716289917587159)
        ·
          refine ⟨63551478521574434876380739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42367652347716289917587159 63551478521574434876380739)
          ·
            refine ⟨95327217782361652314571109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63551478521574434876380739 95327217782361652314571109)
            ·
              refine ⟨17873853334192809808982083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95327217782361652314571109 17873853334192809808982083)
              ·
                refine ⟨26810780001289214713473125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17873853334192809808982083 26810780001289214713473125)
                ·
                  refine ⟨5027021250241727758776211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26810780001289214713473125 5027021250241727758776211)
                  ·
                    refine ⟨7540531875362591638164317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5027021250241727758776211 7540531875362591638164317)
                    ·
                      refine ⟨2827699453260971864311619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540531875362591638164317 2827699453260971864311619)
                      ·
                        rfl

theorem cell23_5506925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5506925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506925 prefixEnd_5506925 := by exact prefixLift 5506925
  have htrace : WordTrace (prefixWord ++ tailWord_5506925) baseStart_5506925 baseEnd_5506925 := by
    simpa [prefixWord, tailWord_5506925, baseEnd_5506925] using wordTrace_append hprefix tailTrace_5506925
  have hstable : (prefixWord ++ tailWord_5506925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506925).length < 2 ^ (prefixWord ++ tailWord_5506925).sum := by decide
  have hdescent : baseEnd_5506925 < baseStart_5506925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506931 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_5506931 : Nat := 118140960795 + 5506931 * 2 ^ 59
def prefixEnd_5506931 : Nat := 4983230072969 + 3 ^ 40 * 5506931 * 2
def baseEnd_5506931 : Nat := 2827702534144898840836591

theorem tailTrace_5506931 : CollatzResearch.WordTrace tailWord_5506931 prefixEnd_5506931 2827702534144898840836591 := by
  unfold tailWord_5506931
  simp only [CollatzResearch.WordTrace]
  refine ⟨200854274412336970782168647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133902849608224647188112431 200854274412336970782168647)
  ·
    refine ⟨301281411618505456173252971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200854274412336970782168647 301281411618505456173252971)
    ·
      refine ⟨451922117427758184259879457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301281411618505456173252971 451922117427758184259879457)
      ·
        refine ⟨338941588070818638194909593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451922117427758184259879457 338941588070818638194909593)
        ·
          refine ⟨254206191053113978646182195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338941588070818638194909593 254206191053113978646182195)
          ·
            refine ⟨381309286579670967969273293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254206191053113978646182195 381309286579670967969273293)
            ·
              refine ⟨142990982467376612988477485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381309286579670967969273293 142990982467376612988477485)
              ·
                refine ⟨53621618425266229870679057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142990982467376612988477485 53621618425266229870679057)
                ·
                  refine ⟨40216213818949672403009293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53621618425266229870679057 40216213818949672403009293)
                  ·
                    refine ⟨15081080182106127151128485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40216213818949672403009293 15081080182106127151128485)
                    ·
                      refine ⟨2827702534144898840836591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15081080182106127151128485 2827702534144898840836591)
                      ·
                        rfl

theorem cell23_5506931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_5506931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506931 prefixEnd_5506931 := by exact prefixLift 5506931
  have htrace : WordTrace (prefixWord ++ tailWord_5506931) baseStart_5506931 baseEnd_5506931 := by
    simpa [prefixWord, tailWord_5506931, baseEnd_5506931] using wordTrace_append hprefix tailTrace_5506931
  have hstable : (prefixWord ++ tailWord_5506931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506931).length < 2 ^ (prefixWord ++ tailWord_5506931).sum := by decide
  have hdescent : baseEnd_5506931 < baseStart_5506931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506941 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_5506941 : Nat := 118140960795 + 5506941 * 2 ^ 59
def prefixEnd_5506941 : Nat := 4983230072969 + 3 ^ 40 * 5506941 * 2
def baseEnd_5506941 : Nat := 942569222983814600570515

theorem tailTrace_5506941 : CollatzResearch.WordTrace tailWord_5506941 prefixEnd_5506941 942569222983814600570515 := by
  unfold tailWord_5506941
  simp only [CollatzResearch.WordTrace]
  refine ⟨200854639142300742490032677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133903092761533828326688451 200854639142300742490032677)
  ·
    refine ⟨37660244839181389216881127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200854639142300742490032677 37660244839181389216881127)
    ·
      refine ⟨56490367258772083825321691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37660244839181389216881127 56490367258772083825321691)
      ·
        refine ⟨84735550888158125737982537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56490367258772083825321691 84735550888158125737982537)
        ·
          refine ⟨63551663166118594303486903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84735550888158125737982537 63551663166118594303486903)
          ·
            refine ⟨95327494749177891455230355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63551663166118594303486903 95327494749177891455230355)
            ·
              refine ⟨142991242123766837182845533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95327494749177891455230355 142991242123766837182845533)
              ·
                refine ⟨53621715796412563943567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142991242123766837182845533 53621715796412563943567075)
                ·
                  refine ⟨80432573694618845915350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53621715796412563943567075 80432573694618845915350613)
                  ·
                    refine ⟨942569222983814600570515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80432573694618845915350613 942569222983814600570515)
                    ·
                      rfl

theorem cell23_5506941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_5506941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506941 prefixEnd_5506941 := by exact prefixLift 5506941
  have htrace : WordTrace (prefixWord ++ tailWord_5506941) baseStart_5506941 baseEnd_5506941 := by
    simpa [prefixWord, tailWord_5506941, baseEnd_5506941] using wordTrace_append hprefix tailTrace_5506941
  have hstable : (prefixWord ++ tailWord_5506941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506941).length < 2 ^ (prefixWord ++ tailWord_5506941).sum := by decide
  have hdescent : baseEnd_5506941 < baseStart_5506941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506952 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5506952 : Nat := 118140960795 + 5506952 * 2 ^ 59
def prefixEnd_5506952 : Nat := 4983230072969 + 3 ^ 40 * 5506952 * 2
def baseEnd_5506952 : Nat := 2827713317238643258673995

theorem tailTrace_5506952 : CollatzResearch.WordTrace tailWord_5506952 prefixEnd_5506952 2827713317238643258673995 := by
  unfold tailWord_5506952
  simp only [CollatzResearch.WordTrace]
  refine ⟨100427520172630445684341555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133903360230173927579122073 100427520172630445684341555)
  ·
    refine ⟨150641280258945668526512333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100427520172630445684341555 150641280258945668526512333)
    ·
      refine ⟨56490480097104625697442125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150641280258945668526512333 56490480097104625697442125)
      ·
        refine ⟨21183930036414234636540797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56490480097104625697442125 21183930036414234636540797)
        ·
          refine ⟨7943973763655337988702799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21183930036414234636540797 7943973763655337988702799)
          ·
            refine ⟨11915960645483006983054199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943973763655337988702799 11915960645483006983054199)
            ·
              refine ⟨17873940968224510474581299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11915960645483006983054199 17873940968224510474581299)
              ·
                refine ⟨26810911452336765711871949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17873940968224510474581299 26810911452336765711871949)
                ·
                  refine ⟨10054091794626287141951981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26810911452336765711871949 10054091794626287141951981)
                  ·
                    refine ⟨3770284422984857678231993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10054091794626287141951981 3770284422984857678231993)
                    ·
                      refine ⟨2827713317238643258673995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770284422984857678231993 2827713317238643258673995)
                      ·
                        rfl

theorem cell23_5506952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5506952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506952 prefixEnd_5506952 := by exact prefixLift 5506952
  have htrace : WordTrace (prefixWord ++ tailWord_5506952) baseStart_5506952 baseEnd_5506952 := by
    simpa [prefixWord, tailWord_5506952, baseEnd_5506952] using wordTrace_append hprefix tailTrace_5506952
  have hstable : (prefixWord ++ tailWord_5506952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506952).length < 2 ^ (prefixWord ++ tailWord_5506952).sum := by decide
  have hdescent : baseEnd_5506952 < baseStart_5506952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506965 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_5506965 : Nat := 118140960795 + 5506965 * 2 ^ 59
def prefixEnd_5506965 : Nat := 4983230072969 + 3 ^ 40 * 5506965 * 2
def baseEnd_5506965 : Nat := 2827719992487151707811435

theorem tailTrace_5506965 : CollatzResearch.WordTrace tailWord_5506965 prefixEnd_5506965 2827719992487151707811435 := by
  unfold tailWord_5506965
  simp only [CollatzResearch.WordTrace]
  refine ⟨200855514494213794588906349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133903676329475863059270899 200855514494213794588906349)
  ·
    refine ⟨75320817935330172970839881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200855514494213794588906349 75320817935330172970839881)
    ·
      refine ⟨56490613451497629728129911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75320817935330172970839881 56490613451497629728129911)
      ·
        refine ⟨84735920177246444592194867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56490613451497629728129911 84735920177246444592194867)
        ·
          refine ⟨127103880265869666888292301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84735920177246444592194867 127103880265869666888292301)
          ·
            refine ⟨47663955099701125083109613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127103880265869666888292301 47663955099701125083109613)
            ·
              refine ⟨17873983162387921906166105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47663955099701125083109613 17873983162387921906166105)
              ·
                refine ⟨13405487371790941429624579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17873983162387921906166105 13405487371790941429624579)
                ·
                  refine ⟨20108231057686412144436869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13405487371790941429624579 20108231057686412144436869)
                  ·
                    refine ⟨3770293323316202277081913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20108231057686412144436869 3770293323316202277081913)
                    ·
                      refine ⟨2827719992487151707811435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770293323316202277081913 2827719992487151707811435)
                      ·
                        rfl

theorem cell23_5506965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_5506965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506965 prefixEnd_5506965 := by exact prefixLift 5506965
  have htrace : WordTrace (prefixWord ++ tailWord_5506965) baseStart_5506965 baseEnd_5506965 := by
    simpa [prefixWord, tailWord_5506965, baseEnd_5506965] using wordTrace_append hprefix tailTrace_5506965
  have hstable : (prefixWord ++ tailWord_5506965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506965).length < 2 ^ (prefixWord ++ tailWord_5506965).sum := by decide
  have hdescent : baseEnd_5506965 < baseStart_5506965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5506981 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_5506981 : Nat := 118140960795 + 5506981 * 2 ^ 59
def prefixEnd_5506981 : Nat := 4983230072969 + 3 ^ 40 * 5506981 * 2
def baseEnd_5506981 : Nat := 2827728208177623645211361

theorem tailTrace_5506981 : CollatzResearch.WordTrace tailWord_5506981 prefixEnd_5506981 2827728208177623645211361 := by
  unfold tailWord_5506981
  simp only [CollatzResearch.WordTrace]
  refine ⟨200856098062155829321488797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133904065374770552880992531 200856098062155829321488797)
  ·
    refine ⟨75321036773308435995558299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200856098062155829321488797 75321036773308435995558299)
    ·
      refine ⟨112981555159962653993337449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75321036773308435995558299 112981555159962653993337449)
      ·
        refine ⟨84736166369971990495003087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112981555159962653993337449 84736166369971990495003087)
        ·
          refine ⟨127104249554957985742504631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84736166369971990495003087 127104249554957985742504631)
          ·
            refine ⟨190656374332436978613756947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127104249554957985742504631 190656374332436978613756947)
            ·
              refine ⟨285984561498655467920635421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190656374332436978613756947 285984561498655467920635421)
              ·
                refine ⟨107244210561995800470238283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285984561498655467920635421 107244210561995800470238283)
                ·
                  refine ⟨160866315842993700705357425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107244210561995800470238283 160866315842993700705357425)
                  ·
                    refine ⟨120649736882245275529018069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160866315842993700705357425 120649736882245275529018069)
                    ·
                      refine ⟨2827728208177623645211361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120649736882245275529018069 2827728208177623645211361)
                      ·
                        rfl

theorem cell23_5506981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_5506981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5506981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5506981 prefixEnd_5506981 := by exact prefixLift 5506981
  have htrace : WordTrace (prefixWord ++ tailWord_5506981) baseStart_5506981 baseEnd_5506981 := by
    simpa [prefixWord, tailWord_5506981, baseEnd_5506981] using wordTrace_append hprefix tailTrace_5506981
  have hstable : (prefixWord ++ tailWord_5506981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5506981).length < 2 ^ (prefixWord ++ tailWord_5506981).sum := by decide
  have hdescent : baseEnd_5506981 < baseStart_5506981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5506981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507055 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 2, 4, 2]
def baseStart_5507055 : Nat := 118140960795 + 5507055 * 2 ^ 59
def prefixEnd_5507055 : Nat := 4983230072969 + 3 ^ 40 * 5507055 * 2
def baseEnd_5507055 : Nat := 2827766205746056355686021

theorem tailTrace_5507055 : CollatzResearch.WordTrace tailWord_5507055 prefixEnd_5507055 2827766205746056355686021 := by
  unfold tailWord_5507055
  simp only [CollatzResearch.WordTrace]
  refine ⟨200858797063887739959682619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133905864709258493306455079 200858797063887739959682619)
  ·
    refine ⟨301288195595831609939523929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200858797063887739959682619 301288195595831609939523929)
    ·
      refine ⟨225966146696873707454642947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301288195595831609939523929 225966146696873707454642947)
      ·
        refine ⟨338949220045310561181964421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225966146696873707454642947 338949220045310561181964421)
        ·
          refine ⟨63552978758495730221618329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338949220045310561181964421 63552978758495730221618329)
          ·
            refine ⟨47664734068871797666213747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63552978758495730221618329 47664734068871797666213747)
            ·
              refine ⟨71497101103307696499320621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47664734068871797666213747 71497101103307696499320621)
              ·
                refine ⟨26811412913740386187245233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71497101103307696499320621 26811412913740386187245233)
                ·
                  refine ⟨20108559685305289640433925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26811412913740386187245233 20108559685305289640433925)
                  ·
                    refine ⟨3770354940994741807581361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20108559685305289640433925 3770354940994741807581361)
                    ·
                      refine ⟨2827766205746056355686021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770354940994741807581361 2827766205746056355686021)
                      ·
                        rfl

theorem cell23_5507055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4, 2].length) (baseStart_5507055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507055 prefixEnd_5507055 := by exact prefixLift 5507055
  have htrace : WordTrace (prefixWord ++ tailWord_5507055) baseStart_5507055 baseEnd_5507055 := by
    simpa [prefixWord, tailWord_5507055, baseEnd_5507055] using wordTrace_append hprefix tailTrace_5507055
  have hstable : (prefixWord ++ tailWord_5507055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507055).length < 2 ^ (prefixWord ++ tailWord_5507055).sum := by decide
  have hdescent : baseEnd_5507055 < baseStart_5507055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507065 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_5507065 : Nat := 118140960795 + 5507065 * 2 ^ 59
def prefixEnd_5507065 : Nat := 4983230072969 + 3 ^ 40 * 5507065 * 2
def baseEnd_5507065 : Nat := 942590446850867105520325

theorem tailTrace_5507065 : CollatzResearch.WordTrace tailWord_5507065 prefixEnd_5507065 942590446850867105520325 := by
  unfold tailWord_5507065
  simp only [CollatzResearch.WordTrace]
  refine ⟨200859161793851511667546649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133906107862567674445031099 200859161793851511667546649)
  ·
    refine ⟨150644371345388633750659987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200859161793851511667546649 150644371345388633750659987)
    ·
      refine ⟨225966557018082950625989981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150644371345388633750659987 225966557018082950625989981)
      ·
        refine ⟨84737458881781106484746243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225966557018082950625989981 84737458881781106484746243)
        ·
          refine ⟨127106188322671659727119365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84737458881781106484746243 127106188322671659727119365)
          ·
            refine ⟨23832410310500936198834881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127106188322671659727119365 23832410310500936198834881)
            ·
              refine ⟨17874307732875702149126161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23832410310500936198834881 17874307732875702149126161)
              ·
                refine ⟨13405730799656776611844621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17874307732875702149126161 13405730799656776611844621)
                ·
                  refine ⟨5027149049871291229441733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13405730799656776611844621 5027149049871291229441733)
                  ·
                    refine ⟨942590446850867105520325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027149049871291229441733 942590446850867105520325)
                    ·
                      rfl

theorem cell23_5507065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_5507065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507065 prefixEnd_5507065 := by exact prefixLift 5507065
  have htrace : WordTrace (prefixWord ++ tailWord_5507065) baseStart_5507065 baseEnd_5507065 := by
    simpa [prefixWord, tailWord_5507065, baseEnd_5507065] using wordTrace_append hprefix tailTrace_5507065
  have hstable : (prefixWord ++ tailWord_5507065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507065).length < 2 ^ (prefixWord ++ tailWord_5507065).sum := by decide
  have hdescent : baseEnd_5507065 < baseStart_5507065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507068 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_5507068 : Nat := 118140960795 + 5507068 * 2 ^ 59
def prefixEnd_5507068 : Nat := 4983230072969 + 3 ^ 40 * 5507068 * 2
def baseEnd_5507068 : Nat := 2827772880994564804823461

theorem tailTrace_5507068 : CollatzResearch.WordTrace tailWord_5507068 prefixEnd_5507068 2827772880994564804823461 := by
  unfold tailWord_5507068
  simp only [CollatzResearch.WordTrace]
  refine ⟨100429635606420321589952929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133906180808560428786603905 100429635606420321589952929)
  ·
    refine ⟨75322226704815241192464697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100429635606420321589952929 75322226704815241192464697)
    ·
      refine ⟨56491670028611430894348523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75322226704815241192464697 56491670028611430894348523)
      ·
        refine ⟨84737505042917146341522785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56491670028611430894348523 84737505042917146341522785)
        ·
          refine ⟨63553128782187859756142089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84737505042917146341522785 63553128782187859756142089)
          ·
            refine ⟨47664846586640894817106567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63553128782187859756142089 47664846586640894817106567)
            ·
              refine ⟨71497269879961342225659851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47664846586640894817106567 71497269879961342225659851)
              ·
                refine ⟨107245904819942013338489777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71497269879961342225659851 107245904819942013338489777)
                ·
                  refine ⟨80434428614956510003867333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107245904819942013338489777 80434428614956510003867333)
                  ·
                    refine ⟨15081455365304345625725125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80434428614956510003867333 15081455365304345625725125)
                    ·
                      refine ⟨2827772880994564804823461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15081455365304345625725125 2827772880994564804823461)
                      ·
                        rfl

theorem cell23_5507068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_5507068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507068 prefixEnd_5507068 := by exact prefixLift 5507068
  have htrace : WordTrace (prefixWord ++ tailWord_5507068) baseStart_5507068 baseEnd_5507068 := by
    simpa [prefixWord, tailWord_5507068, baseEnd_5507068] using wordTrace_append hprefix tailTrace_5507068
  have hstable : (prefixWord ++ tailWord_5507068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507068).length < 2 ^ (prefixWord ++ tailWord_5507068).sum := by decide
  have hdescent : baseEnd_5507068 < baseStart_5507068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_5507088 : Nat := 118140960795 + 5507088 * 2 ^ 59
def prefixEnd_5507088 : Nat := 4983230072969 + 3 ^ 40 * 5507088 * 2
def baseEnd_5507088 : Nat := 2827783150607654726573369

theorem tailTrace_5507088 : CollatzResearch.WordTrace tailWord_5507088 prefixEnd_5507088 2827783150607654726573369 := by
  unfold tailWord_5507088
  simp only [CollatzResearch.WordTrace]
  refine ⟨100430000336384093297816959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133906667115178791063755945 100430000336384093297816959)
  ·
    refine ⟨150645000504576139946725439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100430000336384093297816959 150645000504576139946725439)
    ·
      refine ⟨225967500756864209920088159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150645000504576139946725439 225967500756864209920088159)
      ·
        refine ⟨338951251135296314880132239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225967500756864209920088159 338951251135296314880132239)
        ·
          refine ⟨508426876702944472320198359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338951251135296314880132239 508426876702944472320198359)
          ·
            refine ⟨762640315054416708480297539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508426876702944472320198359 762640315054416708480297539)
            ·
              refine ⟨1143960472581625062720446309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762640315054416708480297539 1143960472581625062720446309)
              ·
                refine ⟨214492588609054699260083683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1143960472581625062720446309 214492588609054699260083683)
                ·
                  refine ⟨321738882913582048890125525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214492588609054699260083683 321738882913582048890125525)
                  ·
                    refine ⟨7540755068287079270862317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 321738882913582048890125525 7540755068287079270862317)
                    ·
                      refine ⟨2827783150607654726573369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540755068287079270862317 2827783150607654726573369)
                      ·
                        rfl

theorem cell23_5507088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_5507088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507088 prefixEnd_5507088 := by exact prefixLift 5507088
  have htrace : WordTrace (prefixWord ++ tailWord_5507088) baseStart_5507088 baseEnd_5507088 := by
    simpa [prefixWord, tailWord_5507088, baseEnd_5507088] using wordTrace_append hprefix tailTrace_5507088
  have hstable : (prefixWord ++ tailWord_5507088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507088).length < 2 ^ (prefixWord ++ tailWord_5507088).sum := by decide
  have hdescent : baseEnd_5507088 < baseStart_5507088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507115 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 5, 2]
def baseStart_5507115 : Nat := 118140960795 + 5507115 * 2 ^ 59
def prefixEnd_5507115 : Nat := 4983230072969 + 3 ^ 40 * 5507115 * 2
def baseEnd_5507115 : Nat := 2827797014585326120935745

theorem tailTrace_5507115 : CollatzResearch.WordTrace tailWord_5507115 prefixEnd_5507115 2827797014585326120935745 := by
  unfold tailWord_5507115
  simp only [CollatzResearch.WordTrace]
  refine ⟨200860985443670370206866799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133907323629113580137911199 200860985443670370206866799)
  ·
    refine ⟨301291478165505555310300199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200860985443670370206866799 301291478165505555310300199)
    ·
      refine ⟨451937217248258332965450299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301291478165505555310300199 451937217248258332965450299)
      ·
        refine ⟨677905825872387499448175449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451937217248258332965450299 677905825872387499448175449)
        ·
          refine ⟨508429369404290624586131587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677905825872387499448175449 508429369404290624586131587)
          ·
            refine ⟨762644054106435936879197381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508429369404290624586131587 762644054106435936879197381)
            ·
              refine ⟨142995760144956738164849509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 762644054106435936879197381 142995760144956738164849509)
              ·
                refine ⟨26811705027179388405909283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142995760144956738164849509 26811705027179388405909283)
                ·
                  refine ⟨40217557540769082608863925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26811705027179388405909283 40217557540769082608863925)
                  ·
                    refine ⟨3770396019447101494580993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40217557540769082608863925 3770396019447101494580993)
                    ·
                      refine ⟨2827797014585326120935745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770396019447101494580993 2827797014585326120935745)
                      ·
                        rfl

theorem cell23_5507115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5, 2].length) (baseStart_5507115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507115 prefixEnd_5507115 := by exact prefixLift 5507115
  have htrace : WordTrace (prefixWord ++ tailWord_5507115) baseStart_5507115 baseEnd_5507115 := by
    simpa [prefixWord, tailWord_5507115, baseEnd_5507115] using wordTrace_append hprefix tailTrace_5507115
  have hstable : (prefixWord ++ tailWord_5507115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507115).length < 2 ^ (prefixWord ++ tailWord_5507115).sum := by decide
  have hdescent : baseEnd_5507115 < baseStart_5507115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507149 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_5507149 : Nat := 118140960795 + 5507149 * 2 ^ 59
def prefixEnd_5507149 : Nat := 4983230072969 + 3 ^ 40 * 5507149 * 2
def baseEnd_5507149 : Nat := 2827814472927578987910589

theorem tailTrace_5507149 : CollatzResearch.WordTrace tailWord_5507149 prefixEnd_5507149 2827814472927578987910589 := by
  unfold tailWord_5507149
  simp only [CollatzResearch.WordTrace]
  refine ⟨200862225525547194013604501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133908150350364796009069667 200862225525547194013604501)
  ·
    refine ⟨9415416821510024719387711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200862225525547194013604501 9415416821510024719387711)
    ·
      refine ⟨14123125232265037079081567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9415416821510024719387711 14123125232265037079081567)
      ·
        refine ⟨21184687848397555618622351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14123125232265037079081567 21184687848397555618622351)
        ·
          refine ⟨31777031772596333427933527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21184687848397555618622351 31777031772596333427933527)
          ·
            refine ⟨47665547658894500141900291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31777031772596333427933527 47665547658894500141900291)
            ·
              refine ⟨71498321488341750212850437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47665547658894500141900291 71498321488341750212850437)
              ·
                refine ⟨13405935279064078164909457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71498321488341750212850437 13405935279064078164909457)
                ·
                  refine ⟨10054451459298058623682093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13405935279064078164909457 10054451459298058623682093)
                  ·
                    refine ⟨3770419297236771983880785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10054451459298058623682093 3770419297236771983880785)
                    ·
                      refine ⟨2827814472927578987910589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770419297236771983880785 2827814472927578987910589)
                      ·
                        rfl

theorem cell23_5507149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_5507149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507149 prefixEnd_5507149 := by exact prefixLift 5507149
  have htrace : WordTrace (prefixWord ++ tailWord_5507149) baseStart_5507149 baseEnd_5507149 := by
    simpa [prefixWord, tailWord_5507149, baseEnd_5507149] using wordTrace_append hprefix tailTrace_5507149
  have hstable : (prefixWord ++ tailWord_5507149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507149).length < 2 ^ (prefixWord ++ tailWord_5507149).sum := by decide
  have hdescent : baseEnd_5507149 < baseStart_5507149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507172 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_5507172 : Nat := 118140960795 + 5507172 * 2 ^ 59
def prefixEnd_5507172 : Nat := 4983230072969 + 3 ^ 40 * 5507172 * 2
def baseEnd_5507172 : Nat := 942608760994210799307661

theorem tailTrace_5507172 : CollatzResearch.WordTrace tailWord_5507172 prefixEnd_5507172 942608760994210799307661 := by
  unfold tailWord_5507172
  simp only [CollatzResearch.WordTrace]
  refine ⟨100431532202231934470845885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133908709602975912627794513 100431532202231934470845885)
  ·
    refine ⟨37661824575836975426567207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100431532202231934470845885 37661824575836975426567207)
    ·
      refine ⟨56492736863755463139850811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37661824575836975426567207 56492736863755463139850811)
      ·
        refine ⟨84739105295633194709776217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56492736863755463139850811 84739105295633194709776217)
        ·
          refine ⟨63554328971724896032332163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84739105295633194709776217 63554328971724896032332163)
          ·
            refine ⟨95331493457587344048498245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63554328971724896032332163 95331493457587344048498245)
            ·
              refine ⟨17874655023297627009093421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95331493457587344048498245 17874655023297627009093421)
              ·
                refine ⟨6702995633736610128410033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17874655023297627009093421 6702995633736610128410033)
                ·
                  refine ⟨5027246725302457596307525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6702995633736610128410033 5027246725302457596307525)
                  ·
                    refine ⟨942608760994210799307661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027246725302457596307525 942608760994210799307661)
                    ·
                      rfl

theorem cell23_5507172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_5507172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507172 prefixEnd_5507172 := by exact prefixLift 5507172
  have htrace : WordTrace (prefixWord ++ tailWord_5507172) baseStart_5507172 baseEnd_5507172 := by
    simpa [prefixWord, tailWord_5507172, baseEnd_5507172] using wordTrace_append hprefix tailTrace_5507172
  have hstable : (prefixWord ++ tailWord_5507172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507172).length < 2 ^ (prefixWord ++ tailWord_5507172).sum := by decide
  have hdescent : baseEnd_5507172 < baseStart_5507172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507182 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_5507182 : Nat := 118140960795 + 5507182 * 2 ^ 59
def prefixEnd_5507182 : Nat := 4983230072969 + 3 ^ 40 * 5507182 * 2
def baseEnd_5507182 : Nat := 2827831417789177358797937

theorem tailTrace_5507182 : CollatzResearch.WordTrace tailWord_5507182 prefixEnd_5507182 2827831417789177358797937 := by
  unfold tailWord_5507182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25107928641803455081194475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133908952756285093766370533 25107928641803455081194475)
  ·
    refine ⟨37661892962705182621791713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25107928641803455081194475 37661892962705182621791713)
    ·
      refine ⟨28246419722028886966343785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37661892962705182621791713 28246419722028886966343785)
      ·
        refine ⟨21184814791521665224757839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28246419722028886966343785 21184814791521665224757839)
        ·
          refine ⟨31777222187282497837136759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21184814791521665224757839 31777222187282497837136759)
          ·
            refine ⟨47665833280923746755705139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31777222187282497837136759 47665833280923746755705139)
            ·
              refine ⟨71498749921385620133557709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47665833280923746755705139 71498749921385620133557709)
              ·
                refine ⟨26812031220519607550084141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71498749921385620133557709 26812031220519607550084141)
                ·
                  refine ⟨10054511707694852831281553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26812031220519607550084141 10054511707694852831281553)
                  ·
                    refine ⟨7540883780771139623461165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10054511707694852831281553 7540883780771139623461165)
                    ·
                      refine ⟨2827831417789177358797937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540883780771139623461165 2827831417789177358797937)
                      ·
                        rfl

theorem cell23_5507182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_5507182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507182 prefixEnd_5507182 := by exact prefixLift 5507182
  have htrace : WordTrace (prefixWord ++ tailWord_5507182) baseStart_5507182 baseEnd_5507182 := by
    simpa [prefixWord, tailWord_5507182, baseEnd_5507182] using wordTrace_append hprefix tailTrace_5507182
  have hstable : (prefixWord ++ tailWord_5507182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507182).length < 2 ^ (prefixWord ++ tailWord_5507182).sum := by decide
  have hdescent : baseEnd_5507182 < baseStart_5507182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507185 : List Nat := [1, 2, 2, 2, 1, 1, 7, 7]
def baseStart_5507185 : Nat := 118140960795 + 5507185 * 2 ^ 59
def prefixEnd_5507185 : Nat := 4983230072969 + 3 ^ 40 * 5507185 * 2
def baseEnd_5507185 : Nat := 104734554008560772113349

theorem tailTrace_5507185 : CollatzResearch.WordTrace tailWord_5507185 prefixEnd_5507185 104734554008560772113349 := by
  unfold tailWord_5507185
  simp only [CollatzResearch.WordTrace]
  refine ⟨200863538553416772161915009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133909025702277848107943339 200863538553416772161915009)
  ·
    refine ⟨150647653915062579121436257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200863538553416772161915009 150647653915062579121436257)
    ·
      refine ⟨112985740436296934341077193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150647653915062579121436257 112985740436296934341077193)
      ·
        refine ⟨84739305327222700755807895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112985740436296934341077193 84739305327222700755807895)
        ·
          refine ⟨127108957990834051133711843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84739305327222700755807895 127108957990834051133711843)
          ·
            refine ⟨190663436986251076700567765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127108957990834051133711843 190663436986251076700567765)
            ·
              refine ⟨4468674304365259610169557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190663436986251076700567765 4468674304365259610169557)
              ·
                refine ⟨104734554008560772113349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4468674304365259610169557 104734554008560772113349)
                ·
                  rfl

theorem cell23_5507185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 7].length) (baseStart_5507185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507185 prefixEnd_5507185 := by exact prefixLift 5507185
  have htrace : WordTrace (prefixWord ++ tailWord_5507185) baseStart_5507185 baseEnd_5507185 := by
    simpa [prefixWord, tailWord_5507185, baseEnd_5507185] using wordTrace_append hprefix tailTrace_5507185
  have hstable : (prefixWord ++ tailWord_5507185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507185).length < 2 ^ (prefixWord ++ tailWord_5507185).sum := by decide
  have hdescent : baseEnd_5507185 < baseStart_5507185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507196 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_5507196 : Nat := 118140960795 + 5507196 * 2 ^ 59
def prefixEnd_5507196 : Nat := 4983230072969 + 3 ^ 40 * 5507196 * 2
def baseEnd_5507196 : Nat := 2827838606518340304022873

theorem tailTrace_5507196 : CollatzResearch.WordTrace tailWord_5507196 prefixEnd_5507196 2827838606518340304022873 := by
  unfold tailWord_5507196
  simp only [CollatzResearch.WordTrace]
  refine ⟨100431969878188460520282721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133909293170917947360376961 100431969878188460520282721)
  ·
    refine ⟨75323977408641345390212041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100431969878188460520282721 75323977408641345390212041)
    ·
      refine ⟨56492983056481009042659031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75323977408641345390212041 56492983056481009042659031)
      ·
        refine ⟨84739474584721513563988547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56492983056481009042659031 84739474584721513563988547)
        ·
          refine ⟨127109211877082270345982821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84739474584721513563988547 127109211877082270345982821)
          ·
            refine ⟨23832977226952925689871779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127109211877082270345982821 23832977226952925689871779)
            ·
              refine ⟨35749465840429388534807669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23832977226952925689871779 35749465840429388534807669)
              ·
                refine ⟨3351512422540255175138219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35749465840429388534807669 3351512422540255175138219)
                ·
                  refine ⟨5027268633810382762707329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351512422540255175138219 5027268633810382762707329)
                  ·
                    refine ⟨3770451475357787072030497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027268633810382762707329 3770451475357787072030497)
                    ·
                      refine ⟨2827838606518340304022873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770451475357787072030497 2827838606518340304022873)
                      ·
                        rfl

theorem cell23_5507196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_5507196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507196 prefixEnd_5507196 := by exact prefixLift 5507196
  have htrace : WordTrace (prefixWord ++ tailWord_5507196) baseStart_5507196 baseEnd_5507196 := by
    simpa [prefixWord, tailWord_5507196, baseEnd_5507196] using wordTrace_append hprefix tailTrace_5507196
  have hstable : (prefixWord ++ tailWord_5507196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507196).length < 2 ^ (prefixWord ++ tailWord_5507196).sum := by decide
  have hdescent : baseEnd_5507196 < baseStart_5507196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507226 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5507226 : Nat := 118140960795 + 5507226 * 2 ^ 59
def prefixEnd_5507226 : Nat := 4983230072969 + 3 ^ 40 * 5507226 * 2
def baseEnd_5507226 : Nat := 2827854010937975186647735

theorem tailTrace_5507226 : CollatzResearch.WordTrace tailWord_5507226 prefixEnd_5507226 2827854010937975186647735 := by
  unfold tailWord_5507226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50216258486567059041039383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133910022630845490776105021 50216258486567059041039383)
  ·
    refine ⟨75324387729850588561559075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50216258486567059041039383 75324387729850588561559075)
    ·
      refine ⟨112986581594775882842338613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75324387729850588561559075 112986581594775882842338613)
      ·
        refine ⟨10592492024510239016469245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112986581594775882842338613 10592492024510239016469245)
        ·
          refine ⟨3972184509191339631175967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10592492024510239016469245 3972184509191339631175967)
          ·
            refine ⟨5958276763787009446763951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972184509191339631175967 5958276763787009446763951)
            ·
              refine ⟨8937415145680514170145927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958276763787009446763951 8937415145680514170145927)
              ·
                refine ⟨13406122718520771255218891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937415145680514170145927 13406122718520771255218891)
                ·
                  refine ⟨20109184077781156882828337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13406122718520771255218891 20109184077781156882828337)
                  ·
                    refine ⟨15081888058335867662121253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20109184077781156882828337 15081888058335867662121253)
                    ·
                      refine ⟨2827854010937975186647735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15081888058335867662121253 2827854010937975186647735)
                      ·
                        rfl

theorem cell23_5507226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5507226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507226 prefixEnd_5507226 := by exact prefixLift 5507226
  have htrace : WordTrace (prefixWord ++ tailWord_5507226) baseStart_5507226 baseEnd_5507226 := by
    simpa [prefixWord, tailWord_5507226, baseEnd_5507226] using wordTrace_append hprefix tailTrace_5507226
  have hstable : (prefixWord ++ tailWord_5507226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507226).length < 2 ^ (prefixWord ++ tailWord_5507226).sum := by decide
  have hdescent : baseEnd_5507226 < baseStart_5507226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507229 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_5507229 : Nat := 118140960795 + 5507229 * 2 ^ 59
def prefixEnd_5507229 : Nat := 4983230072969 + 3 ^ 40 * 5507229 * 2
def baseEnd_5507229 : Nat := 2827855551379938674910221

theorem tailTrace_5507229 : CollatzResearch.WordTrace tailWord_5507229 prefixEnd_5507229 2827855551379938674910221 := by
  unfold tailWord_5507229
  simp only [CollatzResearch.WordTrace]
  refine ⟨200865143365257367676516741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133910095576838245117677827 200865143365257367676516741)
  ·
    refine ⟨37662214380985756439346889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200865143365257367676516741 37662214380985756439346889)
    ·
      refine ⟨28246660785739317329510167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37662214380985756439346889 28246660785739317329510167)
      ·
        refine ⟨42369991178608975994265251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28246660785739317329510167 42369991178608975994265251)
        ·
          refine ⟨63554986767913463991397877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42369991178608975994265251 63554986767913463991397877)
          ·
            refine ⟨5958280009491887249193551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63554986767913463991397877 5958280009491887249193551)
            ·
              refine ⟨8937420014237830873790327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5958280009491887249193551 8937420014237830873790327)
              ·
                refine ⟨13406130021356746310685491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937420014237830873790327 13406130021356746310685491)
                ·
                  refine ⟨20109195032035119466028237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13406130021356746310685491 20109195032035119466028237)
                  ·
                    refine ⟨7540948137013169799760589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20109195032035119466028237 7540948137013169799760589)
                    ·
                      refine ⟨2827855551379938674910221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7540948137013169799760589 2827855551379938674910221)
                      ·
                        rfl

theorem cell23_5507229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_5507229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507229 prefixEnd_5507229 := by exact prefixLift 5507229
  have htrace : WordTrace (prefixWord ++ tailWord_5507229) baseStart_5507229 baseEnd_5507229 := by
    simpa [prefixWord, tailWord_5507229, baseEnd_5507229] using wordTrace_append hprefix tailTrace_5507229
  have hstable : (prefixWord ++ tailWord_5507229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507229).length < 2 ^ (prefixWord ++ tailWord_5507229).sum := by decide
  have hdescent : baseEnd_5507229 < baseStart_5507229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507255 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_5507255 : Nat := 118140960795 + 5507255 * 2 ^ 59
def prefixEnd_5507255 : Nat := 4983230072969 + 3 ^ 40 * 5507255 * 2
def baseEnd_5507255 : Nat := 2827868901876955573185101

theorem tailTrace_5507255 : CollatzResearch.WordTrace tailWord_5507255 prefixEnd_5507255 2827868901876955573185101 := by
  unfold tailWord_5507255
  simp only [CollatzResearch.WordTrace]
  refine ⟨200866091663163174116963219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133910727775442116077975479 200866091663163174116963219)
  ·
    refine ⟨301299137494744761175444829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200866091663163174116963219 301299137494744761175444829)
    ·
      refine ⟨112987176560529285440791811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301299137494744761175444829 112987176560529285440791811)
      ·
        refine ⟨169480764840793928161187717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112987176560529285440791811 169480764840793928161187717)
        ·
          refine ⟨31777643407648861530222697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169480764840793928161187717 31777643407648861530222697)
          ·
            refine ⟨23833232555736646147667023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31777643407648861530222697 23833232555736646147667023)
            ·
              refine ⟨35749848833604969221500535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23833232555736646147667023 35749848833604969221500535)
              ·
                refine ⟨53624773250407453832250803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35749848833604969221500535 53624773250407453832250803)
                ·
                  refine ⟨80437159875611180748376205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53624773250407453832250803 80437159875611180748376205)
                  ·
                    refine ⟨30163934953354192780641077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80437159875611180748376205 30163934953354192780641077)
                    ·
                      refine ⟨2827868901876955573185101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30163934953354192780641077 2827868901876955573185101)
                      ·
                        rfl

theorem cell23_5507255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_5507255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507255 prefixEnd_5507255 := by exact prefixLift 5507255
  have htrace : WordTrace (prefixWord ++ tailWord_5507255) baseStart_5507255 baseEnd_5507255 := by
    simpa [prefixWord, tailWord_5507255, baseEnd_5507255] using wordTrace_append hprefix tailTrace_5507255
  have hstable : (prefixWord ++ tailWord_5507255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507255).length < 2 ^ (prefixWord ++ tailWord_5507255).sum := by decide
  have hdescent : baseEnd_5507255 < baseStart_5507255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507269 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_5507269 : Nat := 118140960795 + 5507269 * 2 ^ 59
def prefixEnd_5507269 : Nat := 4983230072969 + 3 ^ 40 * 5507269 * 2
def baseEnd_5507269 : Nat := 2827876090606118518410037

theorem tailTrace_5507269 : CollatzResearch.WordTrace tailWord_5507269 prefixEnd_5507269 2827876090606118518410037 := by
  unfold tailWord_5507269
  simp only [CollatzResearch.WordTrace]
  refine ⟨200866602285112454507972861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133911068190074969671981907 200866602285112454507972861)
  ·
    refine ⟨75324975856917170440489823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200866602285112454507972861 75324975856917170440489823)
    ·
      refine ⟨112987463785375755660734735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75324975856917170440489823 112987463785375755660734735)
      ·
        refine ⟨169481195678063633491102103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112987463785375755660734735 169481195678063633491102103)
        ·
          refine ⟨254221793517095450236653155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169481195678063633491102103 254221793517095450236653155)
          ·
            refine ⟨381332690275643175354979733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254221793517095450236653155 381332690275643175354979733)
            ·
              refine ⟨17874969856670773844764675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 381332690275643175354979733 17874969856670773844764675)
              ·
                refine ⟨26812454785006160767147013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17874969856670773844764675 26812454785006160767147013)
                ·
                  refine ⟨5027335272188655143840065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26812454785006160767147013 5027335272188655143840065)
                  ·
                    refine ⟨3770501454141491357880049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027335272188655143840065 3770501454141491357880049)
                    ·
                      refine ⟨2827876090606118518410037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770501454141491357880049 2827876090606118518410037)
                      ·
                        rfl

theorem cell23_5507269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_5507269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507269 prefixEnd_5507269 := by exact prefixLift 5507269
  have htrace : WordTrace (prefixWord ++ tailWord_5507269) baseStart_5507269 baseEnd_5507269 := by
    simpa [prefixWord, tailWord_5507269, baseEnd_5507269] using wordTrace_append hprefix tailTrace_5507269
  have hstable : (prefixWord ++ tailWord_5507269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507269).length < 2 ^ (prefixWord ++ tailWord_5507269).sum := by decide
  have hdescent : baseEnd_5507269 < baseStart_5507269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507305 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_5507305 : Nat := 118140960795 + 5507305 * 2 ^ 59
def prefixEnd_5507305 : Nat := 4983230072969 + 3 ^ 40 * 5507305 * 2
def baseEnd_5507305 : Nat := 942631525303226792519957

theorem tailTrace_5507305 : CollatzResearch.WordTrace tailWord_5507305 prefixEnd_5507305 942631525303226792519957 := by
  unfold tailWord_5507305
  simp only [CollatzResearch.WordTrace]
  refine ⟨200867915312982032656283369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133911943541988021770855579 200867915312982032656283369)
  ·
    refine ⟨150650936484736524492212527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200867915312982032656283369 150650936484736524492212527)
    ·
      refine ⟨225976404727104786738318791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150650936484736524492212527 225976404727104786738318791)
      ·
        refine ⟨338964607090657180107478187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225976404727104786738318791 338964607090657180107478187)
        ·
          refine ⟨508446910635985770161217281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338964607090657180107478187 508446910635985770161217281)
          ·
            refine ⟨381335182976989327620912961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508446910635985770161217281 381335182976989327620912961)
            ·
              refine ⟨286001387232741995715684721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381335182976989327620912961 286001387232741995715684721)
              ·
                refine ⟨214501040424556496786763541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286001387232741995715684721 214501040424556496786763541)
                ·
                  refine ⟨10054736269901085786879541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214501040424556496786763541 10054736269901085786879541)
                  ·
                    refine ⟨942631525303226792519957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10054736269901085786879541 942631525303226792519957)
                    ·
                      rfl

theorem cell23_5507305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_5507305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507305 prefixEnd_5507305 := by exact prefixLift 5507305
  have htrace : WordTrace (prefixWord ++ tailWord_5507305) baseStart_5507305 baseEnd_5507305 := by
    simpa [prefixWord, tailWord_5507305, baseEnd_5507305] using wordTrace_append hprefix tailTrace_5507305
  have hstable : (prefixWord ++ tailWord_5507305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507305).length < 2 ^ (prefixWord ++ tailWord_5507305).sum := by decide
  have hdescent : baseEnd_5507305 < baseStart_5507305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507312 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2]
def baseStart_5507312 : Nat := 118140960795 + 5507312 * 2 ^ 59
def prefixEnd_5507312 : Nat := 4983230072969 + 3 ^ 40 * 5507312 * 2
def baseEnd_5507312 : Nat := 2827898170274261850172339

theorem tailTrace_5507312 : CollatzResearch.WordTrace tailWord_5507312 prefixEnd_5507312 2827898170274261850172339 := by
  unfold tailWord_5507312
  simp only [CollatzResearch.WordTrace]
  refine ⟨100434085311978336425894095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133912113749304448567858793 100434085311978336425894095)
  ·
    refine ⟨150651127967967504638841143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100434085311978336425894095 150651127967967504638841143)
    ·
      refine ⟨225976691951951256958261715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150651127967967504638841143 225976691951951256958261715)
      ·
        refine ⟨338965037927926885437392573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225976691951951256958261715 338965037927926885437392573)
        ·
          refine ⟨127111889222972582039022215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338965037927926885437392573 127111889222972582039022215)
          ·
            refine ⟨190667833834458873058533323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127111889222972582039022215 190667833834458873058533323)
            ·
              refine ⟨286001750751688309587799985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190667833834458873058533323 286001750751688309587799985)
              ·
                refine ⟨214501313063766232190849989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286001750751688309587799985 214501313063766232190849989)
                ·
                  refine ⟨40218996199456168535784373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214501313063766232190849989 40218996199456168535784373)
                  ·
                    refine ⟨3770530893699015800229785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40218996199456168535784373 3770530893699015800229785)
                    ·
                      refine ⟨2827898170274261850172339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770530893699015800229785 2827898170274261850172339)
                      ·
                        rfl

theorem cell23_5507312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2].length) (baseStart_5507312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507312 prefixEnd_5507312 := by exact prefixLift 5507312
  have htrace : WordTrace (prefixWord ++ tailWord_5507312) baseStart_5507312 baseEnd_5507312 := by
    simpa [prefixWord, tailWord_5507312, baseEnd_5507312] using wordTrace_append hprefix tailTrace_5507312
  have hstable : (prefixWord ++ tailWord_5507312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507312).length < 2 ^ (prefixWord ++ tailWord_5507312).sum := by decide
  have hdescent : baseEnd_5507312 < baseStart_5507312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507315 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_5507315 : Nat := 118140960795 + 5507315 * 2 ^ 59
def prefixEnd_5507315 : Nat := 4983230072969 + 3 ^ 40 * 5507315 * 2
def baseEnd_5507315 : Nat := 2827899710716225338434825

theorem tailTrace_5507315 : CollatzResearch.WordTrace tailWord_5507315 prefixEnd_5507315 2827899710716225338434825 := by
  unfold tailWord_5507315
  simp only [CollatzResearch.WordTrace]
  refine ⟨200868280042945804364147399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133912186695297202909431599 200868280042945804364147399)
  ·
    refine ⟨301302420064418706546221099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200868280042945804364147399 301302420064418706546221099)
    ·
      refine ⟨451953630096628059819331649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301302420064418706546221099 451953630096628059819331649)
      ·
        refine ⟨338965222572471044864498737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451953630096628059819331649 338965222572471044864498737)
        ·
          refine ⟨254223916929353283648374053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338965222572471044864498737 254223916929353283648374053)
          ·
            refine ⟨47666984424253740684070135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254223916929353283648374053 47666984424253740684070135)
            ·
              refine ⟨71500476636380611026105203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47666984424253740684070135 71500476636380611026105203)
              ·
                refine ⟨107250714954570916539157805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71500476636380611026105203 107250714954570916539157805)
                ·
                  refine ⟨40219018107964093702184177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107250714954570916539157805 40219018107964093702184177)
                  ·
                    refine ⟨30164263580973070276638133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40219018107964093702184177 30164263580973070276638133)
                    ·
                      refine ⟨2827899710716225338434825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30164263580973070276638133 2827899710716225338434825)
                      ·
                        rfl

theorem cell23_5507315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_5507315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507315 prefixEnd_5507315 := by exact prefixLift 5507315
  have htrace : WordTrace (prefixWord ++ tailWord_5507315) baseStart_5507315 baseEnd_5507315 := by
    simpa [prefixWord, tailWord_5507315, baseEnd_5507315] using wordTrace_append hprefix tailTrace_5507315
  have hstable : (prefixWord ++ tailWord_5507315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507315).length < 2 ^ (prefixWord ++ tailWord_5507315).sum := by decide
  have hdescent : baseEnd_5507315 < baseStart_5507315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507322 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_5507322 : Nat := 118140960795 + 5507322 * 2 ^ 59
def prefixEnd_5507322 : Nat := 4983230072969 + 3 ^ 40 * 5507322 * 2
def baseEnd_5507322 : Nat := 942634435026935603682431

theorem tailTrace_5507322 : CollatzResearch.WordTrace tailWord_5507322 prefixEnd_5507322 942634435026935603682431 := by
  unfold tailWord_5507322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50217133838480111139913055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133912356902613629706434813 50217133838480111139913055)
  ·
    refine ⟨75325700757720166709869583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50217133838480111139913055 75325700757720166709869583)
    ·
      refine ⟨112988551136580250064804375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75325700757720166709869583 112988551136580250064804375)
      ·
        refine ⟨169482826704870375097206563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112988551136580250064804375 169482826704870375097206563)
        ·
          refine ⟨254224240057305562645809845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169482826704870375097206563 254224240057305562645809845)
          ·
            refine ⟨23833522505372396498044673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254224240057305562645809845 23833522505372396498044673)
            ·
              refine ⟨17875141879029297373533505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23833522505372396498044673 17875141879029297373533505)
              ·
                refine ⟨13406356409271973030150129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17875141879029297373533505 13406356409271973030150129)
                ·
                  refine ⟨10054767306953979772612597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13406356409271973030150129 10054767306953979772612597)
                  ·
                    refine ⟨942634435026935603682431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10054767306953979772612597 942634435026935603682431)
                    ·
                      rfl

theorem cell23_5507322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_5507322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507322 prefixEnd_5507322 := by exact prefixLift 5507322
  have htrace : WordTrace (prefixWord ++ tailWord_5507322) baseStart_5507322 baseEnd_5507322 := by
    simpa [prefixWord, tailWord_5507322, baseEnd_5507322] using wordTrace_append hprefix tailTrace_5507322
  have hstable : (prefixWord ++ tailWord_5507322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507322).length < 2 ^ (prefixWord ++ tailWord_5507322).sum := by decide
  have hdescent : baseEnd_5507322 < baseStart_5507322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507342 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5507342 : Nat := 118140960795 + 5507342 * 2 ^ 59
def prefixEnd_5507342 : Nat := 4983230072969 + 3 ^ 40 * 5507342 * 2
def baseEnd_5507342 : Nat := 2827913574693896732797201

theorem tailTrace_5507342 : CollatzResearch.WordTrace tailWord_5507342 prefixEnd_5507342 2827913574693896732797201 := by
  unfold tailWord_5507342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25108658101730998496922535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133912843209231991983586853 25108658101730998496922535)
  ·
    refine ⟨37662987152596497745383803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25108658101730998496922535 37662987152596497745383803)
    ·
      refine ⟨56494480728894746618075705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37662987152596497745383803 56494480728894746618075705)
      ·
        refine ⟨42370860546671059963556779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56494480728894746618075705 42370860546671059963556779)
        ·
          refine ⟨63556290820006589945335169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42370860546671059963556779 63556290820006589945335169)
          ·
            refine ⟨47667218115004942459001377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63556290820006589945335169 47667218115004942459001377)
            ·
              refine ⟨35750413586253706844251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47667218115004942459001377 35750413586253706844251033)
              ·
                refine ⟨26812810189690280133188275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35750413586253706844251033 26812810189690280133188275)
                ·
                  refine ⟨40219215284535420199782413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26812810189690280133188275 40219215284535420199782413)
                  ·
                    refine ⟨15082205731700782574918405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40219215284535420199782413 15082205731700782574918405)
                    ·
                      refine ⟨2827913574693896732797201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15082205731700782574918405 2827913574693896732797201)
                      ·
                        rfl

theorem cell23_5507342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5507342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507342 prefixEnd_5507342 := by exact prefixLift 5507342
  have htrace : WordTrace (prefixWord ++ tailWord_5507342) baseStart_5507342 baseEnd_5507342 := by
    simpa [prefixWord, tailWord_5507342, baseEnd_5507342] using wordTrace_append hprefix tailTrace_5507342
  have hstable : (prefixWord ++ tailWord_5507342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507342).length < 2 ^ (prefixWord ++ tailWord_5507342).sum := by decide
  have hdescent : baseEnd_5507342 < baseStart_5507342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507359 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_5507359 : Nat := 118140960795 + 5507359 * 2 ^ 59
def prefixEnd_5507359 : Nat := 4983230072969 + 3 ^ 40 * 5507359 * 2
def baseEnd_5507359 : Nat := 2827922303865023166284623

theorem tailTrace_5507359 : CollatzResearch.WordTrace tailWord_5507359 prefixEnd_5507359 2827922303865023166284623 := by
  unfold tailWord_5507359
  simp only [CollatzResearch.WordTrace]
  refine ⟨200869884854786399878749131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133913256569857599919166087 200869884854786399878749131)
  ·
    refine ⟨301304827282179599818123697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200869884854786399878749131 301304827282179599818123697)
    ·
      refine ⟨225978620461634699863592773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301304827282179599818123697 225978620461634699863592773)
      ·
        refine ⟨42370991336556506224423645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225978620461634699863592773 42370991336556506224423645)
        ·
          refine ⟨15889121751208689834158867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42370991336556506224423645 15889121751208689834158867)
          ·
            refine ⟨23833682626813034751238301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889121751208689834158867 23833682626813034751238301)
            ·
              refine ⟨8937630985054888031714363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23833682626813034751238301 8937630985054888031714363)
              ·
                refine ⟨13406446477582332047571545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8937630985054888031714363 13406446477582332047571545)
                ·
                  refine ⟨10054834858186749035678659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13406446477582332047571545 10054834858186749035678659)
                  ·
                    refine ⟨15082252287280123553517989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10054834858186749035678659 15082252287280123553517989)
                    ·
                      refine ⟨2827922303865023166284623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15082252287280123553517989 2827922303865023166284623)
                      ·
                        rfl

theorem cell23_5507359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_5507359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507359 prefixEnd_5507359 := by exact prefixLift 5507359
  have htrace : WordTrace (prefixWord ++ tailWord_5507359) baseStart_5507359 baseEnd_5507359 := by
    simpa [prefixWord, tailWord_5507359, baseEnd_5507359] using wordTrace_append hprefix tailTrace_5507359
  have hstable : (prefixWord ++ tailWord_5507359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507359).length < 2 ^ (prefixWord ++ tailWord_5507359).sum := by decide
  have hdescent : baseEnd_5507359 < baseStart_5507359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507386 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_5507386 : Nat := 118140960795 + 5507386 * 2 ^ 59
def prefixEnd_5507386 : Nat := 4983230072969 + 3 ^ 40 * 5507386 * 2
def baseEnd_5507386 : Nat := 942645389280898186882333

theorem tailTrace_5507386 : CollatzResearch.WordTrace tailWord_5507386 prefixEnd_5507386 942645389280898186882333 := by
  unfold tailWord_5507386
  simp only [CollatzResearch.WordTrace]
  refine ⟨50217717406422145872495503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133913913083792388993321341 50217717406422145872495503)
  ·
    refine ⟨75326576109633218808743255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50217717406422145872495503 75326576109633218808743255)
    ·
      refine ⟨112989864164449828213114883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75326576109633218808743255 112989864164449828213114883)
      ·
        refine ⟨169484796246674742319672325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112989864164449828213114883 169484796246674742319672325)
        ·
          refine ⟨31778399296251514184938561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169484796246674742319672325 31778399296251514184938561)
          ·
            refine ⟨23833799472188635638703921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31778399296251514184938561 23833799472188635638703921)
            ·
              refine ⟨17875349604141476729027941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23833799472188635638703921 17875349604141476729027941)
              ·
                refine ⟨3351628050776526886692739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17875349604141476729027941 3351628050776526886692739)
                ·
                  refine ⟨5027442076164790330039109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351628050776526886692739 5027442076164790330039109)
                  ·
                    refine ⟨942645389280898186882333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027442076164790330039109 942645389280898186882333)
                    ·
                      rfl

theorem cell23_5507386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_5507386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507386 prefixEnd_5507386 := by exact prefixLift 5507386
  have htrace : WordTrace (prefixWord ++ tailWord_5507386) baseStart_5507386 baseEnd_5507386 := by
    simpa [prefixWord, tailWord_5507386, baseEnd_5507386] using wordTrace_append hprefix tailTrace_5507386
  have hstable : (prefixWord ++ tailWord_5507386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507386).length < 2 ^ (prefixWord ++ tailWord_5507386).sum := by decide
  have hdescent : baseEnd_5507386 < baseStart_5507386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507399 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 6]
def baseStart_5507399 : Nat := 118140960795 + 5507399 * 2 ^ 59
def prefixEnd_5507399 : Nat := 4983230072969 + 3 ^ 40 * 5507399 * 2
def baseEnd_5507399 : Nat := 314215871454578112198271

theorem tailTrace_5507399 : CollatzResearch.WordTrace tailWord_5507399 prefixEnd_5507399 314215871454578112198271 := by
  unfold tailWord_5507399
  simp only [CollatzResearch.WordTrace]
  refine ⟨200871343774641486710205251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133914229183094324473470167 200871343774641486710205251)
  ·
    refine ⟨301307015661962230065307877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200871343774641486710205251 301307015661962230065307877)
    ·
      refine ⟨56495065436617918137245227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301307015661962230065307877 56495065436617918137245227)
      ·
        refine ⟨84742598154926877205867841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56495065436617918137245227 84742598154926877205867841)
        ·
          refine ⟨63556948616195157904400881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84742598154926877205867841 63556948616195157904400881)
          ·
            refine ⟨47667711462146368428300661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63556948616195157904400881 47667711462146368428300661)
            ·
              refine ⟨4468847949576222040153187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47667711462146368428300661 4468847949576222040153187)
              ·
                refine ⟨6703271924364333060229781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468847949576222040153187 6703271924364333060229781)
                ·
                  refine ⟨314215871454578112198271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6703271924364333060229781 314215871454578112198271)
                  ·
                    rfl

theorem cell23_5507399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 6].length) (baseStart_5507399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507399 prefixEnd_5507399 := by exact prefixLift 5507399
  have htrace : WordTrace (prefixWord ++ tailWord_5507399) baseStart_5507399 baseEnd_5507399 := by
    simpa [prefixWord, tailWord_5507399, baseEnd_5507399] using wordTrace_append hprefix tailTrace_5507399
  have hstable : (prefixWord ++ tailWord_5507399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507399).length < 2 ^ (prefixWord ++ tailWord_5507399).sum := by decide
  have hdescent : baseEnd_5507399 < baseStart_5507399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507429 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_5507429 : Nat := 118140960795 + 5507429 * 2 ^ 59
def prefixEnd_5507429 : Nat := 4983230072969 + 3 ^ 40 * 5507429 * 2
def baseEnd_5507429 : Nat := 942652749170279297469767

theorem tailTrace_5507429 : CollatzResearch.WordTrace tailWord_5507429 prefixEnd_5507429 942652749170279297469767 := by
  unfold tailWord_5507429
  simp only [CollatzResearch.WordTrace]
  refine ⟨200872437964532801833797341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133914958643021867889198227 200872437964532801833797341)
  ·
    refine ⟨75327164236699800687674003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200872437964532801833797341 75327164236699800687674003)
    ·
      refine ⟨112990746355049701031511005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75327164236699800687674003 112990746355049701031511005)
      ·
        refine ⟨42371529883143637886816627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112990746355049701031511005 42371529883143637886816627)
        ·
          refine ⟨63557294824715456830224941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42371529883143637886816627 63557294824715456830224941)
          ·
            refine ⟨23833985559268296311334353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63557294824715456830224941 23833985559268296311334353)
            ·
              refine ⟨17875489169451222233500765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23833985559268296311334353 17875489169451222233500765)
              ·
                refine ⟨6703308438544208337562787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17875489169451222233500765 6703308438544208337562787)
                ·
                  refine ⟨10054962657816312506344181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6703308438544208337562787 10054962657816312506344181)
                  ·
                    refine ⟨942652749170279297469767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10054962657816312506344181 942652749170279297469767)
                    ·
                      rfl

theorem cell23_5507429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_5507429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507429 prefixEnd_5507429 := by exact prefixLift 5507429
  have htrace : WordTrace (prefixWord ++ tailWord_5507429) baseStart_5507429 baseEnd_5507429 := by
    simpa [prefixWord, tailWord_5507429, baseEnd_5507429] using wordTrace_append hprefix tailTrace_5507429
  have hstable : (prefixWord ++ tailWord_5507429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507429).length < 2 ^ (prefixWord ++ tailWord_5507429).sum := by decide
  have hdescent : baseEnd_5507429 < baseStart_5507429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507452 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_5507452 : Nat := 118140960795 + 5507452 * 2 ^ 59
def prefixEnd_5507452 : Nat := 4983230072969 + 3 ^ 40 * 5507452 * 2
def baseEnd_5507452 : Nat := 2827970057565891302421695

theorem tailTrace_5507452 : CollatzResearch.WordTrace tailWord_5507452 prefixEnd_5507452 2827970057565891302421695 := by
  unfold tailWord_5507452
  simp only [CollatzResearch.WordTrace]
  refine ⟨100436638421724738380942305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133915517895632984507923073 100436638421724738380942305)
  ·
    refine ⟨75327478816293553785706729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100436638421724738380942305 75327478816293553785706729)
    ·
      refine ⟨56495609112220165339280047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75327478816293553785706729 56495609112220165339280047)
      ·
        refine ⟨84743413668330248008920071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56495609112220165339280047 84743413668330248008920071)
        ·
          refine ⟨127115120502495372013380107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84743413668330248008920071 127115120502495372013380107)
          ·
            refine ⟨190672680753743058020070161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127115120502495372013380107 190672680753743058020070161)
            ·
              refine ⟨143004510565307293515052621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190672680753743058020070161 143004510565307293515052621)
              ·
                refine ⟨53626691461990235068144733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143004510565307293515052621 53626691461990235068144733)
                ·
                  refine ⟨20110009298246338150554275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53626691461990235068144733 20110009298246338150554275)
                  ·
                    refine ⟨30165013947369507225831413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20110009298246338150554275 30165013947369507225831413)
                    ·
                      refine ⟨2827970057565891302421695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30165013947369507225831413 2827970057565891302421695)
                      ·
                        rfl

theorem cell23_5507452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_5507452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507452 prefixEnd_5507452 := by exact prefixLift 5507452
  have htrace : WordTrace (prefixWord ++ tailWord_5507452) baseStart_5507452 baseEnd_5507452 := by
    simpa [prefixWord, tailWord_5507452, baseEnd_5507452] using wordTrace_append hprefix tailTrace_5507452
  have hstable : (prefixWord ++ tailWord_5507452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507452).length < 2 ^ (prefixWord ++ tailWord_5507452).sum := by decide
  have hdescent : baseEnd_5507452 < baseStart_5507452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507476 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5507476 : Nat := 118140960795 + 5507476 * 2 ^ 59
def prefixEnd_5507476 : Nat := 4983230072969 + 3 ^ 40 * 5507476 * 2
def baseEnd_5507476 : Nat := 942660793700533069507195

theorem tailTrace_5507476 : CollatzResearch.WordTrace tailWord_5507476 prefixEnd_5507476 942660793700533069507195 := by
  unfold tailWord_5507476
  simp only [CollatzResearch.WordTrace]
  refine ⟨100437076097681264430379141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133916101463575019240505521 100437076097681264430379141)
  ·
    refine ⟨18831951768315237080696089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100437076097681264430379141 18831951768315237080696089)
    ·
      refine ⟨14123963826236427810522067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18831951768315237080696089 14123963826236427810522067)
      ·
        refine ⟨21185945739354641715783101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14123963826236427810522067 21185945739354641715783101)
        ·
          refine ⟨7944729652257990643418663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21185945739354641715783101 7944729652257990643418663)
          ·
            refine ⟨11917094478386985965127995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7944729652257990643418663 11917094478386985965127995)
            ·
              refine ⟨17875641717580478947691993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11917094478386985965127995 17875641717580478947691993)
              ·
                refine ⟨13406731288185359210768995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17875641717580478947691993 13406731288185359210768995)
                ·
                  refine ⟨20110096932278038816153493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13406731288185359210768995 20110096932278038816153493)
                  ·
                    refine ⟨942660793700533069507195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20110096932278038816153493 942660793700533069507195)
                    ·
                      rfl

theorem cell23_5507476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5507476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507476 prefixEnd_5507476 := by exact prefixLift 5507476
  have htrace : WordTrace (prefixWord ++ tailWord_5507476) baseStart_5507476 baseEnd_5507476 := by
    simpa [prefixWord, tailWord_5507476, baseEnd_5507476] using wordTrace_append hprefix tailTrace_5507476
  have hstable : (prefixWord ++ tailWord_5507476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507476).length < 2 ^ (prefixWord ++ tailWord_5507476).sum := by decide
  have hdescent : baseEnd_5507476 < baseStart_5507476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507489 : List Nat := [1, 2, 3, 5, 1, 11]
def baseStart_5507489 : Nat := 118140960795 + 5507489 * 2 ^ 59
def prefixEnd_5507489 : Nat := 4983230072969 + 3 ^ 40 * 5507489 * 2
def baseEnd_5507489 : Nat := 11637815046708261965675

theorem tailTrace_5507489 : CollatzResearch.WordTrace tailWord_5507489 prefixEnd_5507489 11637815046708261965675 := by
  unfold tailWord_5507489
  simp only [CollatzResearch.WordTrace]
  refine ⟨200874626344315432080981521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133916417562876954720654347 200874626344315432080981521)
  ·
    refine ⟨150655969758236574060736141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200874626344315432080981521 150655969758236574060736141)
    ·
      refine ⟨56495988659338715272776053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150655969758236574060736141 56495988659338715272776053)
      ·
        refine ⟨5296498936813004556822755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56495988659338715272776053 5296498936813004556822755)
        ·
          refine ⟨7944748405219506835234133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296498936813004556822755 7944748405219506835234133)
          ·
            refine ⟨11637815046708261965675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7944748405219506835234133 11637815046708261965675)
            ·
              rfl

theorem cell23_5507489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 11].length) (baseStart_5507489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507489 prefixEnd_5507489 := by exact prefixLift 5507489
  have htrace : WordTrace (prefixWord ++ tailWord_5507489) baseStart_5507489 baseEnd_5507489 := by
    simpa [prefixWord, tailWord_5507489, baseEnd_5507489] using wordTrace_append hprefix tailTrace_5507489
  have hstable : (prefixWord ++ tailWord_5507489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507489).length < 2 ^ (prefixWord ++ tailWord_5507489).sum := by decide
  have hdescent : baseEnd_5507489 < baseStart_5507489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507512 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_5507512 : Nat := 118140960795 + 5507512 * 2 ^ 59
def prefixEnd_5507512 : Nat := 4983230072969 + 3 ^ 40 * 5507512 * 2
def baseEnd_5507512 : Nat := 2828000866405161067671419

theorem tailTrace_5507512 : CollatzResearch.WordTrace tailWord_5507512 prefixEnd_5507512 2828000866405161067671419 := by
  unfold tailWord_5507512
  simp only [CollatzResearch.WordTrace]
  refine ⟨100437732611616053504534395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133916976815488071339379193 100437732611616053504534395)
  ·
    refine ⟨150656598917424080256801593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100437732611616053504534395 150656598917424080256801593)
    ·
      refine ⟨112992449188068060192601195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150656598917424080256801593 112992449188068060192601195)
      ·
        refine ⟨169488673782102090288901793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112992449188068060192601195 169488673782102090288901793)
        ·
          refine ⟨127116505336576567716676345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169488673782102090288901793 127116505336576567716676345)
          ·
            refine ⟨95337379002432425787507259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127116505336576567716676345 95337379002432425787507259)
            ·
              refine ⟨143006068503648638681260889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95337379002432425787507259 143006068503648638681260889)
              ·
                refine ⟨107254551377736479010945667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143006068503648638681260889 107254551377736479010945667)
                ·
                  refine ⟨160881827066604718516418501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107254551377736479010945667 160881827066604718516418501)
                  ·
                    refine ⟨30165342574988384721828469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160881827066604718516418501 30165342574988384721828469)
                    ·
                      refine ⟨2828000866405161067671419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30165342574988384721828469 2828000866405161067671419)
                      ·
                        rfl

theorem cell23_5507512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_5507512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507512 prefixEnd_5507512 := by exact prefixLift 5507512
  have htrace : WordTrace (prefixWord ++ tailWord_5507512) baseStart_5507512 baseEnd_5507512 := by
    simpa [prefixWord, tailWord_5507512, baseEnd_5507512] using wordTrace_append hprefix tailTrace_5507512
  have hstable : (prefixWord ++ tailWord_5507512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507512).length < 2 ^ (prefixWord ++ tailWord_5507512).sum := by decide
  have hdescent : baseEnd_5507512 < baseStart_5507512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507516 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5507516 : Nat := 118140960795 + 5507516 * 2 ^ 59
def prefixEnd_5507516 : Nat := 4983230072969 + 3 ^ 40 * 5507516 * 2
def baseEnd_5507516 : Nat := 2828002920327779052021401

theorem tailTrace_5507516 : CollatzResearch.WordTrace tailWord_5507516 prefixEnd_5507516 2828002920327779052021401 := by
  unfold tailWord_5507516
  simp only [CollatzResearch.WordTrace]
  refine ⟨100437805557608807846107201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133917074076811743794809601 100437805557608807846107201)
  ·
    refine ⟨75328354168206605884580401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100437805557608807846107201 75328354168206605884580401)
    ·
      refine ⟨56496265626154954413435301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75328354168206605884580401 56496265626154954413435301)
      ·
        refine ⟨10593049804904053952519119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56496265626154954413435301 10593049804904053952519119)
        ·
          refine ⟨15889574707356080928778679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10593049804904053952519119 15889574707356080928778679)
          ·
            refine ⟨23834362061034121393168019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889574707356080928778679 23834362061034121393168019)
            ·
              refine ⟨35751543091551182089752029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23834362061034121393168019 35751543091551182089752029)
              ·
                refine ⟨13406828659331693283657011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35751543091551182089752029 13406828659331693283657011)
                ·
                  refine ⟨20110242988997539925485517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13406828659331693283657011 20110242988997539925485517)
                  ·
                    refine ⟨7541341120874077472057069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20110242988997539925485517 7541341120874077472057069)
                    ·
                      refine ⟨2828002920327779052021401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7541341120874077472057069 2828002920327779052021401)
                      ·
                        rfl

theorem cell23_5507516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5507516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507516 prefixEnd_5507516 := by exact prefixLift 5507516
  have htrace : WordTrace (prefixWord ++ tailWord_5507516) baseStart_5507516 baseEnd_5507516 := by
    simpa [prefixWord, tailWord_5507516, baseEnd_5507516] using wordTrace_append hprefix tailTrace_5507516
  have hstable : (prefixWord ++ tailWord_5507516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507516).length < 2 ^ (prefixWord ++ tailWord_5507516).sum := by decide
  have hdescent : baseEnd_5507516 < baseStart_5507516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 8, 2]
def baseStart_5507539 : Nat := 118140960795 + 5507539 * 2 ^ 59
def prefixEnd_5507539 : Nat := 4983230072969 + 3 ^ 40 * 5507539 * 2
def baseEnd_5507539 : Nat := 2828014730382832462033795

theorem tailTrace_5507539 : CollatzResearch.WordTrace tailWord_5507539 prefixEnd_5507539 2828014730382832462033795 := by
  unfold tailWord_5507539
  simp only [CollatzResearch.WordTrace]
  refine ⟨200876449994134290620301671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133917633329422860413534447 200876449994134290620301671)
  ·
    refine ⟨301314674991201435930452507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200876449994134290620301671 301314674991201435930452507)
    ·
      refine ⟨451972012486802153895678761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301314674991201435930452507 451972012486802153895678761)
      ·
        refine ⟨338979009365101615421759071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451972012486802153895678761 338979009365101615421759071)
        ·
          refine ⟨508468514047652423132638607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338979009365101615421759071 508468514047652423132638607)
          ·
            refine ⟨762702771071478634698957911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508468514047652423132638607 762702771071478634698957911)
            ·
              refine ⟨1144054156607217952048436867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762702771071478634698957911 1144054156607217952048436867)
              ·
                refine ⟨1716081234910826928072655301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144054156607217952048436867 1716081234910826928072655301)
                ·
                  refine ⟨321765231545780049013622869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716081234910826928072655301 321765231545780049013622869)
                  ·
                    refine ⟨3770686307177109949378393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 321765231545780049013622869 3770686307177109949378393)
                    ·
                      refine ⟨2828014730382832462033795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770686307177109949378393 2828014730382832462033795)
                      ·
                        rfl

theorem cell23_5507539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8, 2].length) (baseStart_5507539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507539 prefixEnd_5507539 := by exact prefixLift 5507539
  have htrace : WordTrace (prefixWord ++ tailWord_5507539) baseStart_5507539 baseEnd_5507539 := by
    simpa [prefixWord, tailWord_5507539, baseEnd_5507539] using wordTrace_append hprefix tailTrace_5507539
  have hstable : (prefixWord ++ tailWord_5507539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507539).length < 2 ^ (prefixWord ++ tailWord_5507539).sum := by decide
  have hdescent : baseEnd_5507539 < baseStart_5507539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507549 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5507549 : Nat := 118140960795 + 5507549 * 2 ^ 59
def prefixEnd_5507549 : Nat := 4983230072969 + 3 ^ 40 * 5507549 * 2
def baseEnd_5507549 : Nat := 942673288396459140969583

theorem tailTrace_5507549 : CollatzResearch.WordTrace tailWord_5507549 prefixEnd_5507549 942673288396459140969583 := by
  unfold tailWord_5507549
  simp only [CollatzResearch.WordTrace]
  refine ⟨200876814724098062328165701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133917876482732041552110467 200876814724098062328165701)
  ·
    refine ⟨37664402760768386686531069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200876814724098062328165701 37664402760768386686531069)
    ·
      refine ⟨14124151035288145007449151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37664402760768386686531069 14124151035288145007449151)
      ·
        refine ⟨21186226552932217511173727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14124151035288145007449151 21186226552932217511173727)
        ·
          refine ⟨31779339829398326266760591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21186226552932217511173727 31779339829398326266760591)
          ·
            refine ⟨47669009744097489400140887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31779339829398326266760591 47669009744097489400140887)
            ·
              refine ⟨71503514616146234100211331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47669009744097489400140887 71503514616146234100211331)
              ·
                refine ⟨107255271924219351150316997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71503514616146234100211331 107255271924219351150316997)
                ·
                  refine ⟨20110363485791128340684437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107255271924219351150316997 20110363485791128340684437)
                  ·
                    refine ⟨942673288396459140969583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20110363485791128340684437 942673288396459140969583)
                    ·
                      rfl

theorem cell23_5507549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5507549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507549 prefixEnd_5507549 := by exact prefixLift 5507549
  have htrace : WordTrace (prefixWord ++ tailWord_5507549) baseStart_5507549 baseEnd_5507549 := by
    simpa [prefixWord, tailWord_5507549, baseEnd_5507549] using wordTrace_append hprefix tailTrace_5507549
  have hstable : (prefixWord ++ tailWord_5507549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507549).length < 2 ^ (prefixWord ++ tailWord_5507549).sum := by decide
  have hdescent : baseEnd_5507549 < baseStart_5507549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507569 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_5507569 : Nat := 118140960795 + 5507569 * 2 ^ 59
def prefixEnd_5507569 : Nat := 4983230072969 + 3 ^ 40 * 5507569 * 2
def baseEnd_5507569 : Nat := 2828030134802467344658657

theorem tailTrace_5507569 : CollatzResearch.WordTrace tailWord_5507569 prefixEnd_5507569 2828030134802467344658657 := by
  unfold tailWord_5507569
  simp only [CollatzResearch.WordTrace]
  refine ⟨200877544184025605743893761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133918362789350403829262507 200877544184025605743893761)
  ·
    refine ⟨150658158138019204307920321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200877544184025605743893761 150658158138019204307920321)
    ·
      refine ⟨112993618603514403230940241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150658158138019204307920321 112993618603514403230940241)
      ·
        refine ⟨84745213952635802423205181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112993618603514403230940241 84745213952635802423205181)
        ·
          refine ⟨31779455232238425908701943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84745213952635802423205181 31779455232238425908701943)
          ·
            refine ⟨47669182848357638863052915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31779455232238425908701943 47669182848357638863052915)
            ·
              refine ⟨71503774272536458294579373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47669182848357638863052915 71503774272536458294579373)
              ·
                refine ⟨26813915352201171860467265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71503774272536458294579373 26813915352201171860467265)
                ·
                  refine ⟨20110436514150878895350449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26813915352201171860467265 20110436514150878895350449)
                  ·
                    refine ⟨15082827385613159171512837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20110436514150878895350449 15082827385613159171512837)
                    ·
                      refine ⟨2828030134802467344658657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15082827385613159171512837 2828030134802467344658657)
                      ·
                        rfl

theorem cell23_5507569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_5507569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507569 prefixEnd_5507569 := by exact prefixLift 5507569
  have htrace : WordTrace (prefixWord ++ tailWord_5507569) baseStart_5507569 baseEnd_5507569 := by
    simpa [prefixWord, tailWord_5507569, baseEnd_5507569] using wordTrace_append hprefix tailTrace_5507569
  have hstable : (prefixWord ++ tailWord_5507569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507569).length < 2 ^ (prefixWord ++ tailWord_5507569).sum := by decide
  have hdescent : baseEnd_5507569 < baseStart_5507569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507589 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_5507589 : Nat := 118140960795 + 5507589 * 2 ^ 59
def prefixEnd_5507589 : Nat := 4983230072969 + 3 ^ 40 * 5507589 * 2
def baseEnd_5507589 : Nat := 2828040404415557266408565

theorem tailTrace_5507589 : CollatzResearch.WordTrace tailWord_5507589 prefixEnd_5507589 2828040404415557266408565 := by
  unfold tailWord_5507589
  simp only [CollatzResearch.WordTrace]
  refine ⟨200878273643953149159621821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133918849095968766106414547 200878273643953149159621821)
  ·
    refine ⟨75329352616482430934858183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200878273643953149159621821 75329352616482430934858183)
    ·
      refine ⟨112994028924723646402287275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75329352616482430934858183 112994028924723646402287275)
      ·
        refine ⟨169491043387085469603430913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112994028924723646402287275 169491043387085469603430913)
        ·
          refine ⟨127118282540314102202573185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169491043387085469603430913 127118282540314102202573185)
          ·
            refine ⟨95338711905235576651929889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127118282540314102202573185 95338711905235576651929889)
            ·
              refine ⟨71504033928926682488947417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95338711905235576651929889 71504033928926682488947417)
              ·
                refine ⟨53628025446695011866710563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71504033928926682488947417 53628025446695011866710563)
                ·
                  refine ⟨80442038170042517800065845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53628025446695011866710563 80442038170042517800065845)
                  ·
                    refine ⟨7541441078441486043756173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80442038170042517800065845 7541441078441486043756173)
                    ·
                      refine ⟨2828040404415557266408565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7541441078441486043756173 2828040404415557266408565)
                      ·
                        rfl

theorem cell23_5507589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_5507589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507589 prefixEnd_5507589 := by exact prefixLift 5507589
  have htrace : WordTrace (prefixWord ++ tailWord_5507589) baseStart_5507589 baseEnd_5507589 := by
    simpa [prefixWord, tailWord_5507589, baseEnd_5507589] using wordTrace_append hprefix tailTrace_5507589
  have hstable : (prefixWord ++ tailWord_5507589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507589).length < 2 ^ (prefixWord ++ tailWord_5507589).sum := by decide
  have hdescent : baseEnd_5507589 < baseStart_5507589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507609 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_5507609 : Nat := 118140960795 + 5507609 * 2 ^ 59
def prefixEnd_5507609 : Nat := 4983230072969 + 3 ^ 40 * 5507609 * 2
def baseEnd_5507609 : Nat := 942683558009549062719491

theorem tailTrace_5507609 : CollatzResearch.WordTrace tailWord_5507609 prefixEnd_5507609 942683558009549062719491 := by
  unfold tailWord_5507609
  simp only [CollatzResearch.WordTrace]
  refine ⟨200879003103880692575349881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133919335402587128383566587 200879003103880692575349881)
  ·
    refine ⟨150659252327910519431512411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200879003103880692575349881 150659252327910519431512411)
    ·
      refine ⟨225988878491865779147268617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150659252327910519431512411 225988878491865779147268617)
      ·
        refine ⟨169491658868899334360451463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225988878491865779147268617 169491658868899334360451463)
        ·
          refine ⟨254237488303349001540677195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169491658868899334360451463 254237488303349001540677195)
          ·
            refine ⟨381356232455023502311015793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254237488303349001540677195 381356232455023502311015793)
            ·
              refine ⟨286017174341267626733261845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381356232455023502311015793 286017174341267626733261845)
              ·
                refine ⟨13407055047246920003121649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 286017174341267626733261845 13407055047246920003121649)
                ·
                  refine ⟨10055291285435190002341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13407055047246920003121649 10055291285435190002341237)
                  ·
                    refine ⟨942683558009549062719491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10055291285435190002341237 942683558009549062719491)
                    ·
                      rfl

theorem cell23_5507609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_5507609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507609 prefixEnd_5507609 := by exact prefixLift 5507609
  have htrace : WordTrace (prefixWord ++ tailWord_5507609) baseStart_5507609 baseEnd_5507609 := by
    simpa [prefixWord, tailWord_5507609, baseEnd_5507609] using wordTrace_append hprefix tailTrace_5507609
  have hstable : (prefixWord ++ tailWord_5507609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507609).length < 2 ^ (prefixWord ++ tailWord_5507609).sum := by decide
  have hdescent : baseEnd_5507609 < baseStart_5507609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507619 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_5507619 : Nat := 118140960795 + 5507619 * 2 ^ 59
def prefixEnd_5507619 : Nat := 4983230072969 + 3 ^ 40 * 5507619 * 2
def baseEnd_5507619 : Nat := 2828055808835192149033427

theorem tailTrace_5507619 : CollatzResearch.WordTrace tailWord_5507619 prefixEnd_5507619 2828055808835192149033427 := by
  unfold tailWord_5507619
  simp only [CollatzResearch.WordTrace]
  refine ⟨200879367833844464283213911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133919578555896309522142607 200879367833844464283213911)
  ·
    refine ⟨301319051750766696424820867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200879367833844464283213911 301319051750766696424820867)
    ·
      refine ⟨451978577626150044637231301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301319051750766696424820867 451978577626150044637231301)
      ·
        refine ⟨84745983304903133369480869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 451978577626150044637231301 84745983304903133369480869)
        ·
          refine ⟨15889871869669337506777663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84745983304903133369480869 15889871869669337506777663)
          ·
            refine ⟨23834807804504006260166495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15889871869669337506777663 23834807804504006260166495)
            ·
              refine ⟨35752211706756009390249743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23834807804504006260166495 35752211706756009390249743)
              ·
                refine ⟨53628317560134014085374615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35752211706756009390249743 53628317560134014085374615)
                ·
                  refine ⟨80442476340201021128061923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53628317560134014085374615 80442476340201021128061923)
                  ·
                    refine ⟨120663714510301531692092885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80442476340201021128061923 120663714510301531692092885)
                    ·
                      refine ⟨2828055808835192149033427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120663714510301531692092885 2828055808835192149033427)
                      ·
                        rfl

theorem cell23_5507619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_5507619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507619 prefixEnd_5507619 := by exact prefixLift 5507619
  have htrace : WordTrace (prefixWord ++ tailWord_5507619) baseStart_5507619 baseEnd_5507619 := by
    simpa [prefixWord, tailWord_5507619, baseEnd_5507619] using wordTrace_append hprefix tailTrace_5507619
  have hstable : (prefixWord ++ tailWord_5507619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507619).length < 2 ^ (prefixWord ++ tailWord_5507619).sum := by decide
  have hdescent : baseEnd_5507619 < baseStart_5507619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507624 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5507624 : Nat := 118140960795 + 5507624 * 2 ^ 59
def prefixEnd_5507624 : Nat := 4983230072969 + 3 ^ 40 * 5507624 * 2
def baseEnd_5507624 : Nat := 2828058376238464629470905

theorem tailTrace_5507624 : CollatzResearch.WordTrace tailWord_5507624 prefixEnd_5507624 2828058376238464629470905 := by
  unfold tailWord_5507624
  simp only [CollatzResearch.WordTrace]
  refine ⟨100439775099413175068572963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133919700132550900091430617 100439775099413175068572963)
  ·
    refine ⟨150659662649119762602859445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100439775099413175068572963 150659662649119762602859445)
    ·
      refine ⟨14124343373354977744018073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150659662649119762602859445 14124343373354977744018073)
      ·
        refine ⟨10593257530016233308013555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14124343373354977744018073 10593257530016233308013555)
        ·
          refine ⟨15889886295024349962020333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10593257530016233308013555 15889886295024349962020333)
          ·
            refine ⟨5958707360634131235757625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15889886295024349962020333 5958707360634131235757625)
            ·
              refine ⟨4469030520475598426818219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5958707360634131235757625 4469030520475598426818219)
              ·
                refine ⟨6703545780713397640227329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4469030520475598426818219 6703545780713397640227329)
                ·
                  refine ⟨5027659335535048230170497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6703545780713397640227329 5027659335535048230170497)
                  ·
                    refine ⟨3770744501651286172627873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027659335535048230170497 3770744501651286172627873)
                    ·
                      refine ⟨2828058376238464629470905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770744501651286172627873 2828058376238464629470905)
                      ·
                        rfl

theorem cell23_5507624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5507624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507624 prefixEnd_5507624 := by exact prefixLift 5507624
  have htrace : WordTrace (prefixWord ++ tailWord_5507624) baseStart_5507624 baseEnd_5507624 := by
    simpa [prefixWord, tailWord_5507624, baseEnd_5507624] using wordTrace_append hprefix tailTrace_5507624
  have hstable : (prefixWord ++ tailWord_5507624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507624).length < 2 ^ (prefixWord ++ tailWord_5507624).sum := by decide
  have hdescent : baseEnd_5507624 < baseStart_5507624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507669 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 8]
def baseStart_5507669 : Nat := 118140960795 + 5507669 * 2 ^ 59
def prefixEnd_5507669 : Nat := 4983230072969 + 3 ^ 40 * 5507669 * 2
def baseEnd_5507669 : Nat := 314231275874212994823133

theorem tailTrace_5507669 : CollatzResearch.WordTrace tailWord_5507669 prefixEnd_5507669 314231275874212994823133 := by
  unfold tailWord_5507669
  simp only [CollatzResearch.WordTrace]
  refine ⟨200881191483663322822534061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133920794322442215215022707 200881191483663322822534061)
  ·
    refine ⟨75330446806373746058450273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200881191483663322822534061 75330446806373746058450273)
    ·
      refine ⟨56497835104780309543837705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75330446806373746058450273 56497835104780309543837705)
      ·
        refine ⟨42373376328585232157878279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56497835104780309543837705 42373376328585232157878279)
        ·
          refine ⟨63560064492877848236817419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42373376328585232157878279 63560064492877848236817419)
          ·
            refine ⟨95340096739316772355226129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63560064492877848236817419 95340096739316772355226129)
            ·
              refine ⟨71505072554487579266419597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95340096739316772355226129 71505072554487579266419597)
              ·
                refine ⟨26814402207932842224907349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71505072554487579266419597 26814402207932842224907349)
                ·
                  refine ⟨314231275874212994823133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26814402207932842224907349 314231275874212994823133)
                  ·
                    rfl

theorem cell23_5507669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_5507669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507669 prefixEnd_5507669 := by exact prefixLift 5507669
  have htrace : WordTrace (prefixWord ++ tailWord_5507669) baseStart_5507669 baseEnd_5507669 := by
    simpa [prefixWord, tailWord_5507669, baseEnd_5507669] using wordTrace_append hprefix tailTrace_5507669
  have hstable : (prefixWord ++ tailWord_5507669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507669).length < 2 ^ (prefixWord ++ tailWord_5507669).sum := by decide
  have hdescent : baseEnd_5507669 < baseStart_5507669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507713 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_5507713 : Nat := 118140960795 + 5507713 * 2 ^ 59
def prefixEnd_5507713 : Nat := 4983230072969 + 3 ^ 40 * 5507713 * 2
def baseEnd_5507713 : Nat := 2828104076016714781257995

theorem tailTrace_5507713 : CollatzResearch.WordTrace tailWord_5507713 prefixEnd_5507713 2828104076016714781257995 := by
  unfold tailWord_5507713
  simp only [CollatzResearch.WordTrace]
  refine ⟨200882796295503918337135793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133921864197002612224757195 200882796295503918337135793)
  ·
    refine ⟨150662097221627938752851845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200882796295503918337135793 150662097221627938752851845)
    ·
      refine ⟨28249143229055238516159721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150662097221627938752851845 28249143229055238516159721)
      ·
        refine ⟨21186857421791428887119791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28249143229055238516159721 21186857421791428887119791)
        ·
          refine ⟨31780286132687143330679687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21186857421791428887119791 31780286132687143330679687)
          ·
            refine ⟨47670429199030714996019531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31780286132687143330679687 47670429199030714996019531)
            ·
              refine ⟨71505643798546072494029297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47670429199030714996019531 71505643798546072494029297)
              ·
                refine ⟨53629232848909554370521973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71505643798546072494029297 53629232848909554370521973)
                ·
                  refine ⟨5027740579585270722236435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53629232848909554370521973 5027740579585270722236435)
                  ·
                    refine ⟨7541610869377906083354653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5027740579585270722236435 7541610869377906083354653)
                    ·
                      refine ⟨2828104076016714781257995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7541610869377906083354653 2828104076016714781257995)
                      ·
                        rfl

theorem cell23_5507713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_5507713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507713 prefixEnd_5507713 := by exact prefixLift 5507713
  have htrace : WordTrace (prefixWord ++ tailWord_5507713) baseStart_5507713 baseEnd_5507713 := by
    simpa [prefixWord, tailWord_5507713, baseEnd_5507713] using wordTrace_append hprefix tailTrace_5507713
  have hstable : (prefixWord ++ tailWord_5507713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507713).length < 2 ^ (prefixWord ++ tailWord_5507713).sum := by decide
  have hdescent : baseEnd_5507713 < baseStart_5507713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507730 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_5507730 : Nat := 118140960795 + 5507730 * 2 ^ 59
def prefixEnd_5507730 : Nat := 4983230072969 + 3 ^ 40 * 5507730 * 2
def baseEnd_5507730 : Nat := 2828112805187841214745417

theorem tailTrace_5507730 : CollatzResearch.WordTrace tailWord_5507730 prefixEnd_5507730 2828112805187841214745417 := by
  unfold tailWord_5507730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50220854084110582560126161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133922277557628220160336429 50220854084110582560126161)
  ·
    refine ⟨37665640563082936920094621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50220854084110582560126161 37665640563082936920094621)
    ·
      refine ⟨14124615211156101345035483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37665640563082936920094621 14124615211156101345035483)
      ·
        refine ⟨21186922816734152017553225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14124615211156101345035483 21186922816734152017553225)
        ·
          refine ⟨15890192112550614013164919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21186922816734152017553225 15890192112550614013164919)
          ·
            refine ⟨23835288168825921019747379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15890192112550614013164919 23835288168825921019747379)
            ·
              refine ⟨35752932253238881529621069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23835288168825921019747379 35752932253238881529621069)
              ·
                refine ⟨13407349594964580573607901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35752932253238881529621069 13407349594964580573607901)
                ·
                  refine ⟨5027756098111717715102963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13407349594964580573607901 5027756098111717715102963)
                  ·
                    refine ⟨7541634147167576572654445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5027756098111717715102963 7541634147167576572654445)
                    ·
                      refine ⟨2828112805187841214745417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7541634147167576572654445 2828112805187841214745417)
                      ·
                        rfl

theorem cell23_5507730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_5507730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507730 prefixEnd_5507730 := by exact prefixLift 5507730
  have htrace : WordTrace (prefixWord ++ tailWord_5507730) baseStart_5507730 baseEnd_5507730 := by
    simpa [prefixWord, tailWord_5507730, baseEnd_5507730] using wordTrace_append hprefix tailTrace_5507730
  have hstable : (prefixWord ++ tailWord_5507730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507730).length < 2 ^ (prefixWord ++ tailWord_5507730).sum := by decide
  have hdescent : baseEnd_5507730 < baseStart_5507730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507773 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_5507773 : Nat := 118140960795 + 5507773 * 2 ^ 59
def prefixEnd_5507773 : Nat := 4983230072969 + 3 ^ 40 * 5507773 * 2
def baseEnd_5507773 : Nat := 2828134884855984546507719

theorem tailTrace_5507773 : CollatzResearch.WordTrace tailWord_5507773 prefixEnd_5507773 2828134884855984546507719 := by
  unfold tailWord_5507773
  simp only [CollatzResearch.WordTrace]
  refine ⟨200884984675286548584319973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133923323116857699056213315 200884984675286548584319973)
  ·
    refine ⟨37665934626616227859559995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200884984675286548584319973 37665934626616227859559995)
    ·
      refine ⟨56498901939924341789339993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37665934626616227859559995 56498901939924341789339993)
      ·
        refine ⟨42374176454943256342004995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56498901939924341789339993 42374176454943256342004995)
        ·
          refine ⟨63561264682414884513007493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42374176454943256342004995 63561264682414884513007493)
          ·
            refine ⟨11917737127952790846188905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63561264682414884513007493 11917737127952790846188905)
            ·
              refine ⟨8938302845964593134641679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11917737127952790846188905 8938302845964593134641679)
              ·
                refine ⟨13407454268946889701962519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8938302845964593134641679 13407454268946889701962519)
                ·
                  refine ⟨20111181403420334552943779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13407454268946889701962519 20111181403420334552943779)
                  ·
                    refine ⟨30166772105130501829415669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20111181403420334552943779 30166772105130501829415669)
                    ·
                      refine ⟨2828134884855984546507719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30166772105130501829415669 2828134884855984546507719)
                      ·
                        rfl

theorem cell23_5507773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_5507773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507773 prefixEnd_5507773 := by exact prefixLift 5507773
  have htrace : WordTrace (prefixWord ++ tailWord_5507773) baseStart_5507773 baseEnd_5507773 := by
    simpa [prefixWord, tailWord_5507773, baseEnd_5507773] using wordTrace_append hprefix tailTrace_5507773
  have hstable : (prefixWord ++ tailWord_5507773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507773).length < 2 ^ (prefixWord ++ tailWord_5507773).sum := by decide
  have hdescent : baseEnd_5507773 < baseStart_5507773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507776 : List Nat := [2, 1, 1, 2, 4, 4, 9]
def baseStart_5507776 : Nat := 118140960795 + 5507776 * 2 ^ 59
def prefixEnd_5507776 : Nat := 4983230072969 + 3 ^ 40 * 5507776 * 2
def baseEnd_5507776 : Nat := 34915264509851210305805

theorem tailTrace_5507776 : CollatzResearch.WordTrace tailWord_5507776 prefixEnd_5507776 34915264509851210305805 := by
  unfold tailWord_5507776
  simp only [CollatzResearch.WordTrace]
  refine ⟨100442547047137840048339591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133923396062850453397786121 100442547047137840048339591)
  ·
    refine ⟨150663820570706760072509387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100442547047137840048339591 150663820570706760072509387)
    ·
      refine ⟨225995730856060140108764081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150663820570706760072509387 225995730856060140108764081)
      ·
        refine ⟨169496798142045105081573061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225995730856060140108764081 169496798142045105081573061)
        ·
          refine ⟨31780649651633457202794949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169496798142045105081573061 31780649651633457202794949)
          ·
            refine ⟨5958871809681273225524053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31780649651633457202794949 5958871809681273225524053)
            ·
              refine ⟨34915264509851210305805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5958871809681273225524053 34915264509851210305805)
              ·
                rfl

theorem cell23_5507776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 9].length) (baseStart_5507776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507776 prefixEnd_5507776 := by exact prefixLift 5507776
  have htrace : WordTrace (prefixWord ++ tailWord_5507776) baseStart_5507776 baseEnd_5507776 := by
    simpa [prefixWord, tailWord_5507776, baseEnd_5507776] using wordTrace_append hprefix tailTrace_5507776
  have hstable : (prefixWord ++ tailWord_5507776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507776).length < 2 ^ (prefixWord ++ tailWord_5507776).sum := by decide
  have hdescent : baseEnd_5507776 < baseStart_5507776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507797 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_5507797 : Nat := 118140960795 + 5507797 * 2 ^ 59
def prefixEnd_5507797 : Nat := 4983230072969 + 3 ^ 40 * 5507797 * 2
def baseEnd_5507797 : Nat := 942715736130564150869203

theorem tailTrace_5507797 : CollatzResearch.WordTrace tailWord_5507797 prefixEnd_5507797 942715736130564150869203 := by
  unfold tailWord_5507797
  simp only [CollatzResearch.WordTrace]
  refine ⟨200885860027199600683193645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133923906684799733788795763 200885860027199600683193645)
  ·
    refine ⟨75332197510199850256197617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200885860027199600683193645 75332197510199850256197617)
    ·
      refine ⟨56499148132649887692148213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75332197510199850256197617 56499148132649887692148213)
      ·
        refine ⟨5296795137435926971138895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56499148132649887692148213 5296795137435926971138895)
        ·
          refine ⟨7945192706153890456708343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5296795137435926971138895 7945192706153890456708343)
          ·
            refine ⟨11917789059230835685062515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945192706153890456708343 11917789059230835685062515)
            ·
              refine ⟨17876683588846253527593773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11917789059230835685062515 17876683588846253527593773)
              ·
                refine ⟨6703756345817345072847665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17876683588846253527593773 6703756345817345072847665)
                ·
                  refine ⟨5027817259363008804635749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6703756345817345072847665 5027817259363008804635749)
                  ·
                    refine ⟨942715736130564150869203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5027817259363008804635749 942715736130564150869203)
                    ·
                      rfl

theorem cell23_5507797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_5507797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507797 prefixEnd_5507797 := by exact prefixLift 5507797
  have htrace : WordTrace (prefixWord ++ tailWord_5507797) baseStart_5507797 baseEnd_5507797 := by
    simpa [prefixWord, tailWord_5507797, baseEnd_5507797] using wordTrace_append hprefix tailTrace_5507797
  have hstable : (prefixWord ++ tailWord_5507797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507797).length < 2 ^ (prefixWord ++ tailWord_5507797).sum := by decide
  have hdescent : baseEnd_5507797 < baseStart_5507797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507838 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5507838 : Nat := 118140960795 + 5507838 * 2 ^ 59
def prefixEnd_5507838 : Nat := 4983230072969 + 3 ^ 40 * 5507838 * 2
def baseEnd_5507838 : Nat := 2828168261098526792194921

theorem tailTrace_5507838 : CollatzResearch.WordTrace tailWord_5507838 prefixEnd_5507838 2828168261098526792194921 := by
  unfold tailWord_5507838
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110919427506383085679521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133924903613367376456957445 25110919427506383085679521)
  ·
    refine ⟨18833189570629787314259641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25110919427506383085679521 18833189570629787314259641)
    ·
      refine ⟨14124892177972340485694731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18833189570629787314259641 14124892177972340485694731)
      ·
        refine ⟨21187338266958510728542097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14124892177972340485694731 21187338266958510728542097)
        ·
          refine ⟨15890503700218883046406573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21187338266958510728542097 15890503700218883046406573)
          ·
            refine ⟨5958938887582081142402465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15890503700218883046406573 5958938887582081142402465)
            ·
              refine ⟨4469204165686560856801849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5958938887582081142402465 4469204165686560856801849)
              ·
                refine ⟨3351903124264920642601387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469204165686560856801849 3351903124264920642601387)
                ·
                  refine ⟨5027854686397380963902081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351903124264920642601387 5027854686397380963902081)
                  ·
                    refine ⟨3770891014798035722926561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5027854686397380963902081 3770891014798035722926561)
                    ·
                      refine ⟨2828168261098526792194921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770891014798035722926561 2828168261098526792194921)
                      ·
                        rfl

theorem cell23_5507838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5507838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507838 prefixEnd_5507838 := by exact prefixLift 5507838
  have htrace : WordTrace (prefixWord ++ tailWord_5507838) baseStart_5507838 baseEnd_5507838 := by
    simpa [prefixWord, tailWord_5507838, baseEnd_5507838] using wordTrace_append hprefix tailTrace_5507838
  have hstable : (prefixWord ++ tailWord_5507838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507838).length < 2 ^ (prefixWord ++ tailWord_5507838).sum := by decide
  have hdescent : baseEnd_5507838 < baseStart_5507838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 5, 4, 2]
def baseStart_5507843 : Nat := 118140960795 + 5507843 * 2 ^ 59
def prefixEnd_5507843 : Nat := 4983230072969 + 3 ^ 40 * 5507843 * 2
def baseEnd_5507843 : Nat := 2828170828501799272632397

theorem tailTrace_5507843 : CollatzResearch.WordTrace tailWord_5507843 prefixEnd_5507843 2828170828501799272632397 := by
  unfold tailWord_5507843
  simp only [CollatzResearch.WordTrace]
  refine ⟨200887537785032950539368183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133925025190021967026245455 200887537785032950539368183)
  ·
    refine ⟨301331306677549425809052275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200887537785032950539368183 301331306677549425809052275)
    ·
      refine ⟨451996960016324138713578413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301331306677549425809052275 451996960016324138713578413)
      ·
        refine ⟨169498860006121552017591905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451996960016324138713578413 169498860006121552017591905)
        ·
          refine ⟨127124145004591164013193929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169498860006121552017591905 127124145004591164013193929)
          ·
            refine ⟨95343108753443373009895447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127124145004591164013193929 95343108753443373009895447)
            ·
              refine ⟨143014663130165059514843171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95343108753443373009895447 143014663130165059514843171)
              ·
                refine ⟨214521994695247589272264757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143014663130165059514843171 214521994695247589272264757)
                ·
                  refine ⟨20111437002679461494274821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214521994695247589272264757 20111437002679461494274821)
                  ·
                    refine ⟨3770894438002399030176529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20111437002679461494274821 3770894438002399030176529)
                    ·
                      refine ⟨2828170828501799272632397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3770894438002399030176529 2828170828501799272632397)
                      ·
                        rfl

theorem cell23_5507843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_5507843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507843 prefixEnd_5507843 := by exact prefixLift 5507843
  have htrace : WordTrace (prefixWord ++ tailWord_5507843) baseStart_5507843 baseEnd_5507843 := by
    simpa [prefixWord, tailWord_5507843, baseEnd_5507843] using wordTrace_append hprefix tailTrace_5507843
  have hstable : (prefixWord ++ tailWord_5507843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507843).length < 2 ^ (prefixWord ++ tailWord_5507843).sum := by decide
  have hdescent : baseEnd_5507843 < baseStart_5507843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5507883 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 5]
def baseStart_5507883 : Nat := 118140960795 + 5507883 * 2 ^ 59
def prefixEnd_5507883 : Nat := 4983230072969 + 3 ^ 40 * 5507883 * 2
def baseEnd_5507883 : Nat := 314243485303108790681357

theorem tailTrace_5507883 : CollatzResearch.WordTrace tailWord_5507883 prefixEnd_5507883 314243485303108790681357 := by
  unfold tailWord_5507883
  simp only [CollatzResearch.WordTrace]
  refine ⟨200888996704888037370824303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133925997803258691580549535 200888996704888037370824303)
  ·
    refine ⟨301333495057332056056236455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200888996704888037370824303 301333495057332056056236455)
    ·
      refine ⟨452000242585998084084354683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301333495057332056056236455 452000242585998084084354683)
      ·
        refine ⟨678000363878997126126532025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452000242585998084084354683 678000363878997126126532025)
        ·
          refine ⟨508500272909247844594899019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678000363878997126126532025 508500272909247844594899019)
          ·
            refine ⟨762750409363871766892348529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508500272909247844594899019 762750409363871766892348529)
            ·
              refine ⟨572062807022903825169261397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762750409363871766892348529 572062807022903825169261397)
              ·
                refine ⟨3351930509899827100601141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 572062807022903825169261397 3351930509899827100601141)
                ·
                  refine ⟨314243485303108790681357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3351930509899827100601141 314243485303108790681357)
                  ·
                    rfl

theorem cell23_5507883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 5].length) (baseStart_5507883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5507883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5507883 prefixEnd_5507883 := by exact prefixLift 5507883
  have htrace : WordTrace (prefixWord ++ tailWord_5507883) baseStart_5507883 baseEnd_5507883 := by
    simpa [prefixWord, tailWord_5507883, baseEnd_5507883] using wordTrace_append hprefix tailTrace_5507883
  have hstable : (prefixWord ++ tailWord_5507883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5507883).length < 2 ^ (prefixWord ++ tailWord_5507883).sum := by decide
  have hdescent : baseEnd_5507883 < baseStart_5507883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5507883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508007 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 6]
def baseStart_5508007 : Nat := 118140960795 + 5508007 * 2 ^ 59
def prefixEnd_5508007 : Nat := 4983230072969 + 3 ^ 40 * 5508007 * 2
def baseEnd_5508007 : Nat := 314250559925459625664627

theorem tailTrace_5508007 : CollatzResearch.WordTrace tailWord_5508007 prefixEnd_5508007 314250559925459625664627 := by
  unfold tailWord_5508007
  simp only [CollatzResearch.WordTrace]
  refine ⟨200893519356438806548338275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133929012904292537698892183 200893519356438806548338275)
  ·
    refine ⟨301340279034658209822507413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200893519356438806548338275 301340279034658209822507413)
    ·
      refine ⟨14125325579749603585430035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 301340279034658209822507413 14125325579749603585430035)
      ·
        refine ⟨21187988369624405378145053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125325579749603585430035 21187988369624405378145053)
        ·
          refine ⟨7945495638609152016804395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21187988369624405378145053 7945495638609152016804395)
          ·
            refine ⟨11918243457913728025206593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945495638609152016804395 11918243457913728025206593)
            ·
              refine ⟨8938682593435296018904945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11918243457913728025206593 8938682593435296018904945)
              ·
                refine ⟨6704011945076472014178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8938682593435296018904945 6704011945076472014178709)
                ·
                  refine ⟨314250559925459625664627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6704011945076472014178709 314250559925459625664627)
                  ·
                    rfl

theorem cell23_5508007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 6].length) (baseStart_5508007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508007 prefixEnd_5508007 := by exact prefixLift 5508007
  have htrace : WordTrace (prefixWord ++ tailWord_5508007) baseStart_5508007 baseEnd_5508007 := by
    simpa [prefixWord, tailWord_5508007, baseEnd_5508007] using wordTrace_append hprefix tailTrace_5508007
  have hstable : (prefixWord ++ tailWord_5508007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508007).length < 2 ^ (prefixWord ++ tailWord_5508007).sum := by decide
  have hdescent : baseEnd_5508007 < baseStart_5508007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508038 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5508038 : Nat := 118140960795 + 5508038 * 2 ^ 59
def prefixEnd_5508038 : Nat := 4983230072969 + 3 ^ 40 * 5508038 * 2
def baseEnd_5508038 : Nat := 2828270957229426009694001

theorem tailTrace_5508038 : CollatzResearch.WordTrace tailWord_5508038 prefixEnd_5508038 2828270957229426009694001 := by
  unfold tailWord_5508038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277957813103953088834899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133929766679550999228477845 6277957813103953088834899)
  ·
    refine ⟨9416936719655929633252349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6277957813103953088834899 9416936719655929633252349)
    ·
      refine ⟨3531351269870973612469631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9416936719655929633252349 3531351269870973612469631)
      ·
        refine ⟨5297026904806460418704447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531351269870973612469631 5297026904806460418704447)
        ·
          refine ⟨7945540357209690628056671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297026904806460418704447 7945540357209690628056671)
          ·
            refine ⟨11918310535814535942085007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945540357209690628056671 11918310535814535942085007)
            ·
              refine ⟨17877465803721803913127511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11918310535814535942085007 17877465803721803913127511)
              ·
                refine ⟨26816198705582705869691267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17877465803721803913127511 26816198705582705869691267)
                ·
                  refine ⟨40224298058374058804536901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26816198705582705869691267 40224298058374058804536901)
                  ·
                    refine ⟨7542055885945136025850669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40224298058374058804536901 7542055885945136025850669)
                    ·
                      refine ⟨2828270957229426009694001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542055885945136025850669 2828270957229426009694001)
                      ·
                        rfl

theorem cell23_5508038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5508038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508038 prefixEnd_5508038 := by exact prefixLift 5508038
  have htrace : WordTrace (prefixWord ++ tailWord_5508038) baseStart_5508038 baseEnd_5508038 := by
    simpa [prefixWord, tailWord_5508038, baseEnd_5508038] using wordTrace_append hprefix tailTrace_5508038
  have hstable : (prefixWord ++ tailWord_5508038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508038).length < 2 ^ (prefixWord ++ tailWord_5508038).sum := by decide
  have hdescent : baseEnd_5508038 < baseStart_5508038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508045 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5508045 : Nat := 118140960795 + 5508045 * 2 ^ 59
def prefixEnd_5508045 : Nat := 4983230072969 + 3 ^ 40 * 5508045 * 2
def baseEnd_5508045 : Nat := 942758183864669160768823

theorem tailTrace_5508045 : CollatzResearch.WordTrace tailWord_5508045 prefixEnd_5508045 942758183864669160768823 := by
  unfold tailWord_5508045
  simp only [CollatzResearch.WordTrace]
  refine ⟨200894905330301139038221589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133929936886867426025481059 200894905330301139038221589)
  ·
    refine ⟨9416948687357865892416637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200894905330301139038221589 9416948687357865892416637)
    ·
      refine ⟨3531355757759199709656239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9416948687357865892416637 3531355757759199709656239)
      ·
        refine ⟨5297033636638799564484359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531355757759199709656239 5297033636638799564484359)
        ·
          refine ⟨7945550454958199346726539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297033636638799564484359 7945550454958199346726539)
          ·
            refine ⟨11918325682437299020089809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945550454958199346726539 11918325682437299020089809)
            ·
              refine ⟨8938744261827974265067357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11918325682437299020089809 8938744261827974265067357)
              ·
                refine ⟨3352029098185490349400259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8938744261827974265067357 3352029098185490349400259)
                ·
                  refine ⟨5028043647278235524100389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352029098185490349400259 5028043647278235524100389)
                  ·
                    refine ⟨942758183864669160768823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028043647278235524100389 942758183864669160768823)
                    ·
                      rfl

theorem cell23_5508045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5508045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508045 prefixEnd_5508045 := by exact prefixLift 5508045
  have htrace : WordTrace (prefixWord ++ tailWord_5508045) baseStart_5508045 baseEnd_5508045 := by
    simpa [prefixWord, tailWord_5508045, baseEnd_5508045] using wordTrace_append hprefix tailTrace_5508045
  have hstable : (prefixWord ++ tailWord_5508045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508045).length < 2 ^ (prefixWord ++ tailWord_5508045).sum := by decide
  have hdescent : baseEnd_5508045 < baseStart_5508045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508054 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_5508054 : Nat := 118140960795 + 5508054 * 2 ^ 59
def prefixEnd_5508054 : Nat := 4983230072969 + 3 ^ 40 * 5508054 * 2
def baseEnd_5508054 : Nat := 942759724306632649031309

theorem tailTrace_5508054 : CollatzResearch.WordTrace tailWord_5508054 prefixEnd_5508054 942759724306632649031309 := by
  unfold tailWord_5508054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12555952099204283348456201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133930155724845689050199477 12555952099204283348456201)
  ·
    refine ⟨9416964074403212511342151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12555952099204283348456201 9416964074403212511342151)
    ·
      refine ⟨14125446111604818767013227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9416964074403212511342151 14125446111604818767013227)
      ·
        refine ⟨21188169167407228150519841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125446111604818767013227 21188169167407228150519841)
        ·
          refine ⟨15891126875555421112889881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21188169167407228150519841 15891126875555421112889881)
          ·
            refine ⟨11918345156666565834667411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15891126875555421112889881 11918345156666565834667411)
            ·
              refine ⟨17877517734999848752001117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11918345156666565834667411 17877517734999848752001117)
              ·
                refine ⟨6704069150624943282000419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17877517734999848752001117 6704069150624943282000419)
                ·
                  refine ⟨10056103725937414923000629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704069150624943282000419 10056103725937414923000629)
                  ·
                    refine ⟨942759724306632649031309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10056103725937414923000629 942759724306632649031309)
                    ·
                      rfl

theorem cell23_5508054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_5508054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508054 prefixEnd_5508054 := by exact prefixLift 5508054
  have htrace : WordTrace (prefixWord ++ tailWord_5508054) baseStart_5508054 baseEnd_5508054 := by
    simpa [prefixWord, tailWord_5508054, baseEnd_5508054] using wordTrace_append hprefix tailTrace_5508054
  have hstable : (prefixWord ++ tailWord_5508054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508054).length < 2 ^ (prefixWord ++ tailWord_5508054).sum := by decide
  have hdescent : baseEnd_5508054 < baseStart_5508054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508057 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_5508057 : Nat := 118140960795 + 5508057 * 2 ^ 59
def prefixEnd_5508057 : Nat := 4983230072969 + 3 ^ 40 * 5508057 * 2
def baseEnd_5508057 : Nat := 2828280713361861435356413

theorem tailTrace_5508057 : CollatzResearch.WordTrace tailWord_5508057 prefixEnd_5508057 2828280713361861435356413 := by
  unfold tailWord_5508057
  simp only [CollatzResearch.WordTrace]
  refine ⟨200895343006257665087658425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133930228670838443391772283 200895343006257665087658425)
  ·
    refine ⟨150671507254693248815743819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200895343006257665087658425 150671507254693248815743819)
    ·
      refine ⟨226007260882039873223615729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150671507254693248815743819 226007260882039873223615729)
      ·
        refine ⟨169505445661529904917711797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226007260882039873223615729 169505445661529904917711797)
        ·
          refine ⟨15891135530768428586035481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169505445661529904917711797 15891135530768428586035481)
          ·
            refine ⟨11918351648076321439526611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15891135530768428586035481 11918351648076321439526611)
            ·
              refine ⟨17877527472114482159289917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11918351648076321439526611 17877527472114482159289917)
              ·
                refine ⟨6704072802042930809733719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17877527472114482159289917 6704072802042930809733719)
                ·
                  refine ⟨10056109203064396214600579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704072802042930809733719 10056109203064396214600579)
                  ·
                    refine ⟨15084163804596594321900869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10056109203064396214600579 15084163804596594321900869)
                    ·
                      refine ⟨2828280713361861435356413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15084163804596594321900869 2828280713361861435356413)
                      ·
                        rfl

theorem cell23_5508057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_5508057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508057 prefixEnd_5508057 := by exact prefixLift 5508057
  have htrace : WordTrace (prefixWord ++ tailWord_5508057) baseStart_5508057 baseEnd_5508057 := by
    simpa [prefixWord, tailWord_5508057, baseEnd_5508057] using wordTrace_append hprefix tailTrace_5508057
  have hstable : (prefixWord ++ tailWord_5508057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508057).length < 2 ^ (prefixWord ++ tailWord_5508057).sum := by decide
  have hdescent : baseEnd_5508057 < baseStart_5508057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508074 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_5508074 : Nat := 118140960795 + 5508074 * 2 ^ 59
def prefixEnd_5508074 : Nat := 4983230072969 + 3 ^ 40 * 5508074 * 2
def baseEnd_5508074 : Nat := 2828289442532987868843835

theorem tailTrace_5508074 : CollatzResearch.WordTrace tailWord_5508074 prefixEnd_5508074 2828289442532987868843835 := by
  unfold tailWord_5508074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50223990761799019247756819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133930642031464051327351517 50223990761799019247756819)
  ·
    refine ⟨75335986142698528871635229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50223990761799019247756819 75335986142698528871635229)
    ·
      refine ⟨28250994803511948326863211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75335986142698528871635229 28250994803511948326863211)
      ·
        refine ⟨42376492205267922490294817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28250994803511948326863211 42376492205267922490294817)
        ·
          refine ⟨31782369153950941867721113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42376492205267922490294817 31782369153950941867721113)
          ·
            refine ⟨23836776865463206400790835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31782369153950941867721113 23836776865463206400790835)
            ·
              refine ⟨35755165298194809601186253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23836776865463206400790835 35755165298194809601186253)
              ·
                refine ⟨13408186986823053600444845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35755165298194809601186253 13408186986823053600444845)
                ·
                  refine ⟨5028070120058645100166817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13408186986823053600444845 5028070120058645100166817)
                  ·
                    refine ⟨3771052590043983825125113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028070120058645100166817 3771052590043983825125113)
                    ·
                      refine ⟨2828289442532987868843835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771052590043983825125113 2828289442532987868843835)
                      ·
                        rfl

theorem cell23_5508074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_5508074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508074 prefixEnd_5508074 := by exact prefixLift 5508074
  have htrace : WordTrace (prefixWord ++ tailWord_5508074) baseStart_5508074 baseEnd_5508074 := by
    simpa [prefixWord, tailWord_5508074, baseEnd_5508074] using wordTrace_append hprefix tailTrace_5508074
  have hstable : (prefixWord ++ tailWord_5508074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508074).length < 2 ^ (prefixWord ++ tailWord_5508074).sum := by decide
  have hdescent : baseEnd_5508074 < baseStart_5508074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508097 : List Nat := [1, 2, 4, 1, 2, 4, 2, 7]
def baseStart_5508097 : Nat := 118140960795 + 5508097 * 2 ^ 59
def prefixEnd_5508097 : Nat := 4983230072969 + 3 ^ 40 * 5508097 * 2
def baseEnd_5508097 : Nat := 104751898244001528846527

theorem tailTrace_5508097 : CollatzResearch.WordTrace tailWord_5508097 prefixEnd_5508097 104751898244001528846527 := by
  unfold tailWord_5508097
  simp only [CollatzResearch.WordTrace]
  refine ⟨200896801926112751919114545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133931201284075167946076363 200896801926112751919114545)
  ·
    refine ⟨150672601444584563939335909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200896801926112751919114545 150672601444584563939335909)
    ·
      refine ⟨28251112770859605738625483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150672601444584563939335909 28251112770859605738625483)
      ·
        refine ⟨42376669156289408607938225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28251112770859605738625483 42376669156289408607938225)
        ·
          refine ⟨31782501867217056455953669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42376669156289408607938225 31782501867217056455953669)
          ·
            refine ⟨5959219100103198085491313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31782501867217056455953669 5959219100103198085491313)
            ·
              refine ⟨4469414325077398564118485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959219100103198085491313 4469414325077398564118485)
              ·
                refine ⟨104751898244001528846527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4469414325077398564118485 104751898244001528846527)
                ·
                  rfl

theorem cell23_5508097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 7].length) (baseStart_5508097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508097 prefixEnd_5508097 := by exact prefixLift 5508097
  have htrace : WordTrace (prefixWord ++ tailWord_5508097) baseStart_5508097 baseEnd_5508097 := by
    simpa [prefixWord, tailWord_5508097, baseEnd_5508097] using wordTrace_append hprefix tailTrace_5508097
  have hstable : (prefixWord ++ tailWord_5508097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508097).length < 2 ^ (prefixWord ++ tailWord_5508097).sum := by decide
  have hdescent : baseEnd_5508097 < baseStart_5508097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508107 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 3]
def baseStart_5508107 : Nat := 118140960795 + 5508107 * 2 ^ 59
def prefixEnd_5508107 : Nat := 4983230072969 + 3 ^ 40 * 5508107 * 2
def baseEnd_5508107 : Nat := 2828306387394586239731183

theorem tailTrace_5508107 : CollatzResearch.WordTrace tailWord_5508107 prefixEnd_5508107 2828306387394586239731183 := by
  unfold tailWord_5508107
  simp only [CollatzResearch.WordTrace]
  refine ⟨200897166656076523626978575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133931444437384349084652383 200897166656076523626978575)
  ·
    refine ⟨301345749984114785440467863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200897166656076523626978575 301345749984114785440467863)
    ·
      refine ⟨452018624976172178160701795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301345749984114785440467863 452018624976172178160701795)
      ·
        refine ⟨678027937464258267241052693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452018624976172178160701795 678027937464258267241052693)
        ·
          refine ⟨31782559568637106276924345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 678027937464258267241052693 31782559568637106276924345)
          ·
            refine ⟨23836919676477829707693259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31782559568637106276924345 23836919676477829707693259)
            ·
              refine ⟨35755379514716744561539889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23836919676477829707693259 35755379514716744561539889)
              ·
                refine ⟨26816534636037558421154917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35755379514716744561539889 26816534636037558421154917)
                ·
                  refine ⟨5028100244257042203966547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26816534636037558421154917 5028100244257042203966547)
                  ·
                    refine ⟨7542150366385563305949821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028100244257042203966547 7542150366385563305949821)
                    ·
                      refine ⟨2828306387394586239731183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542150366385563305949821 2828306387394586239731183)
                      ·
                        rfl

theorem cell23_5508107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 3].length) (baseStart_5508107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508107 prefixEnd_5508107 := by exact prefixLift 5508107
  have htrace : WordTrace (prefixWord ++ tailWord_5508107) baseStart_5508107 baseEnd_5508107 := by
    simpa [prefixWord, tailWord_5508107, baseEnd_5508107] using wordTrace_append hprefix tailTrace_5508107
  have hstable : (prefixWord ++ tailWord_5508107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508107).length < 2 ^ (prefixWord ++ tailWord_5508107).sum := by decide
  have hdescent : baseEnd_5508107 < baseStart_5508107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508108 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 1, 2, 2]
def baseStart_5508108 : Nat := 118140960795 + 5508108 * 2 ^ 59
def prefixEnd_5508108 : Nat := 4983230072969 + 3 ^ 40 * 5508108 * 2
def baseEnd_5508108 : Nat := 2828306900875240735818679

theorem tailTrace_5508108 : CollatzResearch.WordTrace tailWord_5508108 prefixEnd_5508108 2828306900875240735818679 := by
  unfold tailWord_5508108
  simp only [CollatzResearch.WordTrace]
  refine ⟨100448601564536450398882489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133931468752715267198509985 100448601564536450398882489)
  ·
    refine ⟨75336451173402337799161867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100448601564536450398882489 75336451173402337799161867)
    ·
      refine ⟨113004676760103506698742801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75336451173402337799161867 113004676760103506698742801)
      ·
        refine ⟨84753507570077630024057101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113004676760103506698742801 84753507570077630024057101)
        ·
          refine ⟨31782565338779111259021413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84753507570077630024057101 31782565338779111259021413)
          ·
            refine ⟨5959231001021083361066515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31782565338779111259021413 5959231001021083361066515)
            ·
              refine ⟨8938846501531625041599773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959231001021083361066515 8938846501531625041599773)
              ·
                refine ⟨3352067438074359390599915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8938846501531625041599773 3352067438074359390599915)
                ·
                  refine ⟨5028101157111539085899873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352067438074359390599915 5028101157111539085899873)
                  ·
                    refine ⟨3771075867833654314424905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028101157111539085899873 3771075867833654314424905)
                    ·
                      refine ⟨2828306900875240735818679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771075867833654314424905 2828306900875240735818679)
                      ·
                        rfl

theorem cell23_5508108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_5508108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508108 prefixEnd_5508108 := by exact prefixLift 5508108
  have htrace : WordTrace (prefixWord ++ tailWord_5508108) baseStart_5508108 baseEnd_5508108 := by
    simpa [prefixWord, tailWord_5508108, baseEnd_5508108] using wordTrace_append hprefix tailTrace_5508108
  have hstable : (prefixWord ++ tailWord_5508108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508108).length < 2 ^ (prefixWord ++ tailWord_5508108).sum := by decide
  have hdescent : baseEnd_5508108 < baseStart_5508108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508113 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_5508113 : Nat := 118140960795 + 5508113 * 2 ^ 59
def prefixEnd_5508113 : Nat := 4983230072969 + 3 ^ 40 * 5508113 * 2
def baseEnd_5508113 : Nat := 2828309468278513216256155

theorem tailTrace_5508113 : CollatzResearch.WordTrace tailWord_5508113 prefixEnd_5508113 2828309468278513216256155 := by
  unfold tailWord_5508113
  simp only [CollatzResearch.WordTrace]
  refine ⟨200897385494054786651696993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133931590329369857767797995 200897385494054786651696993)
  ·
    refine ⟨150673039120541089988772745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200897385494054786651696993 150673039120541089988772745)
    ·
      refine ⟨113004779340405817491579559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150673039120541089988772745 113004779340405817491579559)
      ·
        refine ⟨169507169010608726237369339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113004779340405817491579559 169507169010608726237369339)
        ·
          refine ⟨254260753515913089356054009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169507169010608726237369339 254260753515913089356054009)
          ·
            refine ⟨190695565136934817017040507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254260753515913089356054009 190695565136934817017040507)
            ·
              refine ⟨286043347705402225525560761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190695565136934817017040507 286043347705402225525560761)
              ·
                refine ⟨214532510779051669144170571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286043347705402225525560761 214532510779051669144170571)
                ·
                  refine ⟨321798766168577503716255857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214532510779051669144170571 321798766168577503716255857)
                  ·
                    refine ⟨241349074626433127787191893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321798766168577503716255857 241349074626433127787191893)
                    ·
                      refine ⟨2828309468278513216256155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241349074626433127787191893 2828309468278513216256155)
                      ·
                        rfl

theorem cell23_5508113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_5508113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508113 prefixEnd_5508113 := by exact prefixLift 5508113
  have htrace : WordTrace (prefixWord ++ tailWord_5508113) baseStart_5508113 baseEnd_5508113 := by
    simpa [prefixWord, tailWord_5508113, baseEnd_5508113] using wordTrace_append hprefix tailTrace_5508113
  have hstable : (prefixWord ++ tailWord_5508113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508113).length < 2 ^ (prefixWord ++ tailWord_5508113).sum := by decide
  have hdescent : baseEnd_5508113 < baseStart_5508113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508125 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_5508125 : Nat := 118140960795 + 5508125 * 2 ^ 59
def prefixEnd_5508125 : Nat := 4983230072969 + 3 ^ 40 * 5508125 * 2
def baseEnd_5508125 : Nat := 2828315630046367169306101

theorem tailTrace_5508125 : CollatzResearch.WordTrace tailWord_5508125 prefixEnd_5508125 2828315630046367169306101 := by
  unfold tailWord_5508125
  simp only [CollatzResearch.WordTrace]
  refine ⟨200897823170011312701133829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133931882113340875134089219 200897823170011312701133829)
  ·
    refine ⟨37668341844377121131462593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200897823170011312701133829 37668341844377121131462593)
    ·
      refine ⟨28251256383282840848596945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37668341844377121131462593 28251256383282840848596945)
      ·
        refine ⟨21188442287462130636447709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28251256383282840848596945 21188442287462130636447709)
        ·
          refine ⟨7945665857798298988667891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21188442287462130636447709 7945665857798298988667891)
          ·
            refine ⟨11918498786697448483001837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945665857798298988667891 11918498786697448483001837)
            ·
              refine ⟨4469437045011543181125689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11918498786697448483001837 4469437045011543181125689)
              ·
                refine ⟨3352077783758657385844267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469437045011543181125689 3352077783758657385844267)
                ·
                  refine ⟨5028116675637986078766401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352077783758657385844267 5028116675637986078766401)
                  ·
                    refine ⟨3771087506728489559074801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028116675637986078766401 3771087506728489559074801)
                    ·
                      refine ⟨2828315630046367169306101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771087506728489559074801 2828315630046367169306101)
                      ·
                        rfl

theorem cell23_5508125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_5508125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508125 prefixEnd_5508125 := by exact prefixLift 5508125
  have htrace : WordTrace (prefixWord ++ tailWord_5508125) baseStart_5508125 baseEnd_5508125 := by
    simpa [prefixWord, tailWord_5508125, baseEnd_5508125] using wordTrace_append hprefix tailTrace_5508125
  have hstable : (prefixWord ++ tailWord_5508125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508125).length < 2 ^ (prefixWord ++ tailWord_5508125).sum := by decide
  have hdescent : baseEnd_5508125 < baseStart_5508125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508147 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 1, 4, 2]
def baseStart_5508147 : Nat := 118140960795 + 5508147 * 2 ^ 59
def prefixEnd_5508147 : Nat := 4983230072969 + 3 ^ 40 * 5508147 * 2
def baseEnd_5508147 : Nat := 2828326926620766083230999

theorem tailTrace_5508147 : CollatzResearch.WordTrace tailWord_5508147 prefixEnd_5508147 2828326926620766083230999 := by
  unfold tailWord_5508147
  simp only [CollatzResearch.WordTrace]
  refine ⟨200898625575931610458434695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133932417050621073638956463 200898625575931610458434695)
  ·
    refine ⟨301347938363897415687652043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200898625575931610458434695 301347938363897415687652043)
    ·
      refine ⟨452021907545846123531478065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301347938363897415687652043 452021907545846123531478065)
      ·
        refine ⟨339016430659384592648608549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452021907545846123531478065 339016430659384592648608549)
        ·
          refine ⟨63565580748634611121614103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339016430659384592648608549 63565580748634611121614103)
          ·
            refine ⟨95348371122951916682421155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63565580748634611121614103 95348371122951916682421155)
            ·
              refine ⟨143022556684427875023631733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95348371122951916682421155 143022556684427875023631733)
              ·
                refine ⟨13408364689165113283465475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143022556684427875023631733 13408364689165113283465475)
                ·
                  refine ⟨20112547033747669925198213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13408364689165113283465475 20112547033747669925198213)
                  ·
                    refine ⟨3771102568827688110974665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20112547033747669925198213 3771102568827688110974665)
                    ·
                      refine ⟨2828326926620766083230999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771102568827688110974665 2828326926620766083230999)
                      ·
                        rfl

theorem cell23_5508147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4, 2].length) (baseStart_5508147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508147 prefixEnd_5508147 := by exact prefixLift 5508147
  have htrace : WordTrace (prefixWord ++ tailWord_5508147) baseStart_5508147 baseEnd_5508147 := by
    simpa [prefixWord, tailWord_5508147, baseEnd_5508147] using wordTrace_append hprefix tailTrace_5508147
  have hstable : (prefixWord ++ tailWord_5508147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508147).length < 2 ^ (prefixWord ++ tailWord_5508147).sum := by decide
  have hdescent : baseEnd_5508147 < baseStart_5508147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508180 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_5508180 : Nat := 118140960795 + 5508180 * 2 ^ 59
def prefixEnd_5508180 : Nat := 4983230072969 + 3 ^ 40 * 5508180 * 2
def baseEnd_5508180 : Nat := 2828343871482364454118347

theorem tailTrace_5508180 : CollatzResearch.WordTrace tailWord_5508180 prefixEnd_5508180 2828343871482364454118347 := by
  unfold tailWord_5508180
  simp only [CollatzResearch.WordTrace]
  refine ⟨100449914592406028547192997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133933219456541371396257329 100449914592406028547192997)
  ·
    refine ⟨18834358986076130352598687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100449914592406028547192997 18834358986076130352598687)
    ·
      refine ⟨28251538479114195528898031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18834358986076130352598687 28251538479114195528898031)
      ·
        refine ⟨42377307718671293293347047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28251538479114195528898031 42377307718671293293347047)
        ·
          refine ⟨63565961578006939940020571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42377307718671293293347047 63565961578006939940020571)
          ·
            refine ⟨95348942367010409910030857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63565961578006939940020571 95348942367010409910030857)
            ·
              refine ⟨71511706775257807432523143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95348942367010409910030857 71511706775257807432523143)
              ·
                refine ⟨107267560162886711148784715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71511706775257807432523143 107267560162886711148784715)
                ·
                  refine ⟨160901340244330066723177073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107267560162886711148784715 160901340244330066723177073)
                  ·
                    refine ⟨120676005183247550042382805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160901340244330066723177073 120676005183247550042382805)
                    ·
                      refine ⟨2828343871482364454118347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120676005183247550042382805 2828343871482364454118347)
                      ·
                        rfl

theorem cell23_5508180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_5508180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508180 prefixEnd_5508180 := by exact prefixLift 5508180
  have htrace : WordTrace (prefixWord ++ tailWord_5508180) baseStart_5508180 baseEnd_5508180 := by
    simpa [prefixWord, tailWord_5508180, baseEnd_5508180] using wordTrace_append hprefix tailTrace_5508180
  have hstable : (prefixWord ++ tailWord_5508180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508180).length < 2 ^ (prefixWord ++ tailWord_5508180).sum := by decide
  have hdescent : baseEnd_5508180 < baseStart_5508180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508181 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_5508181 : Nat := 118140960795 + 5508181 * 2 ^ 59
def prefixEnd_5508181 : Nat := 4983230072969 + 3 ^ 40 * 5508181 * 2
def baseEnd_5508181 : Nat := 2828344384963018950205843

theorem tailTrace_5508181 : CollatzResearch.WordTrace tailWord_5508181 prefixEnd_5508181 2828344384963018950205843 := by
  unfold tailWord_5508181
  simp only [CollatzResearch.WordTrace]
  refine ⟨200899865657808434265172397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133933243771872289510114931 200899865657808434265172397)
  ·
    refine ⟨75337449621678162849439649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200899865657808434265172397 75337449621678162849439649)
    ·
      refine ⟨56503087216258622137079737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75337449621678162849439649 56503087216258622137079737)
      ·
        refine ⟨42377315412193966602809803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56503087216258622137079737 42377315412193966602809803)
        ·
          refine ⟨63565973118290949904214705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42377315412193966602809803 63565973118290949904214705)
          ·
            refine ⟨47674479838718212428161029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63565973118290949904214705 47674479838718212428161029)
            ·
              refine ⟨8938964969759664830280193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47674479838718212428161029 8938964969759664830280193)
              ·
                refine ⟨6704223727319748622710145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8938964969759664830280193 6704223727319748622710145)
                ·
                  refine ⟨5028167795489811467032609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6704223727319748622710145 5028167795489811467032609)
                  ·
                    refine ⟨3771125846617358600274457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028167795489811467032609 3771125846617358600274457)
                    ·
                      refine ⟨2828344384963018950205843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771125846617358600274457 2828344384963018950205843)
                      ·
                        rfl

theorem cell23_5508181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_5508181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508181 prefixEnd_5508181 := by exact prefixLift 5508181
  have htrace : WordTrace (prefixWord ++ tailWord_5508181) baseStart_5508181 baseEnd_5508181 := by
    simpa [prefixWord, tailWord_5508181, baseEnd_5508181] using wordTrace_append hprefix tailTrace_5508181
  have hstable : (prefixWord ++ tailWord_5508181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508181).length < 2 ^ (prefixWord ++ tailWord_5508181).sum := by decide
  have hdescent : baseEnd_5508181 < baseStart_5508181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508194 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5508194 : Nat := 118140960795 + 5508194 * 2 ^ 59
def prefixEnd_5508194 : Nat := 4983230072969 + 3 ^ 40 * 5508194 * 2
def baseEnd_5508194 : Nat := 2828351060211527399343283

theorem tailTrace_5508194 : CollatzResearch.WordTrace tailWord_5508194 prefixEnd_5508194 2828351060211527399343283 := by
  unfold tailWord_5508194
  simp only [CollatzResearch.WordTrace]
  refine ⟨50225084951690334371348909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133933559871174224990263757 50225084951690334371348909)
  ·
    refine ⟨18834406856883875389255841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50225084951690334371348909 18834406856883875389255841)
    ·
      refine ⟨14125805142662906541941881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18834406856883875389255841 14125805142662906541941881)
      ·
        refine ⟨10594353856997179906456411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14125805142662906541941881 10594353856997179906456411)
        ·
          refine ⟨15891530785495769859684617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594353856997179906456411 15891530785495769859684617)
          ·
            refine ⟨11918648089121827394763463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15891530785495769859684617 11918648089121827394763463)
            ·
              refine ⟨17877972133682741092145195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11918648089121827394763463 17877972133682741092145195)
              ·
                refine ⟨26816958200524111638217793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17877972133682741092145195 26816958200524111638217793)
                ·
                  refine ⟨20112718650393083728663345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26816958200524111638217793 20112718650393083728663345)
                  ·
                    refine ⟨15084538987794812796497509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20112718650393083728663345 15084538987794812796497509)
                    ·
                      refine ⟨2828351060211527399343283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15084538987794812796497509 2828351060211527399343283)
                      ·
                        rfl

theorem cell23_5508194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5508194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508194 prefixEnd_5508194 := by exact prefixLift 5508194
  have htrace : WordTrace (prefixWord ++ tailWord_5508194) baseStart_5508194 baseEnd_5508194 := by
    simpa [prefixWord, tailWord_5508194, baseEnd_5508194] using wordTrace_append hprefix tailTrace_5508194
  have hstable : (prefixWord ++ tailWord_5508194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508194).length < 2 ^ (prefixWord ++ tailWord_5508194).sum := by decide
  have hdescent : baseEnd_5508194 < baseStart_5508194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508197 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_5508197 : Nat := 118140960795 + 5508197 * 2 ^ 59
def prefixEnd_5508197 : Nat := 4983230072969 + 3 ^ 40 * 5508197 * 2
def baseEnd_5508197 : Nat := 2828352600653490887605769

theorem tailTrace_5508197 : CollatzResearch.WordTrace tailWord_5508197 prefixEnd_5508197 2828352600653490887605769 := by
  unfold tailWord_5508197
  simp only [CollatzResearch.WordTrace]
  refine ⟨200900449225750468997754845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133933632817166979331836563 200900449225750468997754845)
  ·
    refine ⟨75337668459656425874158067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200900449225750468997754845 75337668459656425874158067)
    ·
      refine ⟨113006502689484638811237101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75337668459656425874158067 113006502689484638811237101)
      ·
        refine ⟨42377438508556739554213913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113006502689484638811237101 42377438508556739554213913)
        ·
          refine ⟨31783078881417554665660435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42377438508556739554213913 31783078881417554665660435)
          ·
            refine ⟨47674618322126331998490653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31783078881417554665660435 47674618322126331998490653)
            ·
              refine ⟨17877981870797374499433995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47674618322126331998490653 17877981870797374499433995)
              ·
                refine ⟨26816972806196061749150993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17877981870797374499433995 26816972806196061749150993)
                ·
                  refine ⟨20112729604647046311863245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26816972806196061749150993 20112729604647046311863245)
                  ·
                    refine ⟨7542273601742642366948717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20112729604647046311863245 7542273601742642366948717)
                    ·
                      refine ⟨2828352600653490887605769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542273601742642366948717 2828352600653490887605769)
                      ·
                        rfl

theorem cell23_5508197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_5508197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508197 prefixEnd_5508197 := by exact prefixLift 5508197
  have htrace : WordTrace (prefixWord ++ tailWord_5508197) baseStart_5508197 baseEnd_5508197 := by
    simpa [prefixWord, tailWord_5508197, baseEnd_5508197] using wordTrace_append hprefix tailTrace_5508197
  have hstable : (prefixWord ++ tailWord_5508197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508197).length < 2 ^ (prefixWord ++ tailWord_5508197).sum := by decide
  have hdescent : baseEnd_5508197 < baseStart_5508197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508207 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 5, 2]
def baseStart_5508207 : Nat := 118140960795 + 5508207 * 2 ^ 59
def prefixEnd_5508207 : Nat := 4983230072969 + 3 ^ 40 * 5508207 * 2
def baseEnd_5508207 : Nat := 2828357735460035848480723

theorem tailTrace_5508207 : CollatzResearch.WordTrace tailWord_5508207 prefixEnd_5508207 2828357735460035848480723 := by
  unfold tailWord_5508207
  simp only [CollatzResearch.WordTrace]
  refine ⟨200900813955714240705618875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133933875970476160470412583 200900813955714240705618875)
  ·
    refine ⟨301351220933571361058428313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200900813955714240705618875 301351220933571361058428313)
    ·
      refine ⟨226013415700178520793821235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301351220933571361058428313 226013415700178520793821235)
      ·
        refine ⟨339020123550267781190731853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226013415700178520793821235 339020123550267781190731853)
        ·
          refine ⟨127132546331350417946524445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339020123550267781190731853 127132546331350417946524445)
          ·
            refine ⟨47674704874256406729946667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127132546331350417946524445 47674704874256406729946667)
            ·
              refine ⟨71512057311384610094920001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47674704874256406729946667 71512057311384610094920001)
              ·
                refine ⟨53634042983538457571190001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71512057311384610094920001 53634042983538457571190001)
                ·
                  refine ⟨40225532237653843178392501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53634042983538457571190001 40225532237653843178392501)
                  ·
                    refine ⟨3771143647280047797974297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40225532237653843178392501 3771143647280047797974297)
                    ·
                      refine ⟨2828357735460035848480723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771143647280047797974297 2828357735460035848480723)
                      ·
                        rfl

theorem cell23_5508207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5, 2].length) (baseStart_5508207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508207 prefixEnd_5508207 := by exact prefixLift 5508207
  have htrace : WordTrace (prefixWord ++ tailWord_5508207) baseStart_5508207 baseEnd_5508207 := by
    simpa [prefixWord, tailWord_5508207, baseEnd_5508207] using wordTrace_append hprefix tailTrace_5508207
  have hstable : (prefixWord ++ tailWord_5508207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508207).length < 2 ^ (prefixWord ++ tailWord_5508207).sum := by decide
  have hdescent : baseEnd_5508207 < baseStart_5508207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508217 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_5508217 : Nat := 118140960795 + 5508217 * 2 ^ 59
def prefixEnd_5508217 : Nat := 4983230072969 + 3 ^ 40 * 5508217 * 2
def baseEnd_5508217 : Nat := 942787623422193603118559

theorem tailTrace_5508217 : CollatzResearch.WordTrace tailWord_5508217 prefixEnd_5508217 942787623422193603118559 := by
  unfold tailWord_5508217
  simp only [CollatzResearch.WordTrace]
  refine ⟨200901178685678012413482905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133934119123785341608988603 200901178685678012413482905)
  ·
    refine ⟨150675884014258509310112179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200901178685678012413482905 150675884014258509310112179)
    ·
      refine ⟨226013826021387763965168269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150675884014258509310112179 226013826021387763965168269)
      ·
        refine ⟨84755184758020411486938101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226013826021387763965168269 84755184758020411486938101)
        ·
          refine ⟨7945798571064413576900447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84755184758020411486938101 7945798571064413576900447)
          ·
            refine ⟨11918697856596620365350671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7945798571064413576900447 11918697856596620365350671)
            ·
              refine ⟨17878046784894930548026007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11918697856596620365350671 17878046784894930548026007)
              ·
                refine ⟨26817070177342395822039011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17878046784894930548026007 26817070177342395822039011)
                ·
                  refine ⟨40225605266013593733058517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26817070177342395822039011 40225605266013593733058517)
                  ·
                    refine ⟨942787623422193603118559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40225605266013593733058517 942787623422193603118559)
                    ·
                      rfl

theorem cell23_5508217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_5508217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508217 prefixEnd_5508217 := by exact prefixLift 5508217
  have htrace : WordTrace (prefixWord ++ tailWord_5508217) baseStart_5508217 baseEnd_5508217 := by
    simpa [prefixWord, tailWord_5508217, baseEnd_5508217] using wordTrace_append hprefix tailTrace_5508217
  have hstable : (prefixWord ++ tailWord_5508217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508217).length < 2 ^ (prefixWord ++ tailWord_5508217).sum := by decide
  have hdescent : baseEnd_5508217 < baseStart_5508217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508254 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5508254 : Nat := 118140960795 + 5508254 * 2 ^ 59
def prefixEnd_5508254 : Nat := 4983230072969 + 3 ^ 40 * 5508254 * 2
def baseEnd_5508254 : Nat := 2828381869050797164593007

theorem tailTrace_5508254 : CollatzResearch.WordTrace tailWord_5508254 prefixEnd_5508254 2828381869050797164593007 := by
  unfold tailWord_5508254
  simp only [CollatzResearch.WordTrace]
  refine ⟨25112816023317995966572477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133935018791029311821719877 25112816023317995966572477)
  ·
    refine ⟨9417306008744248487464679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25112816023317995966572477 9417306008744248487464679)
    ·
      refine ⟨14125959013116372731197019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9417306008744248487464679 14125959013116372731197019)
      ·
        refine ⟨21188938519674559096795529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125959013116372731197019 21188938519674559096795529)
        ·
          refine ⟨15891703889755919322596647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21188938519674559096795529 15891703889755919322596647)
          ·
            refine ⟨23837555834633878983894971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15891703889755919322596647 23837555834633878983894971)
            ·
              refine ⟨35756333751950818475842457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23837555834633878983894971 35756333751950818475842457)
              ·
                refine ⟨26817250313963113856881843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35756333751950818475842457 26817250313963113856881843)
                ·
                  refine ⟨40225875470944670785322765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26817250313963113856881843 40225875470944670785322765)
                  ·
                    refine ⟨15084703301604251544496037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40225875470944670785322765 15084703301604251544496037)
                    ·
                      refine ⟨2828381869050797164593007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15084703301604251544496037 2828381869050797164593007)
                      ·
                        rfl

theorem cell23_5508254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5508254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508254 prefixEnd_5508254 := by exact prefixLift 5508254
  have htrace : WordTrace (prefixWord ++ tailWord_5508254) baseStart_5508254 baseEnd_5508254 := by
    simpa [prefixWord, tailWord_5508254, baseEnd_5508254] using wordTrace_append hprefix tailTrace_5508254
  have hstable : (prefixWord ++ tailWord_5508254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508254).length < 2 ^ (prefixWord ++ tailWord_5508254).sum := by decide
  have hdescent : baseEnd_5508254 < baseStart_5508254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508257 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5508257 : Nat := 118140960795 + 5508257 * 2 ^ 59
def prefixEnd_5508257 : Nat := 4983230072969 + 3 ^ 40 * 5508257 * 2
def baseEnd_5508257 : Nat := 2828383409492760652855493

theorem tailTrace_5508257 : CollatzResearch.WordTrace tailWord_5508257 prefixEnd_5508257 2828383409492760652855493 := by
  unfold tailWord_5508257
  simp only [CollatzResearch.WordTrace]
  refine ⟨200902637605533099244939025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133935091737022066163292683 200902637605533099244939025)
  ·
    refine ⟨150676978204149824433704269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200902637605533099244939025 150676978204149824433704269)
    ·
      refine ⟨56503866826556184162639101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150676978204149824433704269 56503866826556184162639101)
      ·
        refine ⟨21188950059958569060989663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56503866826556184162639101 21188950059958569060989663)
        ·
          refine ⟨31783425089937853591484495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21188950059958569060989663 31783425089937853591484495)
          ·
            refine ⟨47675137634906780387226743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31783425089937853591484495 47675137634906780387226743)
            ·
              refine ⟨71512706452360170580840115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47675137634906780387226743 71512706452360170580840115)
              ·
                refine ⟨107269059678540255871260173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71512706452360170580840115 107269059678540255871260173)
                ·
                  refine ⟨40225897379452595951722565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107269059678540255871260173 40225897379452595951722565)
                  ·
                    refine ⟨7542355758647361740947981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40225897379452595951722565 7542355758647361740947981)
                    ·
                      refine ⟨2828383409492760652855493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542355758647361740947981 2828383409492760652855493)
                      ·
                        rfl

theorem cell23_5508257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5508257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508257 prefixEnd_5508257 := by exact prefixLift 5508257
  have htrace : WordTrace (prefixWord ++ tailWord_5508257) baseStart_5508257 baseEnd_5508257 := by
    simpa [prefixWord, tailWord_5508257, baseEnd_5508257] using wordTrace_append hprefix tailTrace_5508257
  have hstable : (prefixWord ++ tailWord_5508257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508257).length < 2 ^ (prefixWord ++ tailWord_5508257).sum := by decide
  have hdescent : baseEnd_5508257 < baseStart_5508257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_5508280 : Nat := 118140960795 + 5508280 * 2 ^ 59
def prefixEnd_5508280 : Nat := 4983230072969 + 3 ^ 40 * 5508280 * 2
def baseEnd_5508280 : Nat := 2828395219547814062867887

theorem tailTrace_5508280 : CollatzResearch.WordTrace tailWord_5508280 prefixEnd_5508280 2828395219547814062867887 := by
  unfold tailWord_5508280
  simp only [CollatzResearch.WordTrace]
  refine ⟨100451738242224887086513147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133935650989633182782017529 100451738242224887086513147)
  ·
    refine ⟨150677607363337330629769721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100451738242224887086513147 150677607363337330629769721)
    ·
      refine ⟨113008205522502997972327291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150677607363337330629769721 113008205522502997972327291)
      ·
        refine ⟨169512308283754496958490937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113008205522502997972327291 169512308283754496958490937)
        ·
          refine ⟨127134231212815872718868203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169512308283754496958490937 127134231212815872718868203)
          ·
            refine ⟨190701346819223809078302305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127134231212815872718868203 190701346819223809078302305)
            ·
              refine ⟨143026010114417856808726729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190701346819223809078302305 143026010114417856808726729)
              ·
                refine ⟨107269507585813392606545047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143026010114417856808726729 107269507585813392606545047)
                ·
                  refine ⟨160904261378720088909817571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107269507585813392606545047 160904261378720088909817571)
                  ·
                    refine ⟨241356392068080133364726357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160904261378720088909817571 241356392068080133364726357)
                    ·
                      refine ⟨2828395219547814062867887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241356392068080133364726357 2828395219547814062867887)
                      ·
                        rfl

theorem cell23_5508280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_5508280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508280 prefixEnd_5508280 := by exact prefixLift 5508280
  have htrace : WordTrace (prefixWord ++ tailWord_5508280) baseStart_5508280 baseEnd_5508280 := by
    simpa [prefixWord, tailWord_5508280, baseEnd_5508280] using wordTrace_append hprefix tailTrace_5508280
  have hstable : (prefixWord ++ tailWord_5508280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508280).length < 2 ^ (prefixWord ++ tailWord_5508280).sum := by decide
  have hdescent : baseEnd_5508280 < baseStart_5508280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508281 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 1, 4]
def baseStart_5508281 : Nat := 118140960795 + 5508281 * 2 ^ 59
def prefixEnd_5508281 : Nat := 4983230072969 + 3 ^ 40 * 5508281 * 2
def baseEnd_5508281 : Nat := 942798577676156186318461

theorem tailTrace_5508281 : CollatzResearch.WordTrace tailWord_5508281 prefixEnd_5508281 942798577676156186318461 := by
  unfold tailWord_5508281
  simp only [CollatzResearch.WordTrace]
  refine ⟨200903512957446151343812697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133935675304964100895875131 200903512957446151343812697)
  ·
    refine ⟨150677634718084613507859523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200903512957446151343812697 150677634718084613507859523)
    ·
      refine ⟨226016452077126920261789285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150677634718084613507859523 226016452077126920261789285)
      ·
        refine ⟨42378084764461297549085491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226016452077126920261789285 42378084764461297549085491)
        ·
          refine ⟨63567127146691946323628237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42378084764461297549085491 63567127146691946323628237)
          ·
            refine ⟨23837672680009479871360589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63567127146691946323628237 23837672680009479871360589)
            ·
              refine ⟨8939127255003554951760221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23837672680009479871360589 8939127255003554951760221)
              ·
                refine ⟨3352172720626333106910083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8939127255003554951760221 3352172720626333106910083)
                ·
                  refine ⟨5028259080939499660365125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352172720626333106910083 5028259080939499660365125)
                  ·
                    refine ⟨942798577676156186318461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028259080939499660365125 942798577676156186318461)
                    ·
                      rfl

theorem cell23_5508281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 4].length) (baseStart_5508281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508281 prefixEnd_5508281 := by exact prefixLift 5508281
  have htrace : WordTrace (prefixWord ++ tailWord_5508281) baseStart_5508281 baseEnd_5508281 := by
    simpa [prefixWord, tailWord_5508281, baseEnd_5508281] using wordTrace_append hprefix tailTrace_5508281
  have hstable : (prefixWord ++ tailWord_5508281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508281).length < 2 ^ (prefixWord ++ tailWord_5508281).sum := by decide
  have hdescent : baseEnd_5508281 < baseStart_5508281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508298 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_5508298 : Nat := 118140960795 + 5508298 * 2 ^ 59
def prefixEnd_5508298 : Nat := 4983230072969 + 3 ^ 40 * 5508298 * 2
def baseEnd_5508298 : Nat := 942801487399864997480935

theorem tailTrace_5508298 : CollatzResearch.WordTrace tailWord_5508298 prefixEnd_5508298 942801487399864997480935 := by
  unfold tailWord_5508298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226033249596140811795387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133936088665589708831454365 50226033249596140811795387)
  ·
    refine ⟨75339049874394211217693081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50226033249596140811795387 75339049874394211217693081)
    ·
      refine ⟨56504287405795658413269811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75339049874394211217693081 56504287405795658413269811)
      ·
        refine ⟨84756431108693487619904717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56504287405795658413269811 84756431108693487619904717)
        ·
          refine ⟨31783661665760057857464269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84756431108693487619904717 31783661665760057857464269)
          ·
            refine ⟨11918873124660021696549101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31783661665760057857464269 11918873124660021696549101)
            ·
              refine ⟨4469577421747508136205913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11918873124660021696549101 4469577421747508136205913)
              ·
                refine ⟨3352183066310631102154435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469577421747508136205913 3352183066310631102154435)
                ·
                  refine ⟨5028274599465946653231653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352183066310631102154435 5028274599465946653231653)
                  ·
                    refine ⟨942801487399864997480935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028274599465946653231653 942801487399864997480935)
                    ·
                      rfl

theorem cell23_5508298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_5508298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508298 prefixEnd_5508298 := by exact prefixLift 5508298
  have htrace : WordTrace (prefixWord ++ tailWord_5508298) baseStart_5508298 baseEnd_5508298 := by
    simpa [prefixWord, tailWord_5508298, baseEnd_5508298] using wordTrace_append hprefix tailTrace_5508298
  have hstable : (prefixWord ++ tailWord_5508298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508298).length < 2 ^ (prefixWord ++ tailWord_5508298).sum := by decide
  have hdescent : baseEnd_5508298 < baseStart_5508298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508314 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_5508314 : Nat := 118140960795 + 5508314 * 2 ^ 59
def prefixEnd_5508314 : Nat := 4983230072969 + 3 ^ 40 * 5508314 * 2
def baseEnd_5508314 : Nat := 2828412677890066929842731

theorem tailTrace_5508314 : CollatzResearch.WordTrace tailWord_5508314 prefixEnd_5508314 2828412677890066929842731 := by
  unfold tailWord_5508314
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226179141581649494940999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133936477710884398653175997 50226179141581649494940999)
  ·
    refine ⟨75339268712372474242411499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50226179141581649494940999 75339268712372474242411499)
    ·
      refine ⟨113008903068558711363617249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75339268712372474242411499 113008903068558711363617249)
      ·
        refine ⟨84756677301419033522712937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113008903068558711363617249 84756677301419033522712937)
        ·
          refine ⟨63567507976064275142034703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84756677301419033522712937 63567507976064275142034703)
          ·
            refine ⟨95351261964096412713052055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63567507976064275142034703 95351261964096412713052055)
            ·
              refine ⟨143026892946144619069578083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95351261964096412713052055 143026892946144619069578083)
              ·
                refine ⟨214540339419216928604367125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143026892946144619069578083 214540339419216928604367125)
                ·
                  refine ⟨10056578410275793528329709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214540339419216928604367125 10056578410275793528329709)
                  ·
                    refine ⟨3771216903853422573123641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10056578410275793528329709 3771216903853422573123641)
                    ·
                      refine ⟨2828412677890066929842731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771216903853422573123641 2828412677890066929842731)
                      ·
                        rfl

theorem cell23_5508314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_5508314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508314 prefixEnd_5508314 := by exact prefixLift 5508314
  have htrace : WordTrace (prefixWord ++ tailWord_5508314) baseStart_5508314 baseEnd_5508314 := by
    simpa [prefixWord, tailWord_5508314, baseEnd_5508314] using wordTrace_append hprefix tailTrace_5508314
  have hstable : (prefixWord ++ tailWord_5508314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508314).length < 2 ^ (prefixWord ++ tailWord_5508314).sum := by decide
  have hdescent : baseEnd_5508314 < baseStart_5508314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508324 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_5508324 : Nat := 118140960795 + 5508324 * 2 ^ 59
def prefixEnd_5508324 : Nat := 4983230072969 + 3 ^ 40 * 5508324 * 2
def baseEnd_5508324 : Nat := 942805937565537296905895

theorem tailTrace_5508324 : CollatzResearch.WordTrace tailWord_5508324 prefixEnd_5508324 942805937565537296905895 := by
  unfold tailWord_5508324
  simp only [CollatzResearch.WordTrace]
  refine ⟨100452540648145184843814013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133936720864193579791752017 100452540648145184843814013)
  ·
    refine ⟨37669702743054444316430255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100452540648145184843814013 37669702743054444316430255)
    ·
      refine ⟨56504554114581666474645383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37669702743054444316430255 56504554114581666474645383)
      ·
        refine ⟨84756831171872499711968075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56504554114581666474645383 84756831171872499711968075)
        ·
          refine ⟨127135246757808749567952113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84756831171872499711968075 127135246757808749567952113)
          ·
            refine ⟨95351435068356562175964085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127135246757808749567952113 95351435068356562175964085)
            ·
              refine ⟨8939197037658427703996633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95351435068356562175964085 8939197037658427703996633)
              ·
                refine ⟨6704397778243820777997475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8939197037658427703996633 6704397778243820777997475)
                ·
                  refine ⟨10056596667365731166996213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704397778243820777997475 10056596667365731166996213)
                  ·
                    refine ⟨942805937565537296905895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10056596667365731166996213 942805937565537296905895)
                    ·
                      rfl

theorem cell23_5508324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_5508324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508324 prefixEnd_5508324 := by exact prefixLift 5508324
  have htrace : WordTrace (prefixWord ++ tailWord_5508324) baseStart_5508324 baseEnd_5508324 := by
    simpa [prefixWord, tailWord_5508324, baseEnd_5508324] using wordTrace_append hprefix tailTrace_5508324
  have hstable : (prefixWord ++ tailWord_5508324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508324).length < 2 ^ (prefixWord ++ tailWord_5508324).sum := by decide
  have hdescent : baseEnd_5508324 < baseStart_5508324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508331 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 2, 3, 2]
def baseStart_5508331 : Nat := 118140960795 + 5508331 * 2 ^ 59
def prefixEnd_5508331 : Nat := 4983230072969 + 3 ^ 40 * 5508331 * 2
def baseEnd_5508331 : Nat := 2828421407061193363330153

theorem tailTrace_5508331 : CollatzResearch.WordTrace tailWord_5508331 prefixEnd_5508331 2828421407061193363330153 := by
  unfold tailWord_5508331
  simp only [CollatzResearch.WordTrace]
  refine ⟨200905336607265009883132847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133936891071510006588755231 200905336607265009883132847)
  ·
    refine ⟨301358004910897514824699271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200905336607265009883132847 301358004910897514824699271)
    ·
      refine ⟨452037007366346272237048907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301358004910897514824699271 452037007366346272237048907)
      ·
        refine ⟨678055511049519408355573361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452037007366346272237048907 678055511049519408355573361)
        ·
          refine ⟨508541633287139556266680021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678055511049519408355573361 508541633287139556266680021)
          ·
            refine ⟨11918944530167333350000313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 508541633287139556266680021 11918944530167333350000313)
            ·
              refine ⟨8939208397625500012500235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11918944530167333350000313 8939208397625500012500235)
              ·
                refine ⟨13408812596438250018750353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8939208397625500012500235 13408812596438250018750353)
                ·
                  refine ⟨10056609447328687514062765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13408812596438250018750353 10056609447328687514062765)
                  ·
                    refine ⟨3771228542748257817773537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10056609447328687514062765 3771228542748257817773537)
                    ·
                      refine ⟨2828421407061193363330153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771228542748257817773537 2828421407061193363330153)
                      ·
                        rfl

theorem cell23_5508331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3, 2].length) (baseStart_5508331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508331 prefixEnd_5508331 := by exact prefixLift 5508331
  have htrace : WordTrace (prefixWord ++ tailWord_5508331) baseStart_5508331 baseEnd_5508331 := by
    simpa [prefixWord, tailWord_5508331, baseEnd_5508331] using wordTrace_append hprefix tailTrace_5508331
  have hstable : (prefixWord ++ tailWord_5508331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508331).length < 2 ^ (prefixWord ++ tailWord_5508331).sum := by decide
  have hdescent : baseEnd_5508331 < baseStart_5508331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508355 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 1, 1, 3]
def baseStart_5508355 : Nat := 118140960795 + 5508355 * 2 ^ 59
def prefixEnd_5508355 : Nat := 4983230072969 + 3 ^ 40 * 5508355 * 2
def baseEnd_5508355 : Nat := 2828433730596901269430043

theorem tailTrace_5508355 : CollatzResearch.WordTrace tailWord_5508355 prefixEnd_5508355 2828433730596901269430043 := by
  unfold tailWord_5508355
  simp only [CollatzResearch.WordTrace]
  refine ⟨200906211959178061982006519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133937474639452041321337679 200906211959178061982006519)
  ·
    refine ⟨301359317938767092973009779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200906211959178061982006519 301359317938767092973009779)
    ·
      refine ⟨452038976908150639459514669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301359317938767092973009779 452038976908150639459514669)
      ·
        refine ⟨169514616340556489797318001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452038976908150639459514669 169514616340556489797318001)
        ·
          refine ⟨127135962255417367347988501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169514616340556489797318001 127135962255417367347988501)
          ·
            refine ⟨5959498230722689094436961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127135962255417367347988501 5959498230722689094436961)
            ·
              refine ⟨4469623673042016820827721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959498230722689094436961 4469623673042016820827721)
              ·
                refine ⟨3352217754781512615620791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469623673042016820827721 3352217754781512615620791)
                ·
                  refine ⟨5028326632172268923431187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352217754781512615620791 5028326632172268923431187)
                  ·
                    refine ⟨7542489948258403385146781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028326632172268923431187 7542489948258403385146781)
                    ·
                      refine ⟨2828433730596901269430043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542489948258403385146781 2828433730596901269430043)
                      ·
                        rfl

theorem cell23_5508355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_5508355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508355 prefixEnd_5508355 := by exact prefixLift 5508355
  have htrace : WordTrace (prefixWord ++ tailWord_5508355) baseStart_5508355 baseEnd_5508355 := by
    simpa [prefixWord, tailWord_5508355, baseEnd_5508355] using wordTrace_append hprefix tailTrace_5508355
  have hstable : (prefixWord ++ tailWord_5508355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508355).length < 2 ^ (prefixWord ++ tailWord_5508355).sum := by decide
  have hdescent : baseEnd_5508355 < baseStart_5508355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508357 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_5508357 : Nat := 118140960795 + 5508357 * 2 ^ 59
def prefixEnd_5508357 : Nat := 4983230072969 + 3 ^ 40 * 5508357 * 2
def baseEnd_5508357 : Nat := 2828434757558210261605033

theorem tailTrace_5508357 : CollatzResearch.WordTrace tailWord_5508357 prefixEnd_5508357 2828434757558210261605033 := by
  unfold tailWord_5508357
  simp only [CollatzResearch.WordTrace]
  refine ⟨200906284905170816323579325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133937523270113877549052883 200906284905170816323579325)
  ·
    refine ⟨75339856839439056121342247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200906284905170816323579325 75339856839439056121342247)
    ·
      refine ⟨113009785259158584182013371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75339856839439056121342247 113009785259158584182013371)
      ·
        refine ⟨169514677888737876273020057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113009785259158584182013371 169514677888737876273020057)
        ·
          refine ⟨127136008416553407204765043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169514677888737876273020057 127136008416553407204765043)
          ·
            refine ⟨190704012624830110807147565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127136008416553407204765043 190704012624830110807147565)
            ·
              refine ⟨71514004734311291552680337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190704012624830110807147565 71514004734311291552680337)
              ·
                refine ⟨53635503550733468664510253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71514004734311291552680337 53635503550733468664510253)
                ·
                  refine ⟨20113313831525050749191345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53635503550733468664510253 20113313831525050749191345)
                  ·
                    refine ⟨15084985373643788061893509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20113313831525050749191345 15084985373643788061893509)
                    ·
                      refine ⟨2828434757558210261605033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15084985373643788061893509 2828434757558210261605033)
                      ·
                        rfl

theorem cell23_5508357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_5508357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508357 prefixEnd_5508357 := by exact prefixLift 5508357
  have htrace : WordTrace (prefixWord ++ tailWord_5508357) baseStart_5508357 baseEnd_5508357 := by
    simpa [prefixWord, tailWord_5508357, baseEnd_5508357] using wordTrace_append hprefix tailTrace_5508357
  have hstable : (prefixWord ++ tailWord_5508357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508357).length < 2 ^ (prefixWord ++ tailWord_5508357).sum := by decide
  have hdescent : baseEnd_5508357 < baseStart_5508357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508361 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 3, 2, 2]
def baseStart_5508361 : Nat := 118140960795 + 5508361 * 2 ^ 59
def prefixEnd_5508361 : Nat := 4983230072969 + 3 ^ 40 * 5508361 * 2
def baseEnd_5508361 : Nat := 2828436811480828245955015

theorem tailTrace_5508361 : CollatzResearch.WordTrace tailWord_5508361 prefixEnd_5508361 2828436811480828245955015 := by
  unfold tailWord_5508361
  simp only [CollatzResearch.WordTrace]
  refine ⟨200906430797156325006724937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133937620531437550004483291 200906430797156325006724937)
  ·
    refine ⟨150679823097867243755043703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200906430797156325006724937 150679823097867243755043703)
    ·
      refine ⟨226019734646800865632565555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150679823097867243755043703 226019734646800865632565555)
      ·
        refine ⟨339029601970201298448848333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226019734646800865632565555 339029601970201298448848333)
        ·
          refine ⟨127136100738825486918318125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339029601970201298448848333 127136100738825486918318125)
          ·
            refine ⟨47676037777059557594369297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127136100738825486918318125 47676037777059557594369297)
            ·
              refine ⟨35757028332794668195776973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47676037777059557594369297 35757028332794668195776973)
              ·
                refine ⟨13408885624798000573416365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35757028332794668195776973 13408885624798000573416365)
                ·
                  refine ⟨5028332109299250215031137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13408885624798000573416365 5028332109299250215031137)
                  ·
                    refine ⟨3771249081974437661273353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028332109299250215031137 3771249081974437661273353)
                    ·
                      refine ⟨2828436811480828245955015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771249081974437661273353 2828436811480828245955015)
                      ·
                        rfl

theorem cell23_5508361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2, 2].length) (baseStart_5508361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508361 prefixEnd_5508361 := by exact prefixLift 5508361
  have htrace : WordTrace (prefixWord ++ tailWord_5508361) baseStart_5508361 baseEnd_5508361 := by
    simpa [prefixWord, tailWord_5508361, baseEnd_5508361] using wordTrace_append hprefix tailTrace_5508361
  have hstable : (prefixWord ++ tailWord_5508361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508361).length < 2 ^ (prefixWord ++ tailWord_5508361).sum := by decide
  have hdescent : baseEnd_5508361 < baseStart_5508361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508364 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_5508364 : Nat := 118140960795 + 5508364 * 2 ^ 59
def prefixEnd_5508364 : Nat := 4983230072969 + 3 ^ 40 * 5508364 * 2
def baseEnd_5508364 : Nat := 2828438351922791734217501

theorem tailTrace_5508364 : CollatzResearch.WordTrace tailWord_5508364 prefixEnd_5508364 2828438351922791734217501 := by
  unfold tailWord_5508364
  simp only [CollatzResearch.WordTrace]
  refine ⟨100453270108072728259542073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133937693477430304346056097 100453270108072728259542073)
  ·
    refine ⟨75339952581054546194656555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100453270108072728259542073 75339952581054546194656555)
    ·
      refine ⟨113009928871581819291984833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75339952581054546194656555 113009928871581819291984833)
      ·
        refine ⟨84757446653686364468988625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113009928871581819291984833 84757446653686364468988625)
        ·
          refine ⟨63568084990264773351741469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84757446653686364468988625 63568084990264773351741469)
          ·
            refine ⟨23838031871349290006903051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63568084990264773351741469 23838031871349290006903051)
            ·
              refine ⟨35757047807023935010354577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23838031871349290006903051 35757047807023935010354577)
              ·
                refine ⟨26817785855267951257765933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35757047807023935010354577 26817785855267951257765933)
                ·
                  refine ⟨10056669695725481721662225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26817785855267951257765933 10056669695725481721662225)
                  ·
                    refine ⟨7542502271794111291246669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10056669695725481721662225 7542502271794111291246669)
                    ·
                      refine ⟨2828438351922791734217501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542502271794111291246669 2828438351922791734217501)
                      ·
                        rfl

theorem cell23_5508364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_5508364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508364 prefixEnd_5508364 := by exact prefixLift 5508364
  have htrace : WordTrace (prefixWord ++ tailWord_5508364) baseStart_5508364 baseEnd_5508364 := by
    simpa [prefixWord, tailWord_5508364, baseEnd_5508364] using wordTrace_append hprefix tailTrace_5508364
  have hstable : (prefixWord ++ tailWord_5508364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508364).length < 2 ^ (prefixWord ++ tailWord_5508364).sum := by decide
  have hdescent : baseEnd_5508364 < baseStart_5508364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508378 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_5508378 : Nat := 118140960795 + 5508378 * 2 ^ 59
def prefixEnd_5508378 : Nat := 4983230072969 + 3 ^ 40 * 5508378 * 2
def baseEnd_5508378 : Nat := 2828445540651954679442437

theorem tailTrace_5508378 : CollatzResearch.WordTrace tailWord_5508378 prefixEnd_5508378 2828445540651954679442437 := by
  unfold tailWord_5508378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50226762709523684227523447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133938033892063157940062525 50226762709523684227523447)
  ·
    refine ⟨75340144064285526341285171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50226762709523684227523447 75340144064285526341285171)
    ·
      refine ⟨113010216096428289511927757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75340144064285526341285171 113010216096428289511927757)
      ·
        refine ⟨42378831036160608566972909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113010216096428289511927757 42378831036160608566972909)
        ·
          refine ⟨15892061638560228212614841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42378831036160608566972909 15892061638560228212614841)
          ·
            refine ⟨11919046228920171159461131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15892061638560228212614841 11919046228920171159461131)
            ·
              refine ⟨17878569343380256739191697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11919046228920171159461131 17878569343380256739191697)
              ·
                refine ⟨13408927007535192554393773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17878569343380256739191697 13408927007535192554393773)
                ·
                  refine ⟨5028347627825697207897665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13408927007535192554393773 5028347627825697207897665)
                  ·
                    refine ⟨3771260720869272905923249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028347627825697207897665 3771260720869272905923249)
                    ·
                      refine ⟨2828445540651954679442437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771260720869272905923249 2828445540651954679442437)
                      ·
                        rfl

theorem cell23_5508378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_5508378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508378 prefixEnd_5508378 := by exact prefixLift 5508378
  have htrace : WordTrace (prefixWord ++ tailWord_5508378) baseStart_5508378 baseEnd_5508378 := by
    simpa [prefixWord, tailWord_5508378, baseEnd_5508378] using wordTrace_append hprefix tailTrace_5508378
  have hstable : (prefixWord ++ tailWord_5508378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508378).length < 2 ^ (prefixWord ++ tailWord_5508378).sum := by decide
  have hdescent : baseEnd_5508378 < baseStart_5508378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508381 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5508381 : Nat := 118140960795 + 5508381 * 2 ^ 59
def prefixEnd_5508381 : Nat := 4983230072969 + 3 ^ 40 * 5508381 * 2
def baseEnd_5508381 : Nat := 2828447081093918167704923

theorem tailTrace_5508381 : CollatzResearch.WordTrace tailWord_5508381 prefixEnd_5508381 2828447081093918167704923 := by
  unfold tailWord_5508381
  simp only [CollatzResearch.WordTrace]
  refine ⟨200907160257083868422452997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133938106838055912281635331 200907160257083868422452997)
  ·
    refine ⟨37670092548203225329209937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200907160257083868422452997 37670092548203225329209937)
    ·
      refine ⟨28252569411152418996907453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37670092548203225329209937 28252569411152418996907453)
      ·
        refine ⟨10594713529182157123840295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28252569411152418996907453 10594713529182157123840295)
        ·
          refine ⟨15892070293773235685760443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594713529182157123840295 15892070293773235685760443)
          ·
            refine ⟨23838105440659853528640665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15892070293773235685760443 23838105440659853528640665)
            ·
              refine ⟨17878579080494890146480499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23838105440659853528640665 17878579080494890146480499)
              ·
                refine ⟨26817868620742335219720749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17878579080494890146480499 26817868620742335219720749)
                ·
                  refine ⟨10056700732778375707395281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26817868620742335219720749 10056700732778375707395281)
                  ·
                    refine ⟨7542525549583781780546461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10056700732778375707395281 7542525549583781780546461)
                    ·
                      refine ⟨2828447081093918167704923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542525549583781780546461 2828447081093918167704923)
                      ·
                        rfl

theorem cell23_5508381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5508381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508381 prefixEnd_5508381 := by exact prefixLift 5508381
  have htrace : WordTrace (prefixWord ++ tailWord_5508381) baseStart_5508381 baseEnd_5508381 := by
    simpa [prefixWord, tailWord_5508381, baseEnd_5508381] using wordTrace_append hprefix tailTrace_5508381
  have hstable : (prefixWord ++ tailWord_5508381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508381).length < 2 ^ (prefixWord ++ tailWord_5508381).sum := by decide
  have hdescent : baseEnd_5508381 < baseStart_5508381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508382 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5508382 : Nat := 118140960795 + 5508382 * 2 ^ 59
def prefixEnd_5508382 : Nat := 4983230072969 + 3 ^ 40 * 5508382 * 2
def baseEnd_5508382 : Nat := 2828447594574572663792419

theorem tailTrace_5508382 : CollatzResearch.WordTrace tailWord_5508382 prefixEnd_5508382 2828447594574572663792419 := by
  unfold tailWord_5508382
  simp only [CollatzResearch.WordTrace]
  refine ⟨25113399591260030699154925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133938131153386830395492933 25113399591260030699154925)
  ·
    refine ⟨9417524846722511512183097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25113399591260030699154925 9417524846722511512183097)
    ·
      refine ⟨7063143635041883634137323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9417524846722511512183097 7063143635041883634137323)
      ·
        refine ⟨10594715452562825451205985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063143635041883634137323 10594715452562825451205985)
        ·
          refine ⟨7946036589422119088404489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10594715452562825451205985 7946036589422119088404489)
          ·
            refine ⟨5959527442066589316303367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7946036589422119088404489 5959527442066589316303367)
            ·
              refine ⟨8939291163099883974455051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959527442066589316303367 8939291163099883974455051)
              ·
                refine ⟨13408936744649825961682577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8939291163099883974455051 13408936744649825961682577)
                ·
                  refine ⟨10056702558487369471261933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13408936744649825961682577 10056702558487369471261933)
                  ·
                    refine ⟨3771263459432763551723225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10056702558487369471261933 3771263459432763551723225)
                    ·
                      refine ⟨2828447594574572663792419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771263459432763551723225 2828447594574572663792419)
                      ·
                        rfl

theorem cell23_5508382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5508382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508382 prefixEnd_5508382 := by exact prefixLift 5508382
  have htrace : WordTrace (prefixWord ++ tailWord_5508382) baseStart_5508382 baseEnd_5508382 := by
    simpa [prefixWord, tailWord_5508382, baseEnd_5508382] using wordTrace_append hprefix tailTrace_5508382
  have hstable : (prefixWord ++ tailWord_5508382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508382).length < 2 ^ (prefixWord ++ tailWord_5508382).sum := by decide
  have hdescent : baseEnd_5508382 < baseStart_5508382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508422 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_5508422 : Nat := 118140960795 + 5508422 * 2 ^ 59
def prefixEnd_5508422 : Nat := 4983230072969 + 3 ^ 40 * 5508422 * 2
def baseEnd_5508422 : Nat := 942822711266917502430745

theorem tailTrace_5508422 : CollatzResearch.WordTrace tailWord_5508422 prefixEnd_5508422 942822711266917502430745 := by
  unfold tailWord_5508422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278395489060479138271735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133939103766623554949797013 6278395489060479138271735)
  ·
    refine ⟨9417593233590718707407603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278395489060479138271735 9417593233590718707407603)
    ·
      refine ⟨14126389850386078061111405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9417593233590718707407603 14126389850386078061111405)
      ·
        refine ⟨5297396193894779272916777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14126389850386078061111405 5297396193894779272916777)
        ·
          refine ⟨3973047145421084454687583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297396193894779272916777 3973047145421084454687583)
          ·
            refine ⟨5959570718131626682031375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973047145421084454687583 5959570718131626682031375)
            ·
              refine ⟨8939356077197440023047063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959570718131626682031375 8939356077197440023047063)
              ·
                refine ⟨13409034115796160034570595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8939356077197440023047063 13409034115796160034570595)
                ·
                  refine ⟨20113551173694240051855893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13409034115796160034570595 20113551173694240051855893)
                  ·
                    refine ⟨942822711266917502430745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20113551173694240051855893 942822711266917502430745)
                    ·
                      rfl

theorem cell23_5508422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_5508422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508422 prefixEnd_5508422 := by exact prefixLift 5508422
  have htrace : WordTrace (prefixWord ++ tailWord_5508422) baseStart_5508422 baseEnd_5508422 := by
    simpa [prefixWord, tailWord_5508422, baseEnd_5508422] using wordTrace_append hprefix tailTrace_5508422
  have hstable : (prefixWord ++ tailWord_5508422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508422).length < 2 ^ (prefixWord ++ tailWord_5508422).sum := by decide
  have hdescent : baseEnd_5508422 < baseStart_5508422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508485 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_5508485 : Nat := 118140960795 + 5508485 * 2 ^ 59
def prefixEnd_5508485 : Nat := 4983230072969 + 3 ^ 40 * 5508485 * 2
def baseEnd_5508485 : Nat := 2828500483081985760804445

theorem tailTrace_5508485 : CollatzResearch.WordTrace tailWord_5508485 prefixEnd_5508485 2828500483081985760804445 := by
  unfold tailWord_5508485
  simp only [CollatzResearch.WordTrace]
  refine ⟨200910953448707094184238909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133940635632471396122825939 200910953448707094184238909)
  ·
    refine ⟨75341607543265160319089591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200910953448707094184238909 75341607543265160319089591)
    ·
      refine ⟨113012411314897740478634387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75341607543265160319089591 113012411314897740478634387)
      ·
        refine ⟨169518616972346610717951581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113012411314897740478634387 169518616972346610717951581)
        ·
          refine ⟨63569481364629979019231843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169518616972346610717951581 63569481364629979019231843)
          ·
            refine ⟨95354222046944968528847765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63569481364629979019231843 95354222046944968528847765)
            ·
              refine ⟨4469729158450545399789739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95354222046944968528847765 4469729158450545399789739)
              ·
                refine ⟨6704593737675818099684609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4469729158450545399789739 6704593737675818099684609)
                ·
                  refine ⟨5028445303256863574763457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6704593737675818099684609 5028445303256863574763457)
                  ·
                    refine ⟨3771333977442647681072593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028445303256863574763457 3771333977442647681072593)
                    ·
                      refine ⟨2828500483081985760804445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771333977442647681072593 2828500483081985760804445)
                      ·
                        rfl

theorem cell23_5508485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_5508485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508485 prefixEnd_5508485 := by exact prefixLift 5508485
  have htrace : WordTrace (prefixWord ++ tailWord_5508485) baseStart_5508485 baseEnd_5508485 := by
    simpa [prefixWord, tailWord_5508485, baseEnd_5508485] using wordTrace_append hprefix tailTrace_5508485
  have hstable : (prefixWord ++ tailWord_5508485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508485).length < 2 ^ (prefixWord ++ tailWord_5508485).sum := by decide
  have hdescent : baseEnd_5508485 < baseStart_5508485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508507 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_5508507 : Nat := 118140960795 + 5508507 * 2 ^ 59
def prefixEnd_5508507 : Nat := 4983230072969 + 3 ^ 40 * 5508507 * 2
def baseEnd_5508507 : Nat := 2828511779656384674729343

theorem tailTrace_5508507 : CollatzResearch.WordTrace tailWord_5508507 prefixEnd_5508507 2828511779656384674729343 := by
  unfold tailWord_5508507
  simp only [CollatzResearch.WordTrace]
  refine ⟨200911755854627391941539775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133941170569751594627693183 200911755854627391941539775)
  ·
    refine ⟨301367633781941087912309663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200911755854627391941539775 301367633781941087912309663)
    ·
      refine ⟨452051450672911631868464495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301367633781941087912309663 452051450672911631868464495)
      ·
        refine ⟨678077176009367447802696743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452051450672911631868464495 678077176009367447802696743)
        ·
          refine ⟨1017115764014051171704045115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678077176009367447802696743 1017115764014051171704045115)
          ·
            refine ⟨1525673646021076757556067673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017115764014051171704045115 1525673646021076757556067673)
            ·
              refine ⟨1144255234515807568167050755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525673646021076757556067673 1144255234515807568167050755)
              ·
                refine ⟨1716382851773711352250576133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144255234515807568167050755 1716382851773711352250576133)
                ·
                  refine ⟨321821784707570878546983025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716382851773711352250576133 321821784707570878546983025)
                  ·
                    refine ⟨241366338530678158910237269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321821784707570878546983025 241366338530678158910237269)
                    ·
                      refine ⟨2828511779656384674729343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241366338530678158910237269 2828511779656384674729343)
                      ·
                        rfl

theorem cell23_5508507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_5508507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508507 prefixEnd_5508507 := by exact prefixLift 5508507
  have htrace : WordTrace (prefixWord ++ tailWord_5508507) baseStart_5508507 baseEnd_5508507 := by
    simpa [prefixWord, tailWord_5508507, baseEnd_5508507] using wordTrace_append hprefix tailTrace_5508507
  have hstable : (prefixWord ++ tailWord_5508507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508507).length < 2 ^ (prefixWord ++ tailWord_5508507).sum := by decide
  have hdescent : baseEnd_5508507 < baseStart_5508507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508525 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 5]
def baseStart_5508525 : Nat := 118140960795 + 5508525 * 2 ^ 59
def prefixEnd_5508525 : Nat := 4983230072969 + 3 ^ 40 * 5508525 * 2
def baseEnd_5508525 : Nat := 314280113589796178256029

theorem tailTrace_5508525 : CollatzResearch.WordTrace tailWord_5508525 prefixEnd_5508525 314280113589796178256029 := by
  unfold tailWord_5508525
  simp only [CollatzResearch.WordTrace]
  refine ⟨200912412368562181015695029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133941608245708120677130019 200912412368562181015695029)
  ·
    refine ⟨18835538659552704470221409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200912412368562181015695029 18835538659552704470221409)
    ·
      refine ⟨14126653994664528352666057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18835538659552704470221409 14126653994664528352666057)
      ·
        refine ⟨10594990495998396264499543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14126653994664528352666057 10594990495998396264499543)
        ·
          refine ⟨15892485743997594396749315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594990495998396264499543 15892485743997594396749315)
          ·
            refine ⟨23838728615996391595123973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15892485743997594396749315 23838728615996391595123973)
            ·
              refine ⟨4469761615499323424085745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23838728615996391595123973 4469761615499323424085745)
              ·
                refine ⟨3352321211624492568064309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469761615499323424085745 3352321211624492568064309)
                ·
                  refine ⟨314280113589796178256029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3352321211624492568064309 314280113589796178256029)
                  ·
                    rfl

theorem cell23_5508525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_5508525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508525 prefixEnd_5508525 := by exact prefixLift 5508525
  have htrace : WordTrace (prefixWord ++ tailWord_5508525) baseStart_5508525 baseEnd_5508525 := by
    simpa [prefixWord, tailWord_5508525, baseEnd_5508525] using wordTrace_append hprefix tailTrace_5508525
  have hstable : (prefixWord ++ tailWord_5508525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508525).length < 2 ^ (prefixWord ++ tailWord_5508525).sum := by decide
  have hdescent : baseEnd_5508525 < baseStart_5508525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508551 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 3, 4]
def baseStart_5508551 : Nat := 118140960795 + 5508551 * 2 ^ 59
def prefixEnd_5508551 : Nat := 4983230072969 + 3 ^ 40 * 5508551 * 2
def baseEnd_5508551 : Nat := 942844790935060834193047

theorem tailTrace_5508551 : CollatzResearch.WordTrace tailWord_5508551 prefixEnd_5508551 942844790935060834193047 := by
  unfold tailWord_5508551
  simp only [CollatzResearch.WordTrace]
  refine ⟨200913360666467987456141507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133942240444311991637427671 200913360666467987456141507)
  ·
    refine ⟨301370040999701981184212261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200913360666467987456141507 301370040999701981184212261)
    ·
      refine ⟨56506882687444121472039799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301370040999701981184212261 56506882687444121472039799)
      ·
        refine ⟨84760324031166182208059699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56506882687444121472039799 84760324031166182208059699)
        ·
          refine ⟨127140486046749273312089549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84760324031166182208059699 127140486046749273312089549)
          ·
            refine ⟨47677682267530977492033581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127140486046749273312089549 47677682267530977492033581)
            ·
              refine ⟨17879130850324116559512593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47677682267530977492033581 17879130850324116559512593)
              ·
                refine ⟨13409348137743087419634445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17879130850324116559512593 13409348137743087419634445)
                ·
                  refine ⟨5028505551653657782362917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13409348137743087419634445 5028505551653657782362917)
                  ·
                    refine ⟨942844790935060834193047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028505551653657782362917 942844790935060834193047)
                    ·
                      rfl

theorem cell23_5508551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_5508551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508551 prefixEnd_5508551 := by exact prefixLift 5508551
  have htrace : WordTrace (prefixWord ++ tailWord_5508551) baseStart_5508551 baseEnd_5508551 := by
    simpa [prefixWord, tailWord_5508551, baseEnd_5508551] using wordTrace_append hprefix tailTrace_5508551
  have hstable : (prefixWord ++ tailWord_5508551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508551).length < 2 ^ (prefixWord ++ tailWord_5508551).sum := by decide
  have hdescent : baseEnd_5508551 < baseStart_5508551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508568 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 1, 4]
def baseStart_5508568 : Nat := 118140960795 + 5508568 * 2 ^ 59
def prefixEnd_5508568 : Nat := 4983230072969 + 3 ^ 40 * 5508568 * 2
def baseEnd_5508568 : Nat := 942847700658769645355521

theorem tailTrace_5508568 : CollatzResearch.WordTrace tailWord_5508568 prefixEnd_5508568 942847700658769645355521 := by
  unfold tailWord_5508568
  simp only [CollatzResearch.WordTrace]
  refine ⟨100456990353703199679755179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133942653804937599573006905 100456990353703199679755179)
  ·
    refine ⟨150685485530554799519632769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100456990353703199679755179 150685485530554799519632769)
    ·
      refine ⟨113014114147916099639724577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150685485530554799519632769 113014114147916099639724577)
      ·
        refine ⟨84760585610937074729793433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113014114147916099639724577 84760585610937074729793433)
        ·
          refine ⟨63570439208202806047345075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84760585610937074729793433 63570439208202806047345075)
          ·
            refine ⟨95355658812304209071017613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63570439208202806047345075 95355658812304209071017613)
            ·
              refine ⟨35758372054614078401631605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95355658812304209071017613 35758372054614078401631605)
              ·
                refine ⟨3352347380120069850152963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35758372054614078401631605 3352347380120069850152963)
                ·
                  refine ⟨5028521070180104775229445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352347380120069850152963 5028521070180104775229445)
                  ·
                    refine ⟨942847700658769645355521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028521070180104775229445 942847700658769645355521)
                    ·
                      rfl

theorem cell23_5508568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_5508568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508568 prefixEnd_5508568 := by exact prefixLift 5508568
  have htrace : WordTrace (prefixWord ++ tailWord_5508568) baseStart_5508568 baseEnd_5508568 := by
    simpa [prefixWord, tailWord_5508568, baseEnd_5508568] using wordTrace_append hprefix tailTrace_5508568
  have hstable : (prefixWord ++ tailWord_5508568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508568).length < 2 ^ (prefixWord ++ tailWord_5508568).sum := by decide
  have hdescent : baseEnd_5508568 < baseStart_5508568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508581 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 8]
def baseStart_5508581 : Nat := 118140960795 + 5508581 * 2 ^ 59
def prefixEnd_5508581 : Nat := 4983230072969 + 3 ^ 40 * 5508581 * 2
def baseEnd_5508581 : Nat := 314283308580535265022667

theorem tailTrace_5508581 : CollatzResearch.WordTrace tailWord_5508581 prefixEnd_5508581 314283308580535265022667 := by
  unfold tailWord_5508581
  simp only [CollatzResearch.WordTrace]
  refine ⟨200914454856359302579733597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133942969904239535053155731 200914454856359302579733597)
  ·
    refine ⟨75342920571134738467400099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200914454856359302579733597 75342920571134738467400099)
    ·
      refine ⟨113014380856702107701100149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75342920571134738467400099 113014380856702107701100149)
      ·
        refine ⟨10595098205315822596978139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113014380856702107701100149 10595098205315822596978139)
        ·
          refine ⟨15892647307973733895467209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10595098205315822596978139 15892647307973733895467209)
          ·
            refine ⟨11919485480980300421600407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15892647307973733895467209 11919485480980300421600407)
            ·
              refine ⟨17879228221470450632400611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11919485480980300421600407 17879228221470450632400611)
              ·
                refine ⟨26818842332205675948600917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17879228221470450632400611 26818842332205675948600917)
                ·
                  refine ⟨314283308580535265022667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26818842332205675948600917 314283308580535265022667)
                  ·
                    rfl

theorem cell23_5508581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_5508581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508581 prefixEnd_5508581 := by exact prefixLift 5508581
  have htrace : WordTrace (prefixWord ++ tailWord_5508581) baseStart_5508581 baseEnd_5508581 := by
    simpa [prefixWord, tailWord_5508581, baseEnd_5508581] using wordTrace_append hprefix tailTrace_5508581
  have hstable : (prefixWord ++ tailWord_5508581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508581).length < 2 ^ (prefixWord ++ tailWord_5508581).sum := by decide
  have hdescent : baseEnd_5508581 < baseStart_5508581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508584 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5508584 : Nat := 118140960795 + 5508584 * 2 ^ 59
def prefixEnd_5508584 : Nat := 4983230072969 + 3 ^ 40 * 5508584 * 2
def baseEnd_5508584 : Nat := 2828551317666780873466489

theorem tailTrace_5508584 : CollatzResearch.WordTrace tailWord_5508584 prefixEnd_5508584 2828551317666780873466489 := by
  unfold tailWord_5508584
  simp only [CollatzResearch.WordTrace]
  refine ⟨100457282137674217046046403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133943042850232289394728537 100457282137674217046046403)
  ·
    refine ⟨150685923206511325569069605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100457282137674217046046403 150685923206511325569069605)
    ·
      refine ⟨28253610601220873544200551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150685923206511325569069605 28253610601220873544200551)
      ·
        refine ⟨42380415901831310316300827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28253610601220873544200551 42380415901831310316300827)
        ·
          refine ⟨63570623852746965474451241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42380415901831310316300827 63570623852746965474451241)
          ·
            refine ⟨47677967889560224105838431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63570623852746965474451241 47677967889560224105838431)
            ·
              refine ⟨71516951834340336158757647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47677967889560224105838431 71516951834340336158757647)
              ·
                refine ⟨107275427751510504238136471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71516951834340336158757647 107275427751510504238136471)
                ·
                  refine ⟨160913141627265756357204707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107275427751510504238136471 160913141627265756357204707)
                  ·
                    refine ⟨241369712440898634535807061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160913141627265756357204707 241369712440898634535807061)
                    ·
                      refine ⟨2828551317666780873466489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241369712440898634535807061 2828551317666780873466489)
                      ·
                        rfl

theorem cell23_5508584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5508584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508584 prefixEnd_5508584 := by exact prefixLift 5508584
  have htrace : WordTrace (prefixWord ++ tailWord_5508584) baseStart_5508584 baseEnd_5508584 := by
    simpa [prefixWord, tailWord_5508584, baseEnd_5508584] using wordTrace_append hprefix tailTrace_5508584
  have hstable : (prefixWord ++ tailWord_5508584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508584).length < 2 ^ (prefixWord ++ tailWord_5508584).sum := by decide
  have hdescent : baseEnd_5508584 < baseStart_5508584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508604 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_5508604 : Nat := 118140960795 + 5508604 * 2 ^ 59
def prefixEnd_5508604 : Nat := 4983230072969 + 3 ^ 40 * 5508604 * 2
def baseEnd_5508604 : Nat := 2828561587279870795216397

theorem tailTrace_5508604 : CollatzResearch.WordTrace tailWord_5508604 prefixEnd_5508604 2828561587279870795216397 := by
  unfold tailWord_5508604
  simp only [CollatzResearch.WordTrace]
  refine ⟨100457646867637988753910433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133943529156850651671880577 100457646867637988753910433)
  ·
    refine ⟨75343235150728491565432825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100457646867637988753910433 75343235150728491565432825)
    ·
      refine ⟨56507426363046368674074619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75343235150728491565432825 56507426363046368674074619)
      ·
        refine ⟨84761139544569553011111929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56507426363046368674074619 84761139544569553011111929)
        ·
          refine ⟨63570854658427164758333947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84761139544569553011111929 63570854658427164758333947)
          ·
            refine ⟨95356281987640747137500921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63570854658427164758333947 95356281987640747137500921)
            ·
              refine ⟨71517211490730560353125691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95356281987640747137500921 71517211490730560353125691)
              ·
                refine ⟨107275817236095840529688537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71517211490730560353125691 107275817236095840529688537)
                ·
                  refine ⟨80456862927071880397266403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107275817236095840529688537 80456862927071880397266403)
                  ·
                    refine ⟨120685294390607820595899605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80456862927071880397266403 120685294390607820595899605)
                    ·
                      refine ⟨2828561587279870795216397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120685294390607820595899605 2828561587279870795216397)
                      ·
                        rfl

theorem cell23_5508604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_5508604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508604 prefixEnd_5508604 := by exact prefixLift 5508604
  have htrace : WordTrace (prefixWord ++ tailWord_5508604) baseStart_5508604 baseEnd_5508604 := by
    simpa [prefixWord, tailWord_5508604, baseEnd_5508604] using wordTrace_append hprefix tailTrace_5508604
  have hstable : (prefixWord ++ tailWord_5508604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508604).length < 2 ^ (prefixWord ++ tailWord_5508604).sum := by decide
  have hdescent : baseEnd_5508604 < baseStart_5508604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508618 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_5508618 : Nat := 118140960795 + 5508618 * 2 ^ 59
def prefixEnd_5508618 : Nat := 4983230072969 + 3 ^ 40 * 5508618 * 2
def baseEnd_5508618 : Nat := 2828568776009033740441333

theorem tailTrace_5508618 : CollatzResearch.WordTrace tailWord_5508618 prefixEnd_5508618 2828568776009033740441333 := by
  unfold tailWord_5508618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50228951089306314474707627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133943869571483505265887005 50228951089306314474707627)
  ·
    refine ⟨75343426633959471712061441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50228951089306314474707627 75343426633959471712061441)
    ·
      refine ⟨56507569975469603784046081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75343426633959471712061441 56507569975469603784046081)
      ·
        refine ⟨42380677481602202838034561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56507569975469603784046081 42380677481602202838034561)
        ·
          refine ⟨31785508111201652128525921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42380677481602202838034561 31785508111201652128525921)
          ·
            refine ⟨23839131083401239096394441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31785508111201652128525921 23839131083401239096394441)
            ·
              refine ⟨17879348312550929322295831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23839131083401239096394441 17879348312550929322295831)
              ·
                refine ⟨26819022468826393983443747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17879348312550929322295831 26819022468826393983443747)
                ·
                  refine ⟨40228533703239590975165621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26819022468826393983443747 40228533703239590975165621)
                  ·
                    refine ⟨3771425034678711653921777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40228533703239590975165621 3771425034678711653921777)
                    ·
                      refine ⟨2828568776009033740441333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771425034678711653921777 2828568776009033740441333)
                      ·
                        rfl

theorem cell23_5508618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_5508618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508618 prefixEnd_5508618 := by exact prefixLift 5508618
  have htrace : WordTrace (prefixWord ++ tailWord_5508618) baseStart_5508618 baseEnd_5508618 := by
    simpa [prefixWord, tailWord_5508618, baseEnd_5508618] using wordTrace_append hprefix tailTrace_5508618
  have hstable : (prefixWord ++ tailWord_5508618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508618).length < 2 ^ (prefixWord ++ tailWord_5508618).sum := by decide
  have hdescent : baseEnd_5508618 < baseStart_5508618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508661 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5508661 : Nat := 118140960795 + 5508661 * 2 ^ 59
def prefixEnd_5508661 : Nat := 4983230072969 + 3 ^ 40 * 5508661 * 2
def baseEnd_5508661 : Nat := 2828590855677177072203635

theorem tailTrace_5508661 : CollatzResearch.WordTrace tailWord_5508661 prefixEnd_5508661 2828590855677177072203635 := by
  unfold tailWord_5508661
  simp only [CollatzResearch.WordTrace]
  refine ⟨200917372696069476242645837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133944915130712984161763891 200917372696069476242645837)
  ·
    refine ⟨75344014761026053590992189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200917372696069476242645837 75344014761026053590992189)
    ·
      refine ⟨28254005535384770096622071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75344014761026053590992189 28254005535384770096622071)
      ·
        refine ⟨42381008303077155144933107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28254005535384770096622071 42381008303077155144933107)
        ·
          refine ⟨63571512454615732717399661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42381008303077155144933107 63571512454615732717399661)
          ·
            refine ⟨23839317170480899769024873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63571512454615732717399661 23839317170480899769024873)
            ·
              refine ⟨17879487877860674826768655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23839317170480899769024873 17879487877860674826768655)
              ·
                refine ⟨26819231816791012240152983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17879487877860674826768655 26819231816791012240152983)
                ·
                  refine ⟨40228847725186518360229475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26819231816791012240152983 40228847725186518360229475)
                  ·
                    refine ⟨60343271587779777540344213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40228847725186518360229475 60343271587779777540344213)
                    ·
                      refine ⟨2828590855677177072203635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60343271587779777540344213 2828590855677177072203635)
                      ·
                        rfl

theorem cell23_5508661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5508661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508661 prefixEnd_5508661 := by exact prefixLift 5508661
  have htrace : WordTrace (prefixWord ++ tailWord_5508661) baseStart_5508661 baseEnd_5508661 := by
    simpa [prefixWord, tailWord_5508661, baseEnd_5508661] using wordTrace_append hprefix tailTrace_5508661
  have hstable : (prefixWord ++ tailWord_5508661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508661).length < 2 ^ (prefixWord ++ tailWord_5508661).sum := by decide
  have hdescent : baseEnd_5508661 < baseStart_5508661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508662 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5508662 : Nat := 118140960795 + 5508662 * 2 ^ 59
def prefixEnd_5508662 : Nat := 4983230072969 + 3 ^ 40 * 5508662 * 2
def baseEnd_5508662 : Nat := 942863789719277189430377

theorem tailTrace_5508662 : CollatzResearch.WordTrace tailWord_5508662 prefixEnd_5508662 942863789719277189430377 := by
  unfold tailWord_5508662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12557338073066615838339515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133944939446043902275621493 12557338073066615838339515)
  ·
    refine ⟨18836007109599923757509273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12557338073066615838339515 18836007109599923757509273)
    ·
      refine ⟨14127005332199942818131955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18836007109599923757509273 14127005332199942818131955)
      ·
        refine ⟨21190507998299914227197933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14127005332199942818131955 21190507998299914227197933)
        ·
          refine ⟨7946440499362467835199225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21190507998299914227197933 7946440499362467835199225)
          ·
            refine ⟨5959830374521850876399419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7946440499362467835199225 5959830374521850876399419)
            ·
              refine ⟨8939745561782776314599129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959830374521850876399419 8939745561782776314599129)
              ·
                refine ⟨6704809171337082235949347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8939745561782776314599129 6704809171337082235949347)
                ·
                  refine ⟨10057213757005623353924021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704809171337082235949347 10057213757005623353924021)
                  ·
                    refine ⟨942863789719277189430377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10057213757005623353924021 942863789719277189430377)
                    ·
                      rfl

theorem cell23_5508662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5508662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508662 prefixEnd_5508662 := by exact prefixLift 5508662
  have htrace : WordTrace (prefixWord ++ tailWord_5508662) baseStart_5508662 baseEnd_5508662 := by
    simpa [prefixWord, tailWord_5508662, baseEnd_5508662] using wordTrace_append hprefix tailTrace_5508662
  have hstable : (prefixWord ++ tailWord_5508662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508662).length < 2 ^ (prefixWord ++ tailWord_5508662).sum := by decide
  have hdescent : baseEnd_5508662 < baseStart_5508662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508665 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5508665 : Nat := 118140960795 + 5508665 * 2 ^ 59
def prefixEnd_5508665 : Nat := 4983230072969 + 3 ^ 40 * 5508665 * 2
def baseEnd_5508665 : Nat := 2828592909599795056553617

theorem tailTrace_5508665 : CollatzResearch.WordTrace tailWord_5508665 prefixEnd_5508665 2828592909599795056553617 := by
  unfold tailWord_5508665
  simp only [CollatzResearch.WordTrace]
  refine ⟨200917518588054984925791449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133945012392036656617194299 200917518588054984925791449)
  ·
    refine ⟨150688138941041238694343587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200917518588054984925791449 150688138941041238694343587)
    ·
      refine ⟨226032208411561858041515381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150688138941041238694343587 226032208411561858041515381)
      ·
        refine ⟨21190519538583924191392067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226032208411561858041515381 21190519538583924191392067)
        ·
          refine ⟨31785779307875886287088101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21190519538583924191392067 31785779307875886287088101)
          ·
            refine ⟨5959833620226728678829019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31785779307875886287088101 5959833620226728678829019)
            ·
              refine ⟨8939750430340093018243529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959833620226728678829019 8939750430340093018243529)
              ·
                refine ⟨6704812822755069763682647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8939750430340093018243529 6704812822755069763682647)
                ·
                  refine ⟨10057219234132604645523971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6704812822755069763682647 10057219234132604645523971)
                  ·
                    refine ⟨15085828851198906968285957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10057219234132604645523971 15085828851198906968285957)
                    ·
                      refine ⟨2828592909599795056553617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15085828851198906968285957 2828592909599795056553617)
                      ·
                        rfl

theorem cell23_5508665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5508665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508665 prefixEnd_5508665 := by exact prefixLift 5508665
  have htrace : WordTrace (prefixWord ++ tailWord_5508665) baseStart_5508665 baseEnd_5508665 := by
    simpa [prefixWord, tailWord_5508665, baseEnd_5508665] using wordTrace_append hprefix tailTrace_5508665
  have hstable : (prefixWord ++ tailWord_5508665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508665).length < 2 ^ (prefixWord ++ tailWord_5508665).sum := by decide
  have hdescent : baseEnd_5508665 < baseStart_5508665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508682 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_5508682 : Nat := 118140960795 + 5508682 * 2 ^ 59
def prefixEnd_5508682 : Nat := 4983230072969 + 3 ^ 40 * 5508682 * 2
def baseEnd_5508682 : Nat := 2828601638770921490041039

theorem tailTrace_5508682 : CollatzResearch.WordTrace tailWord_5508682 prefixEnd_5508682 2828601638770921490041039 := by
  unfold tailWord_5508682
  simp only [CollatzResearch.WordTrace]
  refine ⟨50229534657248349207290075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133945425752662264552773533 50229534657248349207290075)
  ·
    refine ⟨75344301985872523810935113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50229534657248349207290075 75344301985872523810935113)
    ·
      refine ⟨56508226489404392858201335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75344301985872523810935113 56508226489404392858201335)
      ·
        refine ⟨84762339734106589287302003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56508226489404392858201335 84762339734106589287302003)
        ·
          refine ⟨127143509601159883930953005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84762339734106589287302003 127143509601159883930953005)
          ·
            refine ⟨47678816100434956474107377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127143509601159883930953005 47678816100434956474107377)
            ·
              refine ⟨35759112075326217355580533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47678816100434956474107377 35759112075326217355580533)
              ·
                refine ⟨3352416757061832877085675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35759112075326217355580533 3352416757061832877085675)
                ·
                  refine ⟨5028625135592749315628513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352416757061832877085675 5028625135592749315628513)
                  ·
                    refine ⟨3771468851694561986721385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028625135592749315628513 3771468851694561986721385)
                    ·
                      refine ⟨2828601638770921490041039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771468851694561986721385 2828601638770921490041039)
                      ·
                        rfl

theorem cell23_5508682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_5508682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508682 prefixEnd_5508682 := by exact prefixLift 5508682
  have htrace : WordTrace (prefixWord ++ tailWord_5508682) baseStart_5508682 baseEnd_5508682 := by
    simpa [prefixWord, tailWord_5508682, baseEnd_5508682] using wordTrace_append hprefix tailTrace_5508682
  have hstable : (prefixWord ++ tailWord_5508682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508682).length < 2 ^ (prefixWord ++ tailWord_5508682).sum := by decide
  have hdescent : baseEnd_5508682 < baseStart_5508682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508698 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_5508698 : Nat := 118140960795 + 5508698 * 2 ^ 59
def prefixEnd_5508698 : Nat := 4983230072969 + 3 ^ 40 * 5508698 * 2
def baseEnd_5508698 : Nat := 2828609854461393427440965

theorem tailTrace_5508698 : CollatzResearch.WordTrace tailWord_5508698 prefixEnd_5508698 2828609854461393427440965 := by
  unfold tailWord_5508698
  simp only [CollatzResearch.WordTrace]
  refine ⟨50229680549233857890435687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133945814797956954374495165 50229680549233857890435687)
  ·
    refine ⟨75344520823850786835653531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50229680549233857890435687 75344520823850786835653531)
    ·
      refine ⟨113016781235776180253480297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75344520823850786835653531 113016781235776180253480297)
      ·
        refine ⟨84762585926832135190110223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113016781235776180253480297 84762585926832135190110223)
        ·
          refine ⟨127143878890248202785165335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84762585926832135190110223 127143878890248202785165335)
          ·
            refine ⟨190715818335372304177748003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127143878890248202785165335 190715818335372304177748003)
            ·
              refine ⟨286073727503058456266622005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190715818335372304177748003 286073727503058456266622005)
              ·
                refine ⟨26819411953411730274995813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286073727503058456266622005 26819411953411730274995813)
                ·
                  refine ⟨5028639741264699426561715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26819411953411730274995813 5028639741264699426561715)
                  ·
                    refine ⟨7542959611897049139842573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028639741264699426561715 7542959611897049139842573)
                    ·
                      refine ⟨2828609854461393427440965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7542959611897049139842573 2828609854461393427440965)
                      ·
                        rfl

theorem cell23_5508698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_5508698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508698 prefixEnd_5508698 := by exact prefixLift 5508698
  have htrace : WordTrace (prefixWord ++ tailWord_5508698) baseStart_5508698 baseEnd_5508698 := by
    simpa [prefixWord, tailWord_5508698, baseEnd_5508698] using wordTrace_append hprefix tailTrace_5508698
  have hstable : (prefixWord ++ tailWord_5508698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508698).length < 2 ^ (prefixWord ++ tailWord_5508698).sum := by decide
  have hdescent : baseEnd_5508698 < baseStart_5508698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508741 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_5508741 : Nat := 118140960795 + 5508741 * 2 ^ 59
def prefixEnd_5508741 : Nat := 4983230072969 + 3 ^ 40 * 5508741 * 2
def baseEnd_5508741 : Nat := 2828631934129536759203267

theorem tailTrace_5508741 : CollatzResearch.WordTrace tailWord_5508741 prefixEnd_5508741 2828631934129536759203267 := by
  unfold tailWord_5508741
  simp only [CollatzResearch.WordTrace]
  refine ⟨200920290535779649905558077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133946860357186433270372051 200920290535779649905558077)
  ·
    refine ⟨75345108950917368714584279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200920290535779649905558077 75345108950917368714584279)
    ·
      refine ⟨113017663426376053071876419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75345108950917368714584279 113017663426376053071876419)
      ·
        refine ⟨169526495139564079607814629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113017663426376053071876419 169526495139564079607814629)
        ·
          refine ⟨31786217838668264926465243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169526495139564079607814629 31786217838668264926465243)
          ·
            refine ⟨47679326758002397389697865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31786217838668264926465243 47679326758002397389697865)
            ·
              refine ⟨35759495068501798042273399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47679326758002397389697865 35759495068501798042273399)
              ·
                refine ⟨53639242602752697063410099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35759495068501798042273399 53639242602752697063410099)
                ·
                  refine ⟨80458863904129045595115149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53639242602752697063410099 80458863904129045595115149)
                  ·
                    refine ⟨30172073964048392098168181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80458863904129045595115149 30172073964048392098168181)
                    ·
                      refine ⟨2828631934129536759203267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30172073964048392098168181 2828631934129536759203267)
                      ·
                        rfl

theorem cell23_5508741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_5508741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508741 prefixEnd_5508741 := by exact prefixLift 5508741
  have htrace : WordTrace (prefixWord ++ tailWord_5508741) baseStart_5508741 baseEnd_5508741 := by
    simpa [prefixWord, tailWord_5508741, baseEnd_5508741] using wordTrace_append hprefix tailTrace_5508741
  have hstable : (prefixWord ++ tailWord_5508741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508741).length < 2 ^ (prefixWord ++ tailWord_5508741).sum := by decide
  have hdescent : baseEnd_5508741 < baseStart_5508741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508768 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5508768 : Nat := 118140960795 + 5508768 * 2 ^ 59
def prefixEnd_5508768 : Nat := 4983230072969 + 3 ^ 40 * 5508768 * 2
def baseEnd_5508768 : Nat := 2828645798107208153565643

theorem tailTrace_5508768 : CollatzResearch.WordTrace tailWord_5508768 prefixEnd_5508768 2828645798107208153565643 := by
  unfold tailWord_5508768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100460637653340916758395479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133947516871121222344527305 100460637653340916758395479)
  ·
    refine ⟨150690956480011375137593219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100460637653340916758395479 150690956480011375137593219)
    ·
      refine ⟨226036434720017062706389829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150690956480011375137593219 226036434720017062706389829)
      ·
        refine ⟨42381831510003199257448093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226036434720017062706389829 42381831510003199257448093)
        ·
          refine ⟨15893186816251199721543035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42381831510003199257448093 15893186816251199721543035)
          ·
            refine ⟨23839780224376799582314553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893186816251199721543035 23839780224376799582314553)
            ·
              refine ⟨17879835168282599686735915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23839780224376799582314553 17879835168282599686735915)
              ·
                refine ⟨26819752752423899530103873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17879835168282599686735915 26819752752423899530103873)
                ·
                  refine ⟨20114814564317924647577905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26819752752423899530103873 20114814564317924647577905)
                  ·
                    refine ⟨15086110923238443485683429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20114814564317924647577905 15086110923238443485683429)
                    ·
                      refine ⟨2828645798107208153565643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15086110923238443485683429 2828645798107208153565643)
                      ·
                        rfl

theorem cell23_5508768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5508768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508768 prefixEnd_5508768 := by exact prefixLift 5508768
  have htrace : WordTrace (prefixWord ++ tailWord_5508768) baseStart_5508768 baseEnd_5508768 := by
    simpa [prefixWord, tailWord_5508768, baseEnd_5508768] using wordTrace_append hprefix tailTrace_5508768
  have hstable : (prefixWord ++ tailWord_5508768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508768).length < 2 ^ (prefixWord ++ tailWord_5508768).sum := by decide
  have hdescent : baseEnd_5508768 < baseStart_5508768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508772 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_5508772 : Nat := 118140960795 + 5508772 * 2 ^ 59
def prefixEnd_5508772 : Nat := 4983230072969 + 3 ^ 40 * 5508772 * 2
def baseEnd_5508772 : Nat := 2828647852029826137915625

theorem tailTrace_5508772 : CollatzResearch.WordTrace tailWord_5508772 prefixEnd_5508772 2828647852029826137915625 := by
  unfold tailWord_5508772
  simp only [CollatzResearch.WordTrace]
  refine ⟨100460710599333671099968285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133947614132444894799957713 100460710599333671099968285)
  ·
    refine ⟨37672766474750126662488107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100460710599333671099968285 37672766474750126662488107)
    ·
      refine ⟨56509149712125189993732161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37672766474750126662488107 56509149712125189993732161)
      ·
        refine ⟨42381862284093892495299121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56509149712125189993732161 42381862284093892495299121)
        ·
          refine ⟨31786396713070419371474341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42381862284093892495299121 31786396713070419371474341)
          ·
            refine ⟨5959949383700703632151439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31786396713070419371474341 5959949383700703632151439)
            ·
              refine ⟨8939924075551055448227159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959949383700703632151439 8939924075551055448227159)
              ·
                refine ⟨13409886113326583172340739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8939924075551055448227159 13409886113326583172340739)
                ·
                  refine ⟨20114829169989874758511109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13409886113326583172340739 20114829169989874758511109)
                  ·
                    refine ⟨3771530469373101517220833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20114829169989874758511109 3771530469373101517220833)
                    ·
                      refine ⟨2828647852029826137915625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771530469373101517220833 2828647852029826137915625)
                      ·
                        rfl

theorem cell23_5508772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_5508772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508772 prefixEnd_5508772 := by exact prefixLift 5508772
  have htrace : WordTrace (prefixWord ++ tailWord_5508772) baseStart_5508772 baseEnd_5508772 := by
    simpa [prefixWord, tailWord_5508772, baseEnd_5508772] using wordTrace_append hprefix tailTrace_5508772
  have hstable : (prefixWord ++ tailWord_5508772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508772).length < 2 ^ (prefixWord ++ tailWord_5508772).sum := by decide
  have hdescent : baseEnd_5508772 < baseStart_5508772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508806 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5508806 : Nat := 118140960795 + 5508806 * 2 ^ 59
def prefixEnd_5508806 : Nat := 4983230072969 + 3 ^ 40 * 5508806 * 2
def baseEnd_5508806 : Nat := 2828665310372079004890469

theorem tailTrace_5508806 : CollatzResearch.WordTrace tailWord_5508806 prefixEnd_5508806 2828665310372079004890469 := by
  unfold tailWord_5508806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278833165017005187708571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133948440853696110671116181 6278833165017005187708571)
  ·
    refine ⟨9418249747525507781562857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278833165017005187708571 9418249747525507781562857)
    ·
      refine ⟨7063687310644130836172143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9418249747525507781562857 7063687310644130836172143)
      ·
        refine ⟨10595530965966196254258215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063687310644130836172143 10595530965966196254258215)
        ·
          refine ⟨15893296448949294381387323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10595530965966196254258215 15893296448949294381387323)
          ·
            refine ⟨23839944673423941572080985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893296448949294381387323 23839944673423941572080985)
            ·
              refine ⟨17879958505067956179060739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23839944673423941572080985 17879958505067956179060739)
              ·
                refine ⟨26819937757601934268591109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17879958505067956179060739 26819937757601934268591109)
                ·
                  refine ⟨5028738329550362675360833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26819937757601934268591109 5028738329550362675360833)
                  ·
                    refine ⟨3771553747162772006520625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5028738329550362675360833 3771553747162772006520625)
                    ·
                      refine ⟨2828665310372079004890469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771553747162772006520625 2828665310372079004890469)
                      ·
                        rfl

theorem cell23_5508806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5508806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508806 prefixEnd_5508806 := by exact prefixLift 5508806
  have htrace : WordTrace (prefixWord ++ tailWord_5508806) baseStart_5508806 baseEnd_5508806 := by
    simpa [prefixWord, tailWord_5508806, baseEnd_5508806] using wordTrace_append hprefix tailTrace_5508806
  have hstable : (prefixWord ++ tailWord_5508806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508806).length < 2 ^ (prefixWord ++ tailWord_5508806).sum := by decide
  have hdescent : baseEnd_5508806 < baseStart_5508806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508808 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_5508808 : Nat := 118140960795 + 5508808 * 2 ^ 59
def prefixEnd_5508808 : Nat := 4983230072969 + 3 ^ 40 * 5508808 * 2
def baseEnd_5508808 : Nat := 942888779111129332355153

theorem tailTrace_5508808 : CollatzResearch.WordTrace tailWord_5508808 prefixEnd_5508808 942888779111129332355153 := by
  unfold tailWord_5508808
  simp only [CollatzResearch.WordTrace]
  refine ⟨100461367113268460174123539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133948489484357946898831385 100461367113268460174123539)
  ·
    refine ⟨150692050669902690261185309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100461367113268460174123539 150692050669902690261185309)
    ·
      refine ⟨56509519001213508847944491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150692050669902690261185309 56509519001213508847944491)
      ·
        refine ⟨84764278501820263271916737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56509519001213508847944491 84764278501820263271916737)
        ·
          refine ⟨63573208876365197453937553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84764278501820263271916737 63573208876365197453937553)
          ·
            refine ⟨47679906657273898090453165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63573208876365197453937553 47679906657273898090453165)
            ·
              refine ⟨17879964996477711783919937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47679906657273898090453165 17879964996477711783919937)
              ·
                refine ⟨13409973747358283837939953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17879964996477711783919937 13409973747358283837939953)
                ·
                  refine ⟨10057480310518712878454965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13409973747358283837939953 10057480310518712878454965)
                  ·
                    refine ⟨942888779111129332355153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10057480310518712878454965 942888779111129332355153)
                    ·
                      rfl

theorem cell23_5508808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_5508808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508808 prefixEnd_5508808 := by exact prefixLift 5508808
  have htrace : WordTrace (prefixWord ++ tailWord_5508808) baseStart_5508808 baseEnd_5508808 := by
    simpa [prefixWord, tailWord_5508808, baseEnd_5508808] using wordTrace_append hprefix tailTrace_5508808
  have hstable : (prefixWord ++ tailWord_5508808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508808).length < 2 ^ (prefixWord ++ tailWord_5508808).sum := by decide
  have hdescent : baseEnd_5508808 < baseStart_5508808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508812 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 7]
def baseStart_5508812 : Nat := 118140960795 + 5508812 * 2 ^ 59
def prefixEnd_5508812 : Nat := 4983230072969 + 3 ^ 40 * 5508812 * 2
def baseEnd_5508812 : Nat := 314296487917333997935049

theorem tailTrace_5508812 : CollatzResearch.WordTrace tailWord_5508812 prefixEnd_5508812 314296487917333997935049 := by
  unfold tailWord_5508812
  simp only [CollatzResearch.WordTrace]
  refine ⟨100461440059261214515696345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133948586745681619354261793 100461440059261214515696345)
  ·
    refine ⟨75346080044445910886772259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100461440059261214515696345 75346080044445910886772259)
    ·
      refine ⟨113019120066668866330158389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75346080044445910886772259 113019120066668866330158389)
      ·
        refine ⟨10595542506250206218452349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113019120066668866330158389 10595542506250206218452349)
        ·
          refine ⟨3973328439843827331919631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10595542506250206218452349 3973328439843827331919631)
          ·
            refine ⟨5959992659765740997879447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973328439843827331919631 5959992659765740997879447)
            ·
              refine ⟨8939988989648611496819171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959992659765740997879447 8939988989648611496819171)
              ·
                refine ⟨13409983484472917245228757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8939988989648611496819171 13409983484472917245228757)
                ·
                  refine ⟨314296487917333997935049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13409983484472917245228757 314296487917333997935049)
                  ·
                    rfl

theorem cell23_5508812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_5508812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508812 prefixEnd_5508812 := by exact prefixLift 5508812
  have htrace : WordTrace (prefixWord ++ tailWord_5508812) baseStart_5508812 baseEnd_5508812 := by
    simpa [prefixWord, tailWord_5508812, baseEnd_5508812] using wordTrace_append hprefix tailTrace_5508812
  have hstable : (prefixWord ++ tailWord_5508812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508812).length < 2 ^ (prefixWord ++ tailWord_5508812).sum := by decide
  have hdescent : baseEnd_5508812 < baseStart_5508812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508818 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5508818 : Nat := 118140960795 + 5508818 * 2 ^ 59
def prefixEnd_5508818 : Nat := 4983230072969 + 3 ^ 40 * 5508818 * 2
def baseEnd_5508818 : Nat := 2828671472139932957940413

theorem tailTrace_5508818 : CollatzResearch.WordTrace tailWord_5508818 prefixEnd_5508818 2828671472139932957940413 := by
  unfold tailWord_5508818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50230774739125173014027777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133948732637667128037407405 50230774739125173014027777)
  ·
    refine ⟨37673081054343879760520833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50230774739125173014027777 37673081054343879760520833)
    ·
      refine ⟨28254810790757909820390625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37673081054343879760520833 28254810790757909820390625)
      ·
        refine ⟨21191108093068432365292969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28254810790757909820390625 21191108093068432365292969)
        ·
          refine ⟨15893331069801324273969727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21191108093068432365292969 15893331069801324273969727)
          ·
            refine ⟨23839996604701986410954591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893331069801324273969727 23839996604701986410954591)
            ·
              refine ⟨35759994907052979616431887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23839996604701986410954591 35759994907052979616431887)
              ·
                refine ⟨53639992360579469424647831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35759994907052979616431887 53639992360579469424647831)
                ·
                  refine ⟨80459988540869204136971747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53639992360579469424647831 80459988540869204136971747)
                  ·
                    refine ⟨120689982811303806205457621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80459988540869204136971747 120689982811303806205457621)
                    ·
                      refine ⟨2828671472139932957940413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120689982811303806205457621 2828671472139932957940413)
                      ·
                        rfl

theorem cell23_5508818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5508818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508818 prefixEnd_5508818 := by exact prefixLift 5508818
  have htrace : WordTrace (prefixWord ++ tailWord_5508818) baseStart_5508818 baseEnd_5508818 := by
    simpa [prefixWord, tailWord_5508818, baseEnd_5508818] using wordTrace_append hprefix tailTrace_5508818
  have hstable : (prefixWord ++ tailWord_5508818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508818).length < 2 ^ (prefixWord ++ tailWord_5508818).sum := by decide
  have hdescent : baseEnd_5508818 < baseStart_5508818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508841 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_5508841 : Nat := 118140960795 + 5508841 * 2 ^ 59
def prefixEnd_5508841 : Nat := 4983230072969 + 3 ^ 40 * 5508841 * 2
def baseEnd_5508841 : Nat := 2828683282194986367952807

theorem tailTrace_5508841 : CollatzResearch.WordTrace tailWord_5508841 prefixEnd_5508841 2828683282194986367952807 := by
  unfold tailWord_5508841
  simp only [CollatzResearch.WordTrace]
  refine ⟨200923937835417366984198377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133949291890278244656132251 200923937835417366984198377)
  ·
    refine ⟨150692953376563025238148783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200923937835417366984198377 150692953376563025238148783)
    ·
      refine ⟨226039430064844537857223175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150692953376563025238148783 226039430064844537857223175)
      ·
        refine ⟨339059145097266806785834763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226039430064844537857223175 339059145097266806785834763)
        ·
          refine ⟨508588717645900210178752145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339059145097266806785834763 508588717645900210178752145)
          ·
            refine ⟨381441538234425157634064109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508588717645900210178752145 381441538234425157634064109)
            ·
              refine ⟨143040576837909434112774041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381441538234425157634064109 143040576837909434112774041)
              ·
                refine ⟨107280432628432075584580531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143040576837909434112774041 107280432628432075584580531)
                ·
                  refine ⟨160920648942648113376870797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107280432628432075584580531 160920648942648113376870797)
                  ·
                    refine ⟨60345243353493042516326549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160920648942648113376870797 60345243353493042516326549)
                    ·
                      refine ⟨2828683282194986367952807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60345243353493042516326549 2828683282194986367952807)
                      ·
                        rfl

theorem cell23_5508841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_5508841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508841 prefixEnd_5508841 := by exact prefixLift 5508841
  have htrace : WordTrace (prefixWord ++ tailWord_5508841) baseStart_5508841 baseEnd_5508841 := by
    simpa [prefixWord, tailWord_5508841, baseEnd_5508841] using wordTrace_append hprefix tailTrace_5508841
  have hstable : (prefixWord ++ tailWord_5508841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508841).length < 2 ^ (prefixWord ++ tailWord_5508841).sum := by decide
  have hdescent : baseEnd_5508841 < baseStart_5508841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508845 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5508845 : Nat := 118140960795 + 5508845 * 2 ^ 59
def prefixEnd_5508845 : Nat := 4983230072969 + 3 ^ 40 * 5508845 * 2
def baseEnd_5508845 : Nat := 2828685336117604352302789

theorem tailTrace_5508845 : CollatzResearch.WordTrace tailWord_5508845 prefixEnd_5508845 2828685336117604352302789 := by
  unfold tailWord_5508845
  simp only [CollatzResearch.WordTrace]
  refine ⟨200924083727402875667343989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133949389151601917111562659 200924083727402875667343989)
  ·
    refine ⟨18836632849444019593813499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200924083727402875667343989 18836632849444019593813499)
    ·
      refine ⟨28254949274166029390720249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18836632849444019593813499 28254949274166029390720249)
      ·
        refine ⟨21191211955624522043040187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28254949274166029390720249 21191211955624522043040187)
        ·
          refine ⟨31786817933436783064560281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21191211955624522043040187 31786817933436783064560281)
          ·
            refine ⟨23840113450077587298420211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31786817933436783064560281 23840113450077587298420211)
            ·
              refine ⟨35760170175116380947630317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23840113450077587298420211 35760170175116380947630317)
              ·
                refine ⟨13410063815668642855361369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35760170175116380947630317 13410063815668642855361369)
                ·
                  refine ⟨10057547861751482141521027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13410063815668642855361369 10057547861751482141521027)
                  ·
                    refine ⟨15086321792627223212281541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10057547861751482141521027 15086321792627223212281541)
                    ·
                      refine ⟨2828685336117604352302789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15086321792627223212281541 2828685336117604352302789)
                      ·
                        rfl

theorem cell23_5508845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5508845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508845 prefixEnd_5508845 := by exact prefixLift 5508845
  have htrace : WordTrace (prefixWord ++ tailWord_5508845) baseStart_5508845 baseEnd_5508845 := by
    simpa [prefixWord, tailWord_5508845, baseEnd_5508845] using wordTrace_append hprefix tailTrace_5508845
  have hstable : (prefixWord ++ tailWord_5508845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508845).length < 2 ^ (prefixWord ++ tailWord_5508845).sum := by decide
  have hdescent : baseEnd_5508845 < baseStart_5508845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508851 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 10]
def baseStart_5508851 : Nat := 118140960795 + 5508851 * 2 ^ 59
def prefixEnd_5508851 : Nat := 4983230072969 + 3 ^ 40 * 5508851 * 2
def baseEnd_5508851 : Nat := 314298713000170147647529

theorem tailTrace_5508851 : CollatzResearch.WordTrace tailWord_5508851 prefixEnd_5508851 314298713000170147647529 := by
  unfold tailWord_5508851
  simp only [CollatzResearch.WordTrace]
  refine ⟨200924302565381138692062407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133949535043587425794708271 200924302565381138692062407)
  ·
    refine ⟨301386453848071708038093611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200924302565381138692062407 301386453848071708038093611)
    ·
      refine ⟨452079680772107562057140417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301386453848071708038093611 452079680772107562057140417)
      ·
        refine ⟨339059760579080671542855313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452079680772107562057140417 339059760579080671542855313)
        ·
          refine ⟨254294820434310503657141485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339059760579080671542855313 254294820434310503657141485)
          ·
            refine ⟨95360557662866438871428057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254294820434310503657141485 95360557662866438871428057)
            ·
              refine ⟨71520418247149829153571043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95360557662866438871428057 71520418247149829153571043)
              ·
                refine ⟨107280627370724743730356565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71520418247149829153571043 107280627370724743730356565)
                ·
                  refine ⟨314298713000170147647529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107280627370724743730356565 314298713000170147647529)
                  ·
                    rfl

theorem cell23_5508851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 10].length) (baseStart_5508851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508851 prefixEnd_5508851 := by exact prefixLift 5508851
  have htrace : WordTrace (prefixWord ++ tailWord_5508851) baseStart_5508851 baseEnd_5508851 := by
    simpa [prefixWord, tailWord_5508851, baseEnd_5508851] using wordTrace_append hprefix tailTrace_5508851
  have hstable : (prefixWord ++ tailWord_5508851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508851).length < 2 ^ (prefixWord ++ tailWord_5508851).sum := by decide
  have hdescent : baseEnd_5508851 < baseStart_5508851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508852 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5508852 : Nat := 118140960795 + 5508852 * 2 ^ 59
def prefixEnd_5508852 : Nat := 4983230072969 + 3 ^ 40 * 5508852 * 2
def baseEnd_5508852 : Nat := 2828688930482185824915257

theorem tailTrace_5508852 : CollatzResearch.WordTrace tailWord_5508852 prefixEnd_5508852 2828688930482185824915257 := by
  unfold tailWord_5508852
  simp only [CollatzResearch.WordTrace]
  refine ⟨100462169519188757931424405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133949559358918343908565873 100462169519188757931424405)
  ·
    refine ⟨4709164196211973028035519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100462169519188757931424405 4709164196211973028035519)
    ·
      refine ⟨7063746294317959542053279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709164196211973028035519 7063746294317959542053279)
      ·
        refine ⟨10595619441476939313079919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063746294317959542053279 10595619441476939313079919)
        ·
          refine ⟨15893429162215408969619879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10595619441476939313079919 15893429162215408969619879)
          ·
            refine ⟨23840143743323113454429819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893429162215408969619879 23840143743323113454429819)
            ·
              refine ⟨35760215614984670181644729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23840143743323113454429819 35760215614984670181644729)
              ·
                refine ⟨26820161711238502636233547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35760215614984670181644729 26820161711238502636233547)
                ·
                  refine ⟨40230242566857753954350321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26820161711238502636233547 40230242566857753954350321)
                  ·
                    refine ⟨30172681925143315465762741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40230242566857753954350321 30172681925143315465762741)
                    ·
                      refine ⟨2828688930482185824915257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30172681925143315465762741 2828688930482185824915257)
                      ·
                        rfl

theorem cell23_5508852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5508852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508852 prefixEnd_5508852 := by exact prefixLift 5508852
  have htrace : WordTrace (prefixWord ++ tailWord_5508852) baseStart_5508852 baseEnd_5508852 := by
    simpa [prefixWord, tailWord_5508852, baseEnd_5508852] using wordTrace_append hprefix tailTrace_5508852
  have hstable : (prefixWord ++ tailWord_5508852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508852).length < 2 ^ (prefixWord ++ tailWord_5508852).sum := by decide
  have hdescent : baseEnd_5508852 < baseStart_5508852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508865 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_5508865 : Nat := 118140960795 + 5508865 * 2 ^ 59
def prefixEnd_5508865 : Nat := 4983230072969 + 3 ^ 40 * 5508865 * 2
def baseEnd_5508865 : Nat := 2828695605730694274052697

theorem tailTrace_5508865 : CollatzResearch.WordTrace tailWord_5508865 prefixEnd_5508865 2828695605730694274052697 := by
  unfold tailWord_5508865
  simp only [CollatzResearch.WordTrace]
  refine ⟨200924813187330419083072049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133949875458220279388714699 200924813187330419083072049)
  ·
    refine ⟨150693609890497814312304037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200924813187330419083072049 150693609890497814312304037)
    ·
      refine ⟨28255051854468340183557007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150693609890497814312304037 28255051854468340183557007)
      ·
        refine ⟨42382577781702510275335511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28255051854468340183557007 42382577781702510275335511)
        ·
          refine ⟨63573866672553765413003267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42382577781702510275335511 63573866672553765413003267)
          ·
            refine ⟨95360800008830648119504901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63573866672553765413003267 95360800008830648119504901)
            ·
              refine ⟨17880150001655746522407169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95360800008830648119504901 17880150001655746522407169)
              ·
                refine ⟨13410112501241809891805377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17880150001655746522407169 13410112501241809891805377)
                ·
                  refine ⟨10057584375931357418854033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13410112501241809891805377 10057584375931357418854033)
                  ·
                    refine ⟨7543188281948518064140525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10057584375931357418854033 7543188281948518064140525)
                    ·
                      refine ⟨2828695605730694274052697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7543188281948518064140525 2828695605730694274052697)
                      ·
                        rfl

theorem cell23_5508865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_5508865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508865 prefixEnd_5508865 := by exact prefixLift 5508865
  have htrace : WordTrace (prefixWord ++ tailWord_5508865) baseStart_5508865 baseEnd_5508865 := by
    simpa [prefixWord, tailWord_5508865, baseEnd_5508865] using wordTrace_append hprefix tailTrace_5508865
  have hstable : (prefixWord ++ tailWord_5508865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508865).length < 2 ^ (prefixWord ++ tailWord_5508865).sum := by decide
  have hdescent : baseEnd_5508865 < baseStart_5508865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508872 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 1, 4]
def baseStart_5508872 : Nat := 118140960795 + 5508872 * 2 ^ 59
def prefixEnd_5508872 : Nat := 4983230072969 + 3 ^ 40 * 5508872 * 2
def baseEnd_5508872 : Nat := 942899733365091915555055

theorem tailTrace_5508872 : CollatzResearch.WordTrace tailWord_5508872 prefixEnd_5508872 942899733365091915555055 := by
  unfold tailWord_5508872
  simp only [CollatzResearch.WordTrace]
  refine ⟨100462534249152529639288435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133950045665536706185717913 100462534249152529639288435)
  ·
    refine ⟨150693801373728794458932653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100462534249152529639288435 150693801373728794458932653)
    ·
      refine ⟨56510175515148297922099745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150693801373728794458932653 56510175515148297922099745)
      ·
        refine ⟨42382631636361223441574809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56510175515148297922099745 42382631636361223441574809)
        ·
          refine ⟨31786973727270917581181107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42382631636361223441574809 31786973727270917581181107)
          ·
            refine ⟨47680460590906376371771661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31786973727270917581181107 47680460590906376371771661)
            ·
              refine ⟨17880172721589891139414373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47680460590906376371771661 17880172721589891139414373)
              ·
                refine ⟨3352532385298104588640195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17880172721589891139414373 3352532385298104588640195)
                ·
                  refine ⟨5028798577947156882960293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352532385298104588640195 5028798577947156882960293)
                  ·
                    refine ⟨942899733365091915555055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028798577947156882960293 942899733365091915555055)
                    ·
                      rfl

theorem cell23_5508872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_5508872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508872 prefixEnd_5508872 := by exact prefixLift 5508872
  have htrace : WordTrace (prefixWord ++ tailWord_5508872) baseStart_5508872 baseEnd_5508872 := by
    simpa [prefixWord, tailWord_5508872, baseEnd_5508872] using wordTrace_append hprefix tailTrace_5508872
  have hstable : (prefixWord ++ tailWord_5508872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508872).length < 2 ^ (prefixWord ++ tailWord_5508872).sum := by decide
  have hdescent : baseEnd_5508872 < baseStart_5508872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508945 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_5508945 : Nat := 118140960795 + 5508945 * 2 ^ 59
def prefixEnd_5508945 : Nat := 4983230072969 + 3 ^ 40 * 5508945 * 2
def baseEnd_5508945 : Nat := 942912228061017987017443

theorem tailTrace_5508945 : CollatzResearch.WordTrace tailWord_5508945 prefixEnd_5508945 942912228061017987017443 := by
  unfold tailWord_5508945
  simp only [CollatzResearch.WordTrace]
  refine ⟨200927731027040592745984289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133951820684693728497322859 200927731027040592745984289)
  ·
    refine ⟨150695798270280444559488217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200927731027040592745984289 150695798270280444559488217)
    ·
      refine ⟨113021848702710333419616163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150695798270280444559488217 113021848702710333419616163)
      ·
        refine ⟨169532773054065500129424245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113021848702710333419616163 169532773054065500129424245)
        ·
          refine ⟨15893697473818640637133523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169532773054065500129424245 15893697473818640637133523)
          ·
            refine ⟨23840546210727960955700285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893697473818640637133523 23840546210727960955700285)
            ·
              refine ⟨8940204829022985358387607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23840546210727960955700285 8940204829022985358387607)
              ·
                refine ⟨13410307243534478037581411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8940204829022985358387607 13410307243534478037581411)
                ·
                  refine ⟨20115460865301717056372117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13410307243534478037581411 20115460865301717056372117)
                  ·
                    refine ⟨942912228061017987017443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20115460865301717056372117 942912228061017987017443)
                    ·
                      rfl

theorem cell23_5508945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_5508945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508945 prefixEnd_5508945 := by exact prefixLift 5508945
  have htrace : WordTrace (prefixWord ++ tailWord_5508945) baseStart_5508945 baseEnd_5508945 := by
    simpa [prefixWord, tailWord_5508945, baseEnd_5508945] using wordTrace_append hprefix tailTrace_5508945
  have hstable : (prefixWord ++ tailWord_5508945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508945).length < 2 ^ (prefixWord ++ tailWord_5508945).sum := by decide
  have hdescent : baseEnd_5508945 < baseStart_5508945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508962 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5508962 : Nat := 118140960795 + 5508962 * 2 ^ 59
def prefixEnd_5508962 : Nat := 4983230072969 + 3 ^ 40 * 5508962 * 2
def baseEnd_5508962 : Nat := 942915137784726798179917

theorem tailTrace_5508962 : CollatzResearch.WordTrace tailWord_5508962 prefixEnd_5508962 942915137784726798179917 := by
  unfold tailWord_5508962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50232087766994751162338285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133952234045319336432902093 50232087766994751162338285)
  ·
    refine ⟨18837032912623031685876857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50232087766994751162338285 18837032912623031685876857)
    ·
      refine ⟨14127774684467273764407643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18837032912623031685876857 14127774684467273764407643)
      ·
        refine ⟨21191662026700910646611465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14127774684467273764407643 21191662026700910646611465)
        ·
          refine ⟨15893746520025682984958599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21191662026700910646611465 15893746520025682984958599)
          ·
            refine ⟨23840619780038524477437899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15893746520025682984958599 23840619780038524477437899)
            ·
              refine ⟨35760929670057786716156849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23840619780038524477437899 35760929670057786716156849)
              ·
                refine ⟨26820697252543340037117637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35760929670057786716156849 26820697252543340037117637)
                ·
                  refine ⟨5028880734851876256959557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26820697252543340037117637 5028880734851876256959557)
                  ·
                    refine ⟨942915137784726798179917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028880734851876256959557 942915137784726798179917)
                    ·
                      rfl

theorem cell23_5508962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5508962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508962 prefixEnd_5508962 := by exact prefixLift 5508962
  have htrace : WordTrace (prefixWord ++ tailWord_5508962) baseStart_5508962 baseEnd_5508962 := by
    simpa [prefixWord, tailWord_5508962, baseEnd_5508962] using wordTrace_append hprefix tailTrace_5508962
  have hstable : (prefixWord ++ tailWord_5508962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508962).length < 2 ^ (prefixWord ++ tailWord_5508962).sum := by decide
  have hdescent : baseEnd_5508962 < baseStart_5508962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508963 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 1, 1, 3]
def baseStart_5508963 : Nat := 118140960795 + 5508963 * 2 ^ 59
def prefixEnd_5508963 : Nat := 4983230072969 + 3 ^ 40 * 5508963 * 2
def baseEnd_5508963 : Nat := 2828745926834834890627247

theorem tailTrace_5508963 : CollatzResearch.WordTrace tailWord_5508963 prefixEnd_5508963 2828745926834834890627247 := by
  unfold tailWord_5508963
  simp only [CollatzResearch.WordTrace]
  refine ⟨200928387540975381820139543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133952258360650254546759695 200928387540975381820139543)
  ·
    refine ⟨301392581311463072730209315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200928387540975381820139543 301392581311463072730209315)
    ·
      refine ⟨452088871967194609095313973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301392581311463072730209315 452088871967194609095313973)
      ·
        refine ⟨42383331746924494602685685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 452088871967194609095313973 42383331746924494602685685)
        ·
          refine ⟨3973437351274171369001783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42383331746924494602685685 3973437351274171369001783)
          ·
            refine ⟨5960156026911257053502675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973437351274171369001783 5960156026911257053502675)
            ·
              refine ⟨8940234040366885580254013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5960156026911257053502675 8940234040366885580254013)
              ·
                refine ⟨3352587765137582092595255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8940234040366885580254013 3352587765137582092595255)
                ·
                  refine ⟨5028881647706373138892883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352587765137582092595255 5028881647706373138892883)
                  ·
                    refine ⟨7543322471559559708339325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5028881647706373138892883 7543322471559559708339325)
                    ·
                      refine ⟨2828745926834834890627247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7543322471559559708339325 2828745926834834890627247)
                      ·
                        rfl

theorem cell23_5508963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_5508963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508963 prefixEnd_5508963 := by exact prefixLift 5508963
  have htrace : WordTrace (prefixWord ++ tailWord_5508963) baseStart_5508963 baseEnd_5508963 := by
    simpa [prefixWord, tailWord_5508963, baseEnd_5508963] using wordTrace_append hprefix tailTrace_5508963
  have hstable : (prefixWord ++ tailWord_5508963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508963).length < 2 ^ (prefixWord ++ tailWord_5508963).sum := by decide
  have hdescent : baseEnd_5508963 < baseStart_5508963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5508972 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_5508972 : Nat := 118140960795 + 5508972 * 2 ^ 59
def prefixEnd_5508972 : Nat := 4983230072969 + 3 ^ 40 * 5508972 * 2
def baseEnd_5508972 : Nat := 2828750548160725355414705

theorem tailTrace_5508972 : CollatzResearch.WordTrace tailWord_5508972 prefixEnd_5508972 2828750548160725355414705 := by
  unfold tailWord_5508972
  simp only [CollatzResearch.WordTrace]
  refine ⟨100464357898971388178608585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133952477198628517571478113 100464357898971388178608585)
  ·
    refine ⟨75348268424228541133956439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100464357898971388178608585 75348268424228541133956439)
    ·
      refine ⟨113022402636342811700934659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75348268424228541133956439 113022402636342811700934659)
      ·
        refine ⟨169533603954514217551401989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113022402636342811700934659 169533603954514217551401989)
        ·
          refine ⟨31787550741471415790887873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169533603954514217551401989 31787550741471415790887873)
          ·
            refine ⟨23840663056103561843165905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31787550741471415790887873 23840663056103561843165905)
            ·
              refine ⟨17880497292077671382374429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23840663056103561843165905 17880497292077671382374429)
              ·
                refine ⟨6705186484529126768390411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17880497292077671382374429 6705186484529126768390411)
                ·
                  refine ⟨10057779726793690152585617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6705186484529126768390411 10057779726793690152585617)
                  ·
                    refine ⟨7543334795095267614439213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10057779726793690152585617 7543334795095267614439213)
                    ·
                      refine ⟨2828750548160725355414705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7543334795095267614439213 2828750548160725355414705)
                      ·
                        rfl

theorem cell23_5508972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_5508972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5508972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5508972 prefixEnd_5508972 := by exact prefixLift 5508972
  have htrace : WordTrace (prefixWord ++ tailWord_5508972) baseStart_5508972 baseEnd_5508972 := by
    simpa [prefixWord, tailWord_5508972, baseEnd_5508972] using wordTrace_append hprefix tailTrace_5508972
  have hstable : (prefixWord ++ tailWord_5508972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5508972).length < 2 ^ (prefixWord ++ tailWord_5508972).sum := by decide
  have hdescent : baseEnd_5508972 < baseStart_5508972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5508972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509055 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_5509055 : Nat := 118140960795 + 5509055 * 2 ^ 59
def prefixEnd_5509055 : Nat := 4983230072969 + 3 ^ 40 * 5509055 * 2
def baseEnd_5509055 : Nat := 2828793167055048530676823

theorem tailTrace_5509055 : CollatzResearch.WordTrace tailWord_5509055 prefixEnd_5509055 2828793167055048530676823 := by
  unfold tailWord_5509055
  simp only [CollatzResearch.WordTrace]
  refine ⟨200931743056642081532488619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133954495371094721021659079 200931743056642081532488619)
  ·
    refine ⟨301397614584963122298732929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200931743056642081532488619 301397614584963122298732929)
    ·
      refine ⟨226048210938722341724049697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301397614584963122298732929 226048210938722341724049697)
      ·
        refine ⟨169536158204041756293037273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226048210938722341724049697 169536158204041756293037273)
        ·
          refine ⟨127152118653031317219777955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169536158204041756293037273 127152118653031317219777955)
          ·
            refine ⟨190728177979546975829666933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127152118653031317219777955 190728177979546975829666933)
            ·
              refine ⟨17880766685582528984031275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190728177979546975829666933 17880766685582528984031275)
              ·
                refine ⟨26821150028373793476046913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17880766685582528984031275 26821150028373793476046913)
                ·
                  refine ⟨20115862521280345107035185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26821150028373793476046913 20115862521280345107035185)
                  ·
                    refine ⟨15086896890960258830276389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20115862521280345107035185 15086896890960258830276389)
                    ·
                      refine ⟨2828793167055048530676823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15086896890960258830276389 2828793167055048530676823)
                      ·
                        rfl

theorem cell23_5509055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_5509055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509055 prefixEnd_5509055 := by exact prefixLift 5509055
  have htrace : WordTrace (prefixWord ++ tailWord_5509055) baseStart_5509055 baseEnd_5509055 := by
    simpa [prefixWord, tailWord_5509055, baseEnd_5509055] using wordTrace_append hprefix tailTrace_5509055
  have hstable : (prefixWord ++ tailWord_5509055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509055).length < 2 ^ (prefixWord ++ tailWord_5509055).sum := by decide
  have hdescent : baseEnd_5509055 < baseStart_5509055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509110 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5509110 : Nat := 118140960795 + 5509110 * 2 ^ 59
def prefixEnd_5509110 : Nat := 4983230072969 + 3 ^ 40 * 5509110 * 2
def baseEnd_5509110 : Nat := 2828821408491045815489071

theorem tailTrace_5509110 : CollatzResearch.WordTrace tailWord_5509110 prefixEnd_5509110 2828821408491045815489071 := by
  unfold tailWord_5509110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558359316965176620358799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133955832714295217283827189 12558359316965176620358799)
  ·
    refine ⟨18837538975447764930538199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12558359316965176620358799 18837538975447764930538199)
    ·
      refine ⟨28256308463171647395807299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18837538975447764930538199 28256308463171647395807299)
      ·
        refine ⟨42384462694757471093710949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28256308463171647395807299 42384462694757471093710949)
        ·
          refine ⟨7947086755267025830070803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42384462694757471093710949 7947086755267025830070803)
          ·
            refine ⟨11920630132900538745106205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7947086755267025830070803 11920630132900538745106205)
            ·
              refine ⟨4470236299837702029414827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11920630132900538745106205 4470236299837702029414827)
              ·
                refine ⟨6705354449756553044122241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470236299837702029414827 6705354449756553044122241)
                ·
                  refine ⟨5029015837317414783091681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6705354449756553044122241 5029015837317414783091681)
                  ·
                    refine ⟨3771761877988061087318761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5029015837317414783091681 3771761877988061087318761)
                    ·
                      refine ⟨2828821408491045815489071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771761877988061087318761 2828821408491045815489071)
                      ·
                        rfl

theorem cell23_5509110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5509110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509110 prefixEnd_5509110 := by exact prefixLift 5509110
  have htrace : WordTrace (prefixWord ++ tailWord_5509110) baseStart_5509110 baseEnd_5509110 := by
    simpa [prefixWord, tailWord_5509110, baseEnd_5509110] using wordTrace_append hprefix tailTrace_5509110
  have hstable : (prefixWord ++ tailWord_5509110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509110).length < 2 ^ (prefixWord ++ tailWord_5509110).sum := by decide
  have hdescent : baseEnd_5509110 < baseStart_5509110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509115 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_5509115 : Nat := 118140960795 + 5509115 * 2 ^ 59
def prefixEnd_5509115 : Nat := 4983230072969 + 3 ^ 40 * 5509115 * 2
def baseEnd_5509115 : Nat := 2828823975894318295926547

theorem tailTrace_5509115 : CollatzResearch.WordTrace tailWord_5509115 prefixEnd_5509115 2828823975894318295926547 := by
  unfold tailWord_5509115
  simp only [CollatzResearch.WordTrace]
  refine ⟨200933931436424711779672799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133955954290949807853115199 200933931436424711779672799)
  ·
    refine ⟨301400897154637067669509199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200933931436424711779672799 301400897154637067669509199)
    ·
      refine ⟨452101345731955601504263799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301400897154637067669509199 452101345731955601504263799)
      ·
        refine ⟨678152018597933402256395699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452101345731955601504263799 678152018597933402256395699)
        ·
          refine ⟨1017228027896900103384593549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678152018597933402256395699 1017228027896900103384593549)
          ·
            refine ⟨381460510461337538769222581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1017228027896900103384593549 381460510461337538769222581)
            ·
              refine ⟨35761922855750394259614617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381460510461337538769222581 35761922855750394259614617)
              ·
                refine ⟨26821442141812795694710963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35761922855750394259614617 26821442141812795694710963)
                ·
                  refine ⟨40232163212719193542066445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26821442141812795694710963 40232163212719193542066445)
                  ·
                    refine ⟨15087061204769697578274917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40232163212719193542066445 15087061204769697578274917)
                    ·
                      refine ⟨2828823975894318295926547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15087061204769697578274917 2828823975894318295926547)
                      ·
                        rfl

theorem cell23_5509115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_5509115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509115 prefixEnd_5509115 := by exact prefixLift 5509115
  have htrace : WordTrace (prefixWord ++ tailWord_5509115) baseStart_5509115 baseEnd_5509115 := by
    simpa [prefixWord, tailWord_5509115, baseEnd_5509115] using wordTrace_append hprefix tailTrace_5509115
  have hstable : (prefixWord ++ tailWord_5509115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509115).length < 2 ^ (prefixWord ++ tailWord_5509115).sum := by decide
  have hdescent : baseEnd_5509115 < baseStart_5509115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509132 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_5509132 : Nat := 118140960795 + 5509132 * 2 ^ 59
def prefixEnd_5509132 : Nat := 4983230072969 + 3 ^ 40 * 5509132 * 2
def baseEnd_5509132 : Nat := 2828832705065444729413969

theorem tailTrace_5509132 : CollatzResearch.WordTrace tailWord_5509132 prefixEnd_5509132 2828832705065444729413969 := by
  unfold tailWord_5509132
  simp only [CollatzResearch.WordTrace]
  refine ⟨100467275738681561841520825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133956367651575415788694433 100467275738681561841520825)
  ·
    refine ⟨75350456804011171381140619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100467275738681561841520825 75350456804011171381140619)
    ·
      refine ⟨113025685206016757071710929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75350456804011171381140619 113025685206016757071710929)
      ·
        refine ⟨84769263904512567803783197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113025685206016757071710929 84769263904512567803783197)
        ·
          refine ⟨31788473964192212926418699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84769263904512567803783197 31788473964192212926418699)
          ·
            refine ⟨47682710946288319389628049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31788473964192212926418699 47682710946288319389628049)
            ·
              refine ⟨35762033209716239542221037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47682710946288319389628049 35762033209716239542221037)
              ·
                refine ⟨13410762453643589828332889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35762033209716239542221037 13410762453643589828332889)
                ·
                  refine ⟨10058071840232692371249667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13410762453643589828332889 10058071840232692371249667)
                  ·
                    refine ⟨15087107760349038556874501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10058071840232692371249667 15087107760349038556874501)
                    ·
                      refine ⟨2828832705065444729413969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15087107760349038556874501 2828832705065444729413969)
                      ·
                        rfl

theorem cell23_5509132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_5509132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509132 prefixEnd_5509132 := by exact prefixLift 5509132
  have htrace : WordTrace (prefixWord ++ tailWord_5509132) baseStart_5509132 baseEnd_5509132 := by
    simpa [prefixWord, tailWord_5509132, baseEnd_5509132] using wordTrace_append hprefix tailTrace_5509132
  have hstable : (prefixWord ++ tailWord_5509132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509132).length < 2 ^ (prefixWord ++ tailWord_5509132).sum := by decide
  have hdescent : baseEnd_5509132 < baseStart_5509132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509149 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5509149 : Nat := 118140960795 + 5509149 * 2 ^ 59
def prefixEnd_5509149 : Nat := 4983230072969 + 3 ^ 40 * 5509149 * 2
def baseEnd_5509149 : Nat := 2828841434236571162901391

theorem tailTrace_5509149 : CollatzResearch.WordTrace tailWord_5509149 prefixEnd_5509149 2828841434236571162901391 := by
  unfold tailWord_5509149
  simp only [CollatzResearch.WordTrace]
  refine ⟨200935171518301535586410501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133956781012201023724273667 200935171518301535586410501)
  ·
    refine ⟨37675344659681537922451969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200935171518301535586410501 37675344659681537922451969)
    ·
      refine ⟨28256508494761153441838977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37675344659681537922451969 28256508494761153441838977)
      ·
        refine ⟨21192381371070865081379233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28256508494761153441838977 21192381371070865081379233)
        ·
          refine ⟨15894286028303148811034425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21192381371070865081379233 15894286028303148811034425)
          ·
            refine ⟨11920714521227361608275819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15894286028303148811034425 11920714521227361608275819)
            ·
              refine ⟨17881071781841042412413729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11920714521227361608275819 17881071781841042412413729)
              ·
                refine ⟨13410803836380781809310297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17881071781841042412413729 13410803836380781809310297)
                ·
                  refine ⟨10058102877285586356982723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13410803836380781809310297 10058102877285586356982723)
                  ·
                    refine ⟨15087154315928379535474085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10058102877285586356982723 15087154315928379535474085)
                    ·
                      refine ⟨2828841434236571162901391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15087154315928379535474085 2828841434236571162901391)
                      ·
                        rfl

theorem cell23_5509149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5509149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509149 prefixEnd_5509149 := by exact prefixLift 5509149
  have htrace : WordTrace (prefixWord ++ tailWord_5509149) baseStart_5509149 baseEnd_5509149 := by
    simpa [prefixWord, tailWord_5509149, baseEnd_5509149] using wordTrace_append hprefix tailTrace_5509149
  have hstable : (prefixWord ++ tailWord_5509149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509149).length < 2 ^ (prefixWord ++ tailWord_5509149).sum := by decide
  have hdescent : baseEnd_5509149 < baseStart_5509149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509155 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 8]
def baseStart_5509155 : Nat := 118140960795 + 5509155 * 2 ^ 59
def prefixEnd_5509155 : Nat := 4983230072969 + 3 ^ 40 * 5509155 * 2
def baseEnd_5509155 : Nat := 314316057235610904380707

theorem tailTrace_5509155 : CollatzResearch.WordTrace tailWord_5509155 prefixEnd_5509155 314316057235610904380707 := by
  unfold tailWord_5509155
  simp only [CollatzResearch.WordTrace]
  refine ⟨200935390356279798611128919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133956926904186532407419279 200935390356279798611128919)
  ·
    refine ⟨301403085534419697916693379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200935390356279798611128919 301403085534419697916693379)
    ·
      refine ⟨452104628301629546875040069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301403085534419697916693379 452104628301629546875040069)
      ·
        refine ⟨84769617806555540039070013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 452104628301629546875040069 84769617806555540039070013)
        ·
          refine ⟨31788606677458327514651255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84769617806555540039070013 31788606677458327514651255)
          ·
            refine ⟨47682910016187491271976883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31788606677458327514651255 47682910016187491271976883)
            ·
              refine ⟨71524365024281236907965325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47682910016187491271976883 71524365024281236907965325)
              ·
                refine ⟨26821636884105463840486997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71524365024281236907965325 26821636884105463840486997)
                ·
                  refine ⟨314316057235610904380707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26821636884105463840486997 314316057235610904380707)
                  ·
                    rfl

theorem cell23_5509155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 8].length) (baseStart_5509155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509155 prefixEnd_5509155 := by exact prefixLift 5509155
  have htrace : WordTrace (prefixWord ++ tailWord_5509155) baseStart_5509155 baseEnd_5509155 := by
    simpa [prefixWord, tailWord_5509155, baseEnd_5509155] using wordTrace_append hprefix tailTrace_5509155
  have hstable : (prefixWord ++ tailWord_5509155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509155).length < 2 ^ (prefixWord ++ tailWord_5509155).sum := by decide
  have hdescent : baseEnd_5509155 < baseStart_5509155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509175 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_5509175 : Nat := 118140960795 + 5509175 * 2 ^ 59
def prefixEnd_5509175 : Nat := 4983230072969 + 3 ^ 40 * 5509175 * 2
def baseEnd_5509175 : Nat := 2828854784733588061176271

theorem tailTrace_5509175 : CollatzResearch.WordTrace tailWord_5509175 prefixEnd_5509175 2828854784733588061176271 := by
  unfold tailWord_5509175
  simp only [CollatzResearch.WordTrace]
  refine ⟨200936119816207342026856979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133957413210804894684571319 200936119816207342026856979)
  ·
    refine ⟨301404179724311013040285469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200936119816207342026856979 301404179724311013040285469)
    ·
      refine ⟨113026567396616629890107051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301404179724311013040285469 113026567396616629890107051)
      ·
        refine ⟨169539851094924944835160577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113026567396616629890107051 169539851094924944835160577)
        ·
          refine ⟨127154888321193708626370433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169539851094924944835160577 127154888321193708626370433)
          ·
            refine ⟨95366166240895281469777825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127154888321193708626370433 95366166240895281469777825)
            ·
              refine ⟨71524624680671461102333369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95366166240895281469777825 71524624680671461102333369)
              ·
                refine ⟨53643468510503595826750027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71524624680671461102333369 53643468510503595826750027)
                ·
                  refine ⟨80465202765755393740125041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53643468510503595826750027 80465202765755393740125041)
                  ·
                    refine ⟨60348902074316545305093781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80465202765755393740125041 60348902074316545305093781)
                    ·
                      refine ⟨2828854784733588061176271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60348902074316545305093781 2828854784733588061176271)
                      ·
                        rfl

theorem cell23_5509175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_5509175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509175 prefixEnd_5509175 := by exact prefixLift 5509175
  have htrace : WordTrace (prefixWord ++ tailWord_5509175) baseStart_5509175 baseEnd_5509175 := by
    simpa [prefixWord, tailWord_5509175, baseEnd_5509175] using wordTrace_append hprefix tailTrace_5509175
  have hstable : (prefixWord ++ tailWord_5509175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509175).length < 2 ^ (prefixWord ++ tailWord_5509175).sum := by decide
  have hdescent : baseEnd_5509175 < baseStart_5509175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509206 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_5509206 : Nat := 118140960795 + 5509206 * 2 ^ 59
def prefixEnd_5509206 : Nat := 4983230072969 + 3 ^ 40 * 5509206 * 2
def baseEnd_5509206 : Nat := 314318966959319715543181

theorem tailTrace_5509206 : CollatzResearch.WordTrace tailWord_5509206 prefixEnd_5509206 314318966959319715543181 := by
  unfold tailWord_5509206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558578154943439645077217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133958166986063356214156981 12558578154943439645077217)
  ·
    refine ⟨9418933616207579733807913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12558578154943439645077217 9418933616207579733807913)
    ·
      refine ⟨7064200212155684800355935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9418933616207579733807913 7064200212155684800355935)
      ·
        refine ⟨10596300318233527200533903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7064200212155684800355935 10596300318233527200533903)
        ·
          refine ⟨15894450477350290800800855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10596300318233527200533903 15894450477350290800800855)
          ·
            refine ⟨23841675716025436201201283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15894450477350290800800855 23841675716025436201201283)
            ·
              refine ⟨35762513574038154301801925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23841675716025436201201283 35762513574038154301801925)
              ·
                refine ⟨6705471295132153931587861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35762513574038154301801925 6705471295132153931587861)
                ·
                  refine ⟨314318966959319715543181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6705471295132153931587861 314318966959319715543181)
                  ·
                    rfl

theorem cell23_5509206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_5509206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509206 prefixEnd_5509206 := by exact prefixLift 5509206
  have htrace : WordTrace (prefixWord ++ tailWord_5509206) baseStart_5509206 baseEnd_5509206 := by
    simpa [prefixWord, tailWord_5509206, baseEnd_5509206] using wordTrace_append hprefix tailTrace_5509206
  have hstable : (prefixWord ++ tailWord_5509206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509206).length < 2 ^ (prefixWord ++ tailWord_5509206).sum := by decide
  have hdescent : baseEnd_5509206 < baseStart_5509206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509209 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 2, 3, 2]
def baseStart_5509209 : Nat := 118140960795 + 5509209 * 2 ^ 59
def prefixEnd_5509209 : Nat := 4983230072969 + 3 ^ 40 * 5509209 * 2
def baseEnd_5509209 : Nat := 2828872243075840928151115

theorem tailTrace_5509209 : CollatzResearch.WordTrace tailWord_5509209 prefixEnd_5509209 2828872243075840928151115 := by
  unfold tailWord_5509209
  simp only [CollatzResearch.WordTrace]
  refine ⟨200937359898084165833594681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133958239932056110555729787 200937359898084165833594681)
  ·
    refine ⟨150703019923563124375196011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200937359898084165833594681 150703019923563124375196011)
    ·
      refine ⟨226054529885344686562794017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150703019923563124375196011 226054529885344686562794017)
      ·
        refine ⟨169540897414008514922095513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226054529885344686562794017 169540897414008514922095513)
        ·
          refine ⟨127155673060506386191571635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169540897414008514922095513 127155673060506386191571635)
          ·
            refine ⟨190733509590759579287357453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127155673060506386191571635 190733509590759579287357453)
            ·
              refine ⟨71525066096534842232759045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190733509590759579287357453 71525066096534842232759045)
              ·
                refine ⟨13410949893100282918642321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71525066096534842232759045 13410949893100282918642321)
                ·
                  refine ⟨10058212419825212188981741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13410949893100282918642321 10058212419825212188981741)
                  ·
                    refine ⟨3771829657434454570868153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10058212419825212188981741 3771829657434454570868153)
                    ·
                      refine ⟨2828872243075840928151115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771829657434454570868153 2828872243075840928151115)
                      ·
                        rfl

theorem cell23_5509209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_5509209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509209 prefixEnd_5509209 := by exact prefixLift 5509209
  have htrace : WordTrace (prefixWord ++ tailWord_5509209) baseStart_5509209 baseEnd_5509209 := by
    simpa [prefixWord, tailWord_5509209, baseEnd_5509209] using wordTrace_append hprefix tailTrace_5509209
  have hstable : (prefixWord ++ tailWord_5509209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509209).length < 2 ^ (prefixWord ++ tailWord_5509209).sum := by decide
  have hdescent : baseEnd_5509209 < baseStart_5509209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509232 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_5509232 : Nat := 118140960795 + 5509232 * 2 ^ 59
def prefixEnd_5509232 : Nat := 4983230072969 + 3 ^ 40 * 5509232 * 2
def baseEnd_5509232 : Nat := 942961351043631446054503

theorem tailTrace_5509232 : CollatzResearch.WordTrace tailWord_5509232 prefixEnd_5509232 942961351043631446054503 := by
  unfold tailWord_5509232
  simp only [CollatzResearch.WordTrace]
  refine ⟨100469099388500420380840975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133958799184667227174454633 100469099388500420380840975)
  ·
    refine ⟨150703649082750630571261463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100469099388500420380840975 150703649082750630571261463)
    ·
      refine ⟨226055473624125945856892195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150703649082750630571261463 226055473624125945856892195)
      ·
        refine ⟨339083210436188918785338293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226055473624125945856892195 339083210436188918785338293)
        ·
          refine ⟨31789050978392711136125465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339083210436188918785338293 31789050978392711136125465)
          ·
            refine ⟨23841788233794533352094099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31789050978392711136125465 23841788233794533352094099)
            ·
              refine ⟨35762682350691800028141149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23841788233794533352094099 35762682350691800028141149)
              ·
                refine ⟨13411005881509425010552931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35762682350691800028141149 13411005881509425010552931)
                ·
                  refine ⟨20116508822264137515829397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13411005881509425010552931 20116508822264137515829397)
                  ·
                    refine ⟨942961351043631446054503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20116508822264137515829397 942961351043631446054503)
                    ·
                      rfl

theorem cell23_5509232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_5509232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509232 prefixEnd_5509232 := by exact prefixLift 5509232
  have htrace : WordTrace (prefixWord ++ tailWord_5509232) baseStart_5509232 baseEnd_5509232 := by
    simpa [prefixWord, tailWord_5509232, baseEnd_5509232] using wordTrace_append hprefix tailTrace_5509232
  have hstable : (prefixWord ++ tailWord_5509232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509232).length < 2 ^ (prefixWord ++ tailWord_5509232).sum := by decide
  have hdescent : baseEnd_5509232 < baseStart_5509232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509256 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5509256 : Nat := 118140960795 + 5509256 * 2 ^ 59
def prefixEnd_5509256 : Nat := 4983230072969 + 3 ^ 40 * 5509256 * 2
def baseEnd_5509256 : Nat := 2828896376666602244263399

theorem tailTrace_5509256 : CollatzResearch.WordTrace tailWord_5509256 prefixEnd_5509256 2828896376666602244263399 := by
  unfold tailWord_5509256
  simp only [CollatzResearch.WordTrace]
  refine ⟨100469537064456946430277811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133959382752609261907037081 100469537064456946430277811)
  ·
    refine ⟨150704305596685419645416717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100469537064456946430277811 150704305596685419645416717)
    ·
      refine ⟨56514114598757032367031269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150704305596685419645416717 56514114598757032367031269)
      ·
        refine ⟨10596396487266943568818363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56514114598757032367031269 10596396487266943568818363)
        ·
          refine ⟨15894594730900415353227545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10596396487266943568818363 15894594730900415353227545)
          ·
            refine ⟨11920946048175311514920659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15894594730900415353227545 11920946048175311514920659)
            ·
              refine ⟨17881419072262967272380989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11920946048175311514920659 17881419072262967272380989)
              ·
                refine ⟨6705532152098612727142871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17881419072262967272380989 6705532152098612727142871)
                ·
                  refine ⟨10058298228147919090714307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6705532152098612727142871 10058298228147919090714307)
                  ·
                    refine ⟨15087447342221878636071461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10058298228147919090714307 15087447342221878636071461)
                    ·
                      refine ⟨2828896376666602244263399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15087447342221878636071461 2828896376666602244263399)
                      ·
                        rfl

theorem cell23_5509256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5509256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509256 prefixEnd_5509256 := by exact prefixLift 5509256
  have htrace : WordTrace (prefixWord ++ tailWord_5509256) baseStart_5509256 baseEnd_5509256 := by
    simpa [prefixWord, tailWord_5509256, baseEnd_5509256] using wordTrace_append hprefix tailTrace_5509256
  have hstable : (prefixWord ++ tailWord_5509256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509256).length < 2 ^ (prefixWord ++ tailWord_5509256).sum := by decide
  have hdescent : baseEnd_5509256 < baseStart_5509256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509293 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_5509293 : Nat := 118140960795 + 5509293 * 2 ^ 59
def prefixEnd_5509293 : Nat := 4983230072969 + 3 ^ 40 * 5509293 * 2
def baseEnd_5509293 : Nat := 2828915375450818599500729

theorem tailTrace_5509293 : CollatzResearch.WordTrace tailWord_5509293 prefixEnd_5509293 2828915375450818599500729 := by
  unfold tailWord_5509293
  simp only [CollatzResearch.WordTrace]
  refine ⟨200940423629779848179652533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133960282419853232119768355 200940423629779848179652533)
  ·
    refine ⟨18838164715291860766842425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200940423629779848179652533 18838164715291860766842425)
    ·
      refine ⟨14128623536468895575131819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18838164715291860766842425 14128623536468895575131819)
      ·
        refine ⟨21192935304703343362697729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14128623536468895575131819 21192935304703343362697729)
        ·
          refine ⟨15894701478527507522023297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21192935304703343362697729 15894701478527507522023297)
          ·
            refine ⟨11921026108895630641517473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15894701478527507522023297 11921026108895630641517473)
            ·
              refine ⟨8940769581671722981138105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11921026108895630641517473 8940769581671722981138105)
              ·
                refine ⟨6705577186253792235853579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8940769581671722981138105 6705577186253792235853579)
                ·
                  refine ⟨10058365779380688353780369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6705577186253792235853579 10058365779380688353780369)
                  ·
                    refine ⟨7543774334535516265335277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10058365779380688353780369 7543774334535516265335277)
                    ·
                      refine ⟨2828915375450818599500729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7543774334535516265335277 2828915375450818599500729)
                      ·
                        rfl

theorem cell23_5509293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_5509293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509293 prefixEnd_5509293 := by exact prefixLift 5509293
  have htrace : WordTrace (prefixWord ++ tailWord_5509293) baseStart_5509293 baseEnd_5509293 := by
    simpa [prefixWord, tailWord_5509293, baseEnd_5509293] using wordTrace_append hprefix tailTrace_5509293
  have hstable : (prefixWord ++ tailWord_5509293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509293).length < 2 ^ (prefixWord ++ tailWord_5509293).sum := by decide
  have hdescent : baseEnd_5509293 < baseStart_5509293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509324 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5509324 : Nat := 118140960795 + 5509324 * 2 ^ 59
def prefixEnd_5509324 : Nat := 4983230072969 + 3 ^ 40 * 5509324 * 2
def baseEnd_5509324 : Nat := 2828931293351107978213087

theorem tailTrace_5509324 : CollatzResearch.WordTrace tailWord_5509324 prefixEnd_5509324 2828931293351107978213087 := by
  unfold tailWord_5509324
  simp only [CollatzResearch.WordTrace]
  refine ⟨100470777146333770237015513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133961036195111693649354017 100470777146333770237015513)
  ·
    refine ⟨75353082859750327677761635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100470777146333770237015513 75353082859750327677761635)
    ·
      refine ⟨113029624289625491516642453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75353082859750327677761635 113029624289625491516642453)
      ·
        refine ⟨5298263638576194914842615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113029624289625491516642453 5298263638576194914842615)
        ·
          refine ⟨7947395457864292372263923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5298263638576194914842615 7947395457864292372263923)
          ·
            refine ⟨11921093186796438558395885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7947395457864292372263923 11921093186796438558395885)
            ·
              refine ⟨4470409945048664459398457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11921093186796438558395885 4470409945048664459398457)
              ·
                refine ⟨3352807458786498344548843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470409945048664459398457 3352807458786498344548843)
                ·
                  refine ⟨5029211188179747516823265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352807458786498344548843 5029211188179747516823265)
                  ·
                    refine ⟨3771908391134810637617449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5029211188179747516823265 3771908391134810637617449)
                    ·
                      refine ⟨2828931293351107978213087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771908391134810637617449 2828931293351107978213087)
                      ·
                        rfl

theorem cell23_5509324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5509324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509324 prefixEnd_5509324 := by exact prefixLift 5509324
  have htrace : WordTrace (prefixWord ++ tailWord_5509324) baseStart_5509324 baseEnd_5509324 := by
    simpa [prefixWord, tailWord_5509324, baseEnd_5509324] using wordTrace_append hprefix tailTrace_5509324
  have hstable : (prefixWord ++ tailWord_5509324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509324).length < 2 ^ (prefixWord ++ tailWord_5509324).sum := by decide
  have hdescent : baseEnd_5509324 < baseStart_5509324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509349 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5509349 : Nat := 118140960795 + 5509349 * 2 ^ 59
def prefixEnd_5509349 : Nat := 4983230072969 + 3 ^ 40 * 5509349 * 2
def baseEnd_5509349 : Nat := 2828944130367470380400471

theorem tailTrace_5509349 : CollatzResearch.WordTrace tailWord_5509349 prefixEnd_5509349 2828944130367470380400471 := by
  unfold tailWord_5509349
  simp only [CollatzResearch.WordTrace]
  refine ⟨200942466117576969743691101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133961644078384646495794067 200942466117576969743691101)
  ·
    refine ⟨75353424794091363653884163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200942466117576969743691101 75353424794091363653884163)
    ·
      refine ⟨113030137191137045480826245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75353424794091363653884163 113030137191137045480826245)
      ·
        refine ⟨21193150723338196027654921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113030137191137045480826245 21193150723338196027654921)
        ·
          refine ⟨15894863042503647020741191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21193150723338196027654921 15894863042503647020741191)
          ·
            refine ⟨23842294563755470531111787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15894863042503647020741191 23842294563755470531111787)
            ·
              refine ⟨35763441845633205796667681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23842294563755470531111787 35763441845633205796667681)
              ·
                refine ⟨26822581384224904347500761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35763441845633205796667681 26822581384224904347500761)
                ·
                  refine ⟨20116936038168678260625571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26822581384224904347500761 20116936038168678260625571)
                  ·
                    refine ⟨30175404057253017390938357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20116936038168678260625571 30175404057253017390938357)
                    ·
                      refine ⟨2828944130367470380400471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30175404057253017390938357 2828944130367470380400471)
                      ·
                        rfl

theorem cell23_5509349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5509349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509349 prefixEnd_5509349 := by exact prefixLift 5509349
  have htrace : WordTrace (prefixWord ++ tailWord_5509349) baseStart_5509349 baseEnd_5509349 := by
    simpa [prefixWord, tailWord_5509349, baseEnd_5509349] using wordTrace_append hprefix tailTrace_5509349
  have hstable : (prefixWord ++ tailWord_5509349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509349).length < 2 ^ (prefixWord ++ tailWord_5509349).sum := by decide
  have hdescent : baseEnd_5509349 < baseStart_5509349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509379 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3]
def baseStart_5509379 : Nat := 118140960795 + 5509379 * 2 ^ 59
def prefixEnd_5509379 : Nat := 4983230072969 + 3 ^ 40 * 5509379 * 2
def baseEnd_5509379 : Nat := 2828959534787105263025333

theorem tailTrace_5509379 : CollatzResearch.WordTrace tailWord_5509379 prefixEnd_5509379 2828959534787105263025333 := by
  unfold tailWord_5509379
  simp only [CollatzResearch.WordTrace]
  refine ⟨200943560307468284867283191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133962373538312189911522127 200943560307468284867283191)
  ·
    refine ⟨301415340461202427300924787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200943560307468284867283191 301415340461202427300924787)
    ·
      refine ⟨452123010691803640951387181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301415340461202427300924787 452123010691803640951387181)
      ·
        refine ⟨169546129009426365356770193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452123010691803640951387181 169546129009426365356770193)
        ·
          refine ⟨127159596757069774017577645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169546129009426365356770193 127159596757069774017577645)
          ·
            refine ⟨47684848783901165256591617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127159596757069774017577645 47684848783901165256591617)
            ·
              refine ⟨35763636587925873942443713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47684848783901165256591617 35763636587925873942443713)
              ·
                refine ⟨26822727440944405456832785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35763636587925873942443713 26822727440944405456832785)
                ·
                  refine ⟨20117045580708304092624589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26822727440944405456832785 20117045580708304092624589)
                  ·
                    refine ⟨7543892092765614034734221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20117045580708304092624589 7543892092765614034734221)
                    ·
                      refine ⟨2828959534787105263025333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7543892092765614034734221 2828959534787105263025333)
                      ·
                        rfl

theorem cell23_5509379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_5509379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509379 prefixEnd_5509379 := by exact prefixLift 5509379
  have htrace : WordTrace (prefixWord ++ tailWord_5509379) baseStart_5509379 baseEnd_5509379 := by
    simpa [prefixWord, tailWord_5509379, baseEnd_5509379] using wordTrace_append hprefix tailTrace_5509379
  have hstable : (prefixWord ++ tailWord_5509379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509379).length < 2 ^ (prefixWord ++ tailWord_5509379).sum := by decide
  have hdescent : baseEnd_5509379 < baseStart_5509379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509416 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_5509416 : Nat := 118140960795 + 5509416 * 2 ^ 59
def prefixEnd_5509416 : Nat := 4983230072969 + 3 ^ 40 * 5509416 * 2
def baseEnd_5509416 : Nat := 942992844523773872754221

theorem tailTrace_5509416 : CollatzResearch.WordTrace tailWord_5509416 prefixEnd_5509416 942992844523773872754221 := by
  unfold tailWord_5509416
  simp only [CollatzResearch.WordTrace]
  refine ⟨100472454904167120093190051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133963273205556160124253401 100472454904167120093190051)
  ·
    refine ⟨150708682356250680139785077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100472454904167120093190051 150708682356250680139785077)
    ·
      refine ⟨14128938970898501263104851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150708682356250680139785077 14128938970898501263104851)
      ·
        refine ⟨21193408456347751894657277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14128938970898501263104851 21193408456347751894657277)
        ·
          refine ⟨7947528171130406960496479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21193408456347751894657277 7947528171130406960496479)
          ·
            refine ⟨11921292256695610440744719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7947528171130406960496479 11921292256695610440744719)
            ·
              refine ⟨17881938385043415661117079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11921292256695610440744719 17881938385043415661117079)
              ·
                refine ⟨26822907577565123491675619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17881938385043415661117079 26822907577565123491675619)
                ·
                  refine ⟨40234361366347685237513429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26822907577565123491675619 40234361366347685237513429)
                  ·
                    refine ⟨942992844523773872754221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40234361366347685237513429 942992844523773872754221)
                    ·
                      rfl

theorem cell23_5509416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_5509416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509416 prefixEnd_5509416 := by exact prefixLift 5509416
  have htrace : WordTrace (prefixWord ++ tailWord_5509416) baseStart_5509416 baseEnd_5509416 := by
    simpa [prefixWord, tailWord_5509416, baseEnd_5509416] using wordTrace_append hprefix tailTrace_5509416
  have hstable : (prefixWord ++ tailWord_5509416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509416).length < 2 ^ (prefixWord ++ tailWord_5509416).sum := by decide
  have hdescent : baseEnd_5509416 < baseStart_5509416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509436 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_5509436 : Nat := 118140960795 + 5509436 * 2 ^ 59
def prefixEnd_5509436 : Nat := 4983230072969 + 3 ^ 40 * 5509436 * 2
def baseEnd_5509436 : Nat := 2828988803184411540012571

theorem tailTrace_5509436 : CollatzResearch.WordTrace tailWord_5509436 prefixEnd_5509436 2828988803184411540012571 := by
  unfold tailWord_5509436
  simp only [CollatzResearch.WordTrace]
  refine ⟨100472819634130891801054081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133963759512174522401405441 100472819634130891801054081)
  ·
    refine ⟨75354614725598168850790561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100472819634130891801054081 75354614725598168850790561)
    ·
      refine ⟨56515961044198626638092921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75354614725598168850790561 56515961044198626638092921)
      ·
        refine ⟨42386970783148969978569691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56515961044198626638092921 42386970783148969978569691)
        ·
          refine ⟨63580456174723454967854537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42386970783148969978569691 63580456174723454967854537)
          ·
            refine ⟨47685342131042591225890903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63580456174723454967854537 47685342131042591225890903)
            ·
              refine ⟨71528013196563886838836355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47685342131042591225890903 71528013196563886838836355)
              ·
                refine ⟨107292019794845830258254533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71528013196563886838836355 107292019794845830258254533)
                ·
                  refine ⟨20117253711533593173422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107292019794845830258254533 20117253711533593173422725)
                  ·
                    refine ⟨3771985070912548720016761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20117253711533593173422725 3771985070912548720016761)
                    ·
                      refine ⟨2828988803184411540012571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3771985070912548720016761 2828988803184411540012571)
                      ·
                        rfl

theorem cell23_5509436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_5509436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509436 prefixEnd_5509436 := by exact prefixLift 5509436
  have htrace : WordTrace (prefixWord ++ tailWord_5509436) baseStart_5509436 baseEnd_5509436 := by
    simpa [prefixWord, tailWord_5509436, baseEnd_5509436] using wordTrace_append hprefix tailTrace_5509436
  have hstable : (prefixWord ++ tailWord_5509436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509436).length < 2 ^ (prefixWord ++ tailWord_5509436).sum := by decide
  have hdescent : baseEnd_5509436 < baseStart_5509436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509480 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 1, 4]
def baseStart_5509480 : Nat := 118140960795 + 5509480 * 2 ^ 59
def prefixEnd_5509480 : Nat := 4983230072969 + 3 ^ 40 * 5509480 * 2
def baseEnd_5509480 : Nat := 943003798777736455954123

theorem tailTrace_5509480 : CollatzResearch.WordTrace tailWord_5509480 prefixEnd_5509480 943003798777736455954123 := by
  unfold tailWord_5509480
  simp only [CollatzResearch.WordTrace]
  refine ⟨100473622040051189558354947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133964829386734919411139929 100473622040051189558354947)
  ·
    refine ⟨150710433060076784337532421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100473622040051189558354947 150710433060076784337532421)
    ·
      refine ⟨28258206198764397063287329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150710433060076784337532421 28258206198764397063287329)
      ·
        refine ⟨21193654649073297797465497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28258206198764397063287329 21193654649073297797465497)
        ·
          refine ⟨15895240986804973348099123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21193654649073297797465497 15895240986804973348099123)
          ·
            refine ⟨23842861480207460022148685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15895240986804973348099123 23842861480207460022148685)
            ·
              refine ⟨8941073055077797508305757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23842861480207460022148685 8941073055077797508305757)
              ·
                refine ⟨3352902395654174065614659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8941073055077797508305757 3352902395654174065614659)
                ·
                  refine ⟨5029353593481261098421989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352902395654174065614659 5029353593481261098421989)
                  ·
                    refine ⟨943003798777736455954123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5029353593481261098421989 943003798777736455954123)
                    ·
                      rfl

theorem cell23_5509480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_5509480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509480 prefixEnd_5509480 := by exact prefixLift 5509480
  have htrace : WordTrace (prefixWord ++ tailWord_5509480) baseStart_5509480 baseEnd_5509480 := by
    simpa [prefixWord, tailWord_5509480, baseEnd_5509480] using wordTrace_append hprefix tailTrace_5509480
  have hstable : (prefixWord ++ tailWord_5509480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509480).length < 2 ^ (prefixWord ++ tailWord_5509480).sum := by decide
  have hdescent : baseEnd_5509480 < baseStart_5509480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509489 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_5509489 : Nat := 118140960795 + 5509489 * 2 ^ 59
def prefixEnd_5509489 : Nat := 4983230072969 + 3 ^ 40 * 5509489 * 2
def baseEnd_5509489 : Nat := 943005339219699944216609

theorem tailTrace_5509489 : CollatzResearch.WordTrace tailWord_5509489 prefixEnd_5509489 943005339219699944216609 := by
  unfold tailWord_5509489
  simp only [CollatzResearch.WordTrace]
  refine ⟨200947572337069773653787521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133965048224713182435858347 200947572337069773653787521)
  ·
    refine ⟨150710679252802330240340641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200947572337069773653787521 150710679252802330240340641)
    ·
      refine ⟨113033009439601747680255481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150710679252802330240340641 113033009439601747680255481)
      ·
        refine ⟨84774757079701310760191611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113033009439601747680255481 84774757079701310760191611)
        ·
          refine ⟨127162135619551966140287417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84774757079701310760191611 127162135619551966140287417)
          ·
            refine ⟨95371601714663974605215563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127162135619551966140287417 95371601714663974605215563)
            ·
              refine ⟨143057402571995961907823345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95371601714663974605215563 143057402571995961907823345)
              ·
                refine ⟨107293051928996971430867509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143057402571995961907823345 107293051928996971430867509)
                ·
                  refine ⟨10058723618343466071643829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107293051928996971430867509 10058723618343466071643829)
                  ·
                    refine ⟨943005339219699944216609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10058723618343466071643829 943005339219699944216609)
                    ·
                      rfl

theorem cell23_5509489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_5509489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509489 prefixEnd_5509489 := by exact prefixLift 5509489
  have htrace : WordTrace (prefixWord ++ tailWord_5509489) baseStart_5509489 baseEnd_5509489 := by
    simpa [prefixWord, tailWord_5509489, baseEnd_5509489] using wordTrace_append hprefix tailTrace_5509489
  have hstable : (prefixWord ++ tailWord_5509489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509489).length < 2 ^ (prefixWord ++ tailWord_5509489).sum := by decide
  have hdescent : baseEnd_5509489 < baseStart_5509489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509509 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_5509509 : Nat := 118140960795 + 5509509 * 2 ^ 59
def prefixEnd_5509509 : Nat := 4983230072969 + 3 ^ 40 * 5509509 * 2
def baseEnd_5509509 : Nat := 2829026287272189754399735

theorem tailTrace_5509509 : CollatzResearch.WordTrace tailWord_5509509 prefixEnd_5509509 2829026287272189754399735 := by
  unfold tailWord_5509509
  simp only [CollatzResearch.WordTrace]
  refine ⟨200948301796997317069515581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133965534531331544713010387 200948301796997317069515581)
  ·
    refine ⟨75355613173873993901068343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200948301796997317069515581 75355613173873993901068343)
    ·
      refine ⟨113033419760810990851602515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75355613173873993901068343 113033419760810990851602515)
      ·
        refine ⟨169550129641216486277403773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113033419760810990851602515 169550129641216486277403773)
        ·
          refine ⟨63581298615456182354026415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169550129641216486277403773 63581298615456182354026415)
          ·
            refine ⟨95371947923184273531039623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63581298615456182354026415 95371947923184273531039623)
            ·
              refine ⟨143057921884776410296559435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95371947923184273531039623 143057921884776410296559435)
              ·
                refine ⟨214586882827164615444839153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143057921884776410296559435 214586882827164615444839153)
                ·
                  refine ⟨160940162120373461583629365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214586882827164615444839153 160940162120373461583629365)
                  ·
                    refine ⟨15088140198785012023465253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160940162120373461583629365 15088140198785012023465253)
                    ·
                      refine ⟨2829026287272189754399735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15088140198785012023465253 2829026287272189754399735)
                      ·
                        rfl

theorem cell23_5509509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_5509509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509509 prefixEnd_5509509 := by exact prefixLift 5509509
  have htrace : WordTrace (prefixWord ++ tailWord_5509509) baseStart_5509509 baseEnd_5509509 := by
    simpa [prefixWord, tailWord_5509509, baseEnd_5509509] using wordTrace_append hprefix tailTrace_5509509
  have hstable : (prefixWord ++ tailWord_5509509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509509).length < 2 ^ (prefixWord ++ tailWord_5509509).sum := by decide
  have hdescent : baseEnd_5509509 < baseStart_5509509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509530 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5509530 : Nat := 118140960795 + 5509530 * 2 ^ 59
def prefixEnd_5509530 : Nat := 4983230072969 + 3 ^ 40 * 5509530 * 2
def baseEnd_5509530 : Nat := 2829037070365934172237139

theorem tailTrace_5509530 : CollatzResearch.WordTrace tailWord_5509530 prefixEnd_5509530 2829037070365934172237139 := by
  unfold tailWord_5509530
  simp only [CollatzResearch.WordTrace]
  refine ⟨50237266932480309414007511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133966045153280825104020029 50237266932480309414007511)
  ·
    refine ⟨75355900398720464121011267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50237266932480309414007511 75355900398720464121011267)
    ·
      refine ⟨113033850598080696181516901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75355900398720464121011267 113033850598080696181516901)
      ·
        refine ⟨21193846987140130534034419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113033850598080696181516901 21193846987140130534034419)
        ·
          refine ⟨31790770480710195801051629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21193846987140130534034419 31790770480710195801051629)
          ·
            refine ⟨11921538930266323425394361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31790770480710195801051629 11921538930266323425394361)
            ·
              refine ⟨8941154197699742569045771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11921538930266323425394361 8941154197699742569045771)
              ·
                refine ⟨13411731296549613853568657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941154197699742569045771 13411731296549613853568657)
                ·
                  refine ⟨10058798472412210390176493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13411731296549613853568657 10058798472412210390176493)
                  ·
                    refine ⟨3772049427154578896316185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10058798472412210390176493 3772049427154578896316185)
                    ·
                      refine ⟨2829037070365934172237139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3772049427154578896316185 2829037070365934172237139)
                      ·
                        rfl

theorem cell23_5509530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5509530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509530 prefixEnd_5509530 := by exact prefixLift 5509530
  have htrace : WordTrace (prefixWord ++ tailWord_5509530) baseStart_5509530 baseEnd_5509530 := by
    simpa [prefixWord, tailWord_5509530, baseEnd_5509530] using wordTrace_append hprefix tailTrace_5509530
  have hstable : (prefixWord ++ tailWord_5509530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509530).length < 2 ^ (prefixWord ++ tailWord_5509530).sum := by decide
  have hdescent : baseEnd_5509530 < baseStart_5509530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509536 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_5509536 : Nat := 118140960795 + 5509536 * 2 ^ 59
def prefixEnd_5509536 : Nat := 4983230072969 + 3 ^ 40 * 5509536 * 2
def baseEnd_5509536 : Nat := 943013383749953716254037

theorem tailTrace_5509536 : CollatzResearch.WordTrace tailWord_5509536 prefixEnd_5509536 943013383749953716254037 := by
  unfold tailWord_5509536
  simp only [CollatzResearch.WordTrace]
  refine ⟨100474643283949750340374231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133966191045266333787165641 100474643283949750340374231)
  ·
    refine ⟨150711964925924625510561347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100474643283949750340374231 150711964925924625510561347)
    ·
      refine ⟨226067947388886938265842021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150711964925924625510561347 226067947388886938265842021)
      ·
        refine ⟨42387740135416300924845379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226067947388886938265842021 42387740135416300924845379)
        ·
          refine ⟨63581610203124451387268069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42387740135416300924845379 63581610203124451387268069)
          ·
            refine ⟨11921551913085834635112763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63581610203124451387268069 11921551913085834635112763)
            ·
              refine ⟨17882327869628751952669145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11921551913085834635112763 17882327869628751952669145)
              ·
                refine ⟨13411745902221563964501859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17882327869628751952669145 13411745902221563964501859)
                ·
                  refine ⟨20117618853332345946752789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13411745902221563964501859 20117618853332345946752789)
                  ·
                    refine ⟨943013383749953716254037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20117618853332345946752789 943013383749953716254037)
                    ·
                      rfl

theorem cell23_5509536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_5509536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509536 prefixEnd_5509536 := by exact prefixLift 5509536
  have htrace : WordTrace (prefixWord ++ tailWord_5509536) baseStart_5509536 baseEnd_5509536 := by
    simpa [prefixWord, tailWord_5509536, baseEnd_5509536] using wordTrace_append hprefix tailTrace_5509536
  have hstable : (prefixWord ++ tailWord_5509536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509536).length < 2 ^ (prefixWord ++ tailWord_5509536).sum := by decide
  have hdescent : baseEnd_5509536 < baseStart_5509536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509553 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_5509553 : Nat := 118140960795 + 5509553 * 2 ^ 59
def prefixEnd_5509553 : Nat := 4983230072969 + 3 ^ 40 * 5509553 * 2
def baseEnd_5509553 : Nat := 943016293473662527416511

theorem tailTrace_5509553 : CollatzResearch.WordTrace tailWord_5509553 prefixEnd_5509553 943016293473662527416511 := by
  unfold tailWord_5509553
  simp only [CollatzResearch.WordTrace]
  refine ⟨200949906608837912584117313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133966604405891941722744875 200949906608837912584117313)
  ·
    refine ⟨150712429956628434438087985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200949906608837912584117313 150712429956628434438087985)
    ·
      refine ⟨113034322467471325828565989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150712429956628434438087985 113034322467471325828565989)
      ·
        refine ⟨21193935462650873592856123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113034322467471325828565989 21193935462650873592856123)
        ·
          refine ⟨31790903193976310389284185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21193935462650873592856123 31790903193976310389284185)
          ·
            refine ⟨23843177395482232791963139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31790903193976310389284185 23843177395482232791963139)
            ·
              refine ⟨35764766093223349187944709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23843177395482232791963139 35764766093223349187944709)
              ·
                refine ⟨6705893642479377972739633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35764766093223349187944709 6705893642479377972739633)
                ·
                  refine ⟨5029420231859533479554725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6705893642479377972739633 5029420231859533479554725)
                  ·
                    refine ⟨943016293473662527416511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5029420231859533479554725 943016293473662527416511)
                    ·
                      rfl

theorem cell23_5509553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_5509553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509553 prefixEnd_5509553 := by exact prefixLift 5509553
  have htrace : WordTrace (prefixWord ++ tailWord_5509553) baseStart_5509553 baseEnd_5509553 := by
    simpa [prefixWord, tailWord_5509553, baseEnd_5509553] using wordTrace_append hprefix tailTrace_5509553
  have hstable : (prefixWord ++ tailWord_5509553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509553).length < 2 ^ (prefixWord ++ tailWord_5509553).sum := by decide
  have hdescent : baseEnd_5509553 < baseStart_5509553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509566 : List Nat := [4, 2, 1, 1, 1, 1, 5, 8]
def baseStart_5509566 : Nat := 118140960795 + 5509566 * 2 ^ 59
def prefixEnd_5509566 : Nat := 4983230072969 + 3 ^ 40 * 5509566 * 2
def baseEnd_5509566 : Nat := 104779835395166519680999

theorem tailTrace_5509566 : CollatzResearch.WordTrace tailWord_5509566 prefixEnd_5509566 104779835395166519680999 := by
  unfold tailWord_5509566
  simp only [CollatzResearch.WordTrace]
  refine ⟨25118797594723851975542569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133966920505193877202893701 25118797594723851975542569)
  ·
    refine ⟨18839098196042888981656927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25118797594723851975542569 18839098196042888981656927)
    ·
      refine ⟨28258647294064333472485391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18839098196042888981656927 28258647294064333472485391)
      ·
        refine ⟨42387970941096500208728087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28258647294064333472485391 42387970941096500208728087)
        ·
          refine ⟨63581956411644750313092131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42387970941096500208728087 63581956411644750313092131)
          ·
            refine ⟨95372934617467125469638197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63581956411644750313092131 95372934617467125469638197)
            ·
              refine ⟨8941212620387543012778581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95372934617467125469638197 8941212620387543012778581)
              ·
                refine ⟨104779835395166519680999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8941212620387543012778581 104779835395166519680999)
                ·
                  rfl

theorem cell23_5509566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_5509566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509566 prefixEnd_5509566 := by exact prefixLift 5509566
  have htrace : WordTrace (prefixWord ++ tailWord_5509566) baseStart_5509566 baseEnd_5509566 := by
    simpa [prefixWord, tailWord_5509566, baseEnd_5509566] using wordTrace_append hprefix tailTrace_5509566
  have hstable : (prefixWord ++ tailWord_5509566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509566).length < 2 ^ (prefixWord ++ tailWord_5509566).sum := by decide
  have hdescent : baseEnd_5509566 < baseStart_5509566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509579 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 7]
def baseStart_5509579 : Nat := 118140960795 + 5509579 * 2 ^ 59
def prefixEnd_5509579 : Nat := 4983230072969 + 3 ^ 40 * 5509579 * 2
def baseEnd_5509579 : Nat := 943020743639334826841471

theorem tailTrace_5509579 : CollatzResearch.WordTrace tailWord_5509579 prefixEnd_5509579 943020743639334826841471 := by
  unfold tailWord_5509579
  simp only [CollatzResearch.WordTrace]
  refine ⟨200950854906743719024563791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133967236604495812683042527 200950854906743719024563791)
  ·
    refine ⟨301426282360115578536845687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200950854906743719024563791 301426282360115578536845687)
    ·
      refine ⟨452139423540173367805268531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301426282360115578536845687 452139423540173367805268531)
      ·
        refine ⟨678209135310260051707902797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452139423540173367805268531 678209135310260051707902797)
        ·
          refine ⟨254328425741347519390463549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 678209135310260051707902797 254328425741347519390463549)
          ·
            refine ⟨95373159653005319771423831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254328425741347519390463549 95373159653005319771423831)
            ·
              refine ⟨143059739479507979657135747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95373159653005319771423831 143059739479507979657135747)
              ·
                refine ⟨214589609219261969485703621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143059739479507979657135747 214589609219261969485703621)
                ·
                  refine ⟨40235551728611619278569429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214589609219261969485703621 40235551728611619278569429)
                  ·
                    refine ⟨943020743639334826841471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40235551728611619278569429 943020743639334826841471)
                    ·
                      rfl

theorem cell23_5509579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_5509579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509579 prefixEnd_5509579 := by exact prefixLift 5509579
  have htrace : WordTrace (prefixWord ++ tailWord_5509579) baseStart_5509579 baseEnd_5509579 := by
    simpa [prefixWord, tailWord_5509579, baseEnd_5509579] using wordTrace_append hprefix tailTrace_5509579
  have hstable : (prefixWord ++ tailWord_5509579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509579).length < 2 ^ (prefixWord ++ tailWord_5509579).sum := by decide
  have hdescent : baseEnd_5509579 < baseStart_5509579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509593 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 3]
def baseStart_5509593 : Nat := 118140960795 + 5509593 * 2 ^ 59
def prefixEnd_5509593 : Nat := 4983230072969 + 3 ^ 40 * 5509593 * 2
def baseEnd_5509593 : Nat := 2829069419647167425749349

theorem tailTrace_5509593 : CollatzResearch.WordTrace tailWord_5509593 prefixEnd_5509593 2829069419647167425749349 := by
  unfold tailWord_5509593
  simp only [CollatzResearch.WordTrace]
  refine ⟨200951365528692999415573433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133967577019128666277048955 200951365528692999415573433)
  ·
    refine ⟨150713524146519749561680075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200951365528692999415573433 150713524146519749561680075)
    ·
      refine ⟨226070286219779624342520113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150713524146519749561680075 226070286219779624342520113)
      ·
        refine ⟨169552714664834718256890085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226070286219779624342520113 169552714664834718256890085)
        ·
          refine ⟨31791133999656509673166891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169552714664834718256890085 31791133999656509673166891)
          ·
            refine ⟨47686700999484764509750337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31791133999656509673166891 47686700999484764509750337)
            ·
              refine ⟨35765025749613573382312753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47686700999484764509750337 35765025749613573382312753)
              ·
                refine ⟨26823769312210180036734565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35765025749613573382312753 26823769312210180036734565)
                ·
                  refine ⟨5029456746039408756887731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26823769312210180036734565 5029456746039408756887731)
                  ·
                    refine ⟨7544185119059113135331597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029456746039408756887731 7544185119059113135331597)
                    ·
                      refine ⟨2829069419647167425749349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544185119059113135331597 2829069419647167425749349)
                      ·
                        rfl

theorem cell23_5509593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_5509593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509593 prefixEnd_5509593 := by exact prefixLift 5509593
  have htrace : WordTrace (prefixWord ++ tailWord_5509593) baseStart_5509593 baseEnd_5509593 := by
    simpa [prefixWord, tailWord_5509593, baseEnd_5509593] using wordTrace_append hprefix tailTrace_5509593
  have hstable : (prefixWord ++ tailWord_5509593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509593).length < 2 ^ (prefixWord ++ tailWord_5509593).sum := by decide
  have hdescent : baseEnd_5509593 < baseStart_5509593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509610 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_5509610 : Nat := 118140960795 + 5509610 * 2 ^ 59
def prefixEnd_5509610 : Nat := 4983230072969 + 3 ^ 40 * 5509610 * 2
def baseEnd_5509610 : Nat := 2829078148818293859236771

theorem tailTrace_5509610 : CollatzResearch.WordTrace tailWord_5509610 prefixEnd_5509610 2829078148818293859236771 := by
  unfold tailWord_5509610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50237996392407852829735571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133967990379754274212628189 50237996392407852829735571)
  ·
    refine ⟨75356994588611779244603357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50237996392407852829735571 75356994588611779244603357)
    ·
      refine ⟨28258872970729417216726259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75356994588611779244603357 28258872970729417216726259)
      ·
        refine ⟨42388309456094125825089389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28258872970729417216726259 42388309456094125825089389)
        ·
          refine ⟨15895616046035297184408521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42388309456094125825089389 15895616046035297184408521)
          ·
            refine ⟨11921712034526472888306391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15895616046035297184408521 11921712034526472888306391)
            ·
              refine ⟨17882568051789709332459587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11921712034526472888306391 17882568051789709332459587)
              ·
                refine ⟨26823852077684563998689381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17882568051789709332459587 26823852077684563998689381)
                ·
                  refine ⟨5029472264565855749754259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26823852077684563998689381 5029472264565855749754259)
                  ·
                    refine ⟨7544208396848783624631389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029472264565855749754259 7544208396848783624631389)
                    ·
                      refine ⟨2829078148818293859236771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544208396848783624631389 2829078148818293859236771)
                      ·
                        rfl

theorem cell23_5509610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_5509610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509610 prefixEnd_5509610 := by exact prefixLift 5509610
  have htrace : WordTrace (prefixWord ++ tailWord_5509610) baseStart_5509610 baseEnd_5509610 := by
    simpa [prefixWord, tailWord_5509610, baseEnd_5509610] using wordTrace_append hprefix tailTrace_5509610
  have hstable : (prefixWord ++ tailWord_5509610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509610).length < 2 ^ (prefixWord ++ tailWord_5509610).sum := by decide
  have hdescent : baseEnd_5509610 < baseStart_5509610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509666 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_5509666 : Nat := 118140960795 + 5509666 * 2 ^ 59
def prefixEnd_5509666 : Nat := 4983230072969 + 3 ^ 40 * 5509666 * 2
def baseEnd_5509666 : Nat := 2829106903734945640136513

theorem tailTrace_5509666 : CollatzResearch.WordTrace tailWord_5509666 prefixEnd_5509666 2829106903734945640136513 := by
  unfold tailWord_5509666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50238507014357133220745213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133969352038285688588653901 50238507014357133220745213)
  ·
    refine ⟨18839440130383924957779455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50238507014357133220745213 18839440130383924957779455)
    ·
      refine ⟨28259160195575887436669183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18839440130383924957779455 28259160195575887436669183)
      ·
        refine ⟨42388740293363831155003775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28259160195575887436669183 42388740293363831155003775)
        ·
          refine ⟨63583110440045746732505663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42388740293363831155003775 63583110440045746732505663)
          ·
            refine ⟨95374665660068620098758495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63583110440045746732505663 95374665660068620098758495)
            ·
              refine ⟨143061998490102930148137743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95374665660068620098758495 143061998490102930148137743)
              ·
                refine ⟨214592997735154395222206615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143061998490102930148137743 214592997735154395222206615)
                ·
                  refine ⟨321889496602731592833309923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214592997735154395222206615 321889496602731592833309923)
                  ·
                    refine ⟨482834244904097389249964885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321889496602731592833309923 482834244904097389249964885)
                    ·
                      refine ⟨2829106903734945640136513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 482834244904097389249964885 2829106903734945640136513)
                      ·
                        rfl

theorem cell23_5509666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_5509666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509666 prefixEnd_5509666 := by exact prefixLift 5509666
  have htrace : WordTrace (prefixWord ++ tailWord_5509666) baseStart_5509666 baseEnd_5509666 := by
    simpa [prefixWord, tailWord_5509666, baseEnd_5509666] using wordTrace_append hprefix tailTrace_5509666
  have hstable : (prefixWord ++ tailWord_5509666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509666).length < 2 ^ (prefixWord ++ tailWord_5509666).sum := by decide
  have hdescent : baseEnd_5509666 < baseStart_5509666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509703 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 2, 5]
def baseStart_5509703 : Nat := 118140960795 + 5509703 * 2 ^ 59
def prefixEnd_5509703 : Nat := 4983230072969 + 3 ^ 40 * 5509703 * 2
def baseEnd_5509703 : Nat := 943041967506387331791281

theorem tailTrace_5509703 : CollatzResearch.WordTrace tailWord_5509703 prefixEnd_5509703 943041967506387331791281 := by
  unfold tailWord_5509703
  simp only [CollatzResearch.WordTrace]
  refine ⟨200955377558294488202077763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133970251705529658801385175 200955377558294488202077763)
  ·
    refine ⟨301433066337441732303116645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200955377558294488202077763 301433066337441732303116645)
    ·
      refine ⟨56518699938270324806834371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301433066337441732303116645 56518699938270324806834371)
      ·
        refine ⟨84778049907405487210251557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56518699938270324806834371 84778049907405487210251557)
        ·
          refine ⟨15895884357638528851922167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84778049907405487210251557 15895884357638528851922167)
          ·
            refine ⟨23843826536457793277883251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15895884357638528851922167 23843826536457793277883251)
            ·
              refine ⟨35765739804686689916824877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23843826536457793277883251 35765739804686689916824877)
              ·
                refine ⟨13412152426757508718809329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35765739804686689916824877 13412152426757508718809329)
                ·
                  refine ⟨10059114320068131539106997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13412152426757508718809329 10059114320068131539106997)
                  ·
                    refine ⟨943041967506387331791281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10059114320068131539106997 943041967506387331791281)
                    ·
                      rfl

theorem cell23_5509703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_5509703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509703 prefixEnd_5509703 := by exact prefixLift 5509703
  have htrace : WordTrace (prefixWord ++ tailWord_5509703) baseStart_5509703 baseEnd_5509703 := by
    simpa [prefixWord, tailWord_5509703, baseEnd_5509703] using wordTrace_append hprefix tailTrace_5509703
  have hstable : (prefixWord ++ tailWord_5509703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509703).length < 2 ^ (prefixWord ++ tailWord_5509703).sum := by decide
  have hdescent : baseEnd_5509703 < baseStart_5509703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509724 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 5]
def baseStart_5509724 : Nat := 118140960795 + 5509724 * 2 ^ 59
def prefixEnd_5509724 : Nat := 4983230072969 + 3 ^ 40 * 5509724 * 2
def baseEnd_5509724 : Nat := 314348520623656268134583

theorem tailTrace_5509724 : CollatzResearch.WordTrace tailWord_5509724 prefixEnd_5509724 314348520623656268134583 := by
  unfold tailWord_5509724
  simp only [CollatzResearch.WordTrace]
  refine ⟨100478071745609204394296113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133970762327478939192394817 100478071745609204394296113)
  ·
    refine ⟨75358553809206903295722085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100478071745609204394296113 75358553809206903295722085)
    ·
      refine ⟨14129728839226294367947891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75358553809206903295722085 14129728839226294367947891)
      ·
        refine ⟨21194593258839441551921837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14129728839226294367947891 21194593258839441551921837)
        ·
          refine ⟨7947972472064790581970689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21194593258839441551921837 7947972472064790581970689)
          ·
            refine ⟨5960979354048592936478017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7947972472064790581970689 5960979354048592936478017)
            ·
              refine ⟨4470734515536444702358513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960979354048592936478017 4470734515536444702358513)
              ·
                refine ⟨3353050886652333526768885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470734515536444702358513 3353050886652333526768885)
                ·
                  refine ⟨314348520623656268134583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3353050886652333526768885 314348520623656268134583)
                  ·
                    rfl

theorem cell23_5509724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_5509724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509724 prefixEnd_5509724 := by exact prefixLift 5509724
  have htrace : WordTrace (prefixWord ++ tailWord_5509724) baseStart_5509724 baseEnd_5509724 := by
    simpa [prefixWord, tailWord_5509724, baseEnd_5509724] using wordTrace_append hprefix tailTrace_5509724
  have hstable : (prefixWord ++ tailWord_5509724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509724).length < 2 ^ (prefixWord ++ tailWord_5509724).sum := by decide
  have hdescent : baseEnd_5509724 < baseStart_5509724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509743 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_5509743 : Nat := 118140960795 + 5509743 * 2 ^ 59
def prefixEnd_5509743 : Nat := 4983230072969 + 3 ^ 40 * 5509743 * 2
def baseEnd_5509743 : Nat := 2829146441745341838873659

theorem tailTrace_5509743 : CollatzResearch.WordTrace tailWord_5509743 prefixEnd_5509743 2829146441745341838873659 := by
  unfold tailWord_5509743
  simp only [CollatzResearch.WordTrace]
  refine ⟨200956836478149575033533883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133971224318766383355689255 200956836478149575033533883)
  ·
    refine ⟨301435254717224362550300825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200956836478149575033533883 301435254717224362550300825)
    ·
      refine ⟨226076441037918271912725619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301435254717224362550300825 226076441037918271912725619)
      ·
        refine ⟨339114661556877407869088429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226076441037918271912725619 339114661556877407869088429)
        ·
          refine ⟨127167998083829027950908161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339114661556877407869088429 127167998083829027950908161)
          ·
            refine ⟨95375998562871770963181121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127167998083829027950908161 95375998562871770963181121)
            ·
              refine ⟨71531998922153828222385841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95375998562871770963181121 71531998922153828222385841)
              ·
                refine ⟨53648999191615371166789381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71531998922153828222385841 53648999191615371166789381)
                ·
                  refine ⟨10059187348427882093773009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53648999191615371166789381 10059187348427882093773009)
                  ·
                    refine ⟨7544390511320911570329757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10059187348427882093773009 7544390511320911570329757)
                    ·
                      refine ⟨2829146441745341838873659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544390511320911570329757 2829146441745341838873659)
                      ·
                        rfl

theorem cell23_5509743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_5509743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509743 prefixEnd_5509743 := by exact prefixLift 5509743
  have htrace : WordTrace (prefixWord ++ tailWord_5509743) baseStart_5509743 baseEnd_5509743 := by
    simpa [prefixWord, tailWord_5509743, baseEnd_5509743] using wordTrace_append hprefix tailTrace_5509743
  have hstable : (prefixWord ++ tailWord_5509743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509743).length < 2 ^ (prefixWord ++ tailWord_5509743).sum := by decide
  have hdescent : baseEnd_5509743 < baseStart_5509743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509757 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_5509757 : Nat := 118140960795 + 5509757 * 2 ^ 59
def prefixEnd_5509757 : Nat := 4983230072969 + 3 ^ 40 * 5509757 * 2
def baseEnd_5509757 : Nat := 2829153630474504784098595

theorem tailTrace_5509757 : CollatzResearch.WordTrace tailWord_5509757 prefixEnd_5509757 2829153630474504784098595 := by
  unfold tailWord_5509757
  simp only [CollatzResearch.WordTrace]
  refine ⟨200957347100098855424543525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133971564733399236949695683 200957347100098855424543525)
  ·
    refine ⟨37679502581268535392101911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200957347100098855424543525 37679502581268535392101911)
    ·
      refine ⟨56519253871902803088152867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37679502581268535392101911 56519253871902803088152867)
      ·
        refine ⟨84778880807854204632229301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56519253871902803088152867 84778880807854204632229301)
        ·
          refine ⟨7948020075736331684271497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84778880807854204632229301 7948020075736331684271497)
          ·
            refine ⟨5961015056802248763203623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948020075736331684271497 5961015056802248763203623)
            ·
              refine ⟨8941522585203373144805435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5961015056802248763203623 8941522585203373144805435)
              ·
                refine ⟨13412283877805059717208153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941522585203373144805435 13412283877805059717208153)
                ·
                  refine ⟨10059212908353794787906115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13412283877805059717208153 10059212908353794787906115)
                  ·
                    refine ⟨15088819362530692181859173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10059212908353794787906115 15088819362530692181859173)
                    ·
                      refine ⟨2829153630474504784098595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15088819362530692181859173 2829153630474504784098595)
                      ·
                        rfl

theorem cell23_5509757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_5509757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509757 prefixEnd_5509757 := by exact prefixLift 5509757
  have htrace : WordTrace (prefixWord ++ tailWord_5509757) baseStart_5509757 baseEnd_5509757 := by
    simpa [prefixWord, tailWord_5509757, baseEnd_5509757] using wordTrace_append hprefix tailTrace_5509757
  have hstable : (prefixWord ++ tailWord_5509757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509757).length < 2 ^ (prefixWord ++ tailWord_5509757).sum := by decide
  have hdescent : baseEnd_5509757 < baseStart_5509757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509760 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_5509760 : Nat := 118140960795 + 5509760 * 2 ^ 59
def prefixEnd_5509760 : Nat := 4983230072969 + 3 ^ 40 * 5509760 * 2
def baseEnd_5509760 : Nat := 2829155170916468272361081

theorem tailTrace_5509760 : CollatzResearch.WordTrace tailWord_5509760 prefixEnd_5509760 2829155170916468272361081 := by
  unfold tailWord_5509760
  simp only [CollatzResearch.WordTrace]
  refine ⟨100478728259543993468451367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133971637679391991291268489 100478728259543993468451367)
  ·
    refine ⟨150718092389315990202677051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100478728259543993468451367 150718092389315990202677051)
    ·
      refine ⟨226077138583973985304015577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150718092389315990202677051 226077138583973985304015577)
      ·
        refine ⟨169557853937980488978011683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226077138583973985304015577 169557853937980488978011683)
        ·
          refine ⟨254336780906970733467017525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169557853937980488978011683 254336780906970733467017525)
          ·
            refine ⟨23844073210028506262532893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254336780906970733467017525 23844073210028506262532893)
            ·
              refine ⟨8941527453760689848449835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23844073210028506262532893 8941527453760689848449835)
              ·
                refine ⟨13412291180641034772674753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8941527453760689848449835 13412291180641034772674753)
                ·
                  refine ⟨10059218385480776079506065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13412291180641034772674753 10059218385480776079506065)
                  ·
                    refine ⟨7544413789110582059629549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10059218385480776079506065 7544413789110582059629549)
                    ·
                      refine ⟨2829155170916468272361081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544413789110582059629549 2829155170916468272361081)
                      ·
                        rfl

theorem cell23_5509760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_5509760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509760 prefixEnd_5509760 := by exact prefixLift 5509760
  have htrace : WordTrace (prefixWord ++ tailWord_5509760) baseStart_5509760 baseEnd_5509760 := by
    simpa [prefixWord, tailWord_5509760, baseEnd_5509760] using wordTrace_append hprefix tailTrace_5509760
  have hstable : (prefixWord ++ tailWord_5509760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509760).length < 2 ^ (prefixWord ++ tailWord_5509760).sum := by decide
  have hdescent : baseEnd_5509760 < baseStart_5509760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509767 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 1, 4]
def baseStart_5509767 : Nat := 118140960795 + 5509767 * 2 ^ 59
def prefixEnd_5509767 : Nat := 4983230072969 + 3 ^ 40 * 5509767 * 2
def baseEnd_5509767 : Nat := 943052921760349914991183

theorem tailTrace_5509767 : CollatzResearch.WordTrace tailWord_5509767 prefixEnd_5509767 943052921760349914991183 := by
  unfold tailWord_5509767
  simp only [CollatzResearch.WordTrace]
  refine ⟨200957711830062627132407555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133971807886708418088271703 200957711830062627132407555)
  ·
    refine ⟨301436567745093940698611333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200957711830062627132407555 301436567745093940698611333)
    ·
      refine ⟨56519356452205113880989625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301436567745093940698611333 56519356452205113880989625)
      ·
        refine ⟨42389517339153835410742219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56519356452205113880989625 42389517339153835410742219)
        ·
          refine ⟨63584276008730753116113329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42389517339153835410742219 63584276008730753116113329)
          ·
            refine ⟨47688207006548064837084997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63584276008730753116113329 47688207006548064837084997)
            ·
              refine ⟨8941538813727762156953437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47688207006548064837084997 8941538813727762156953437)
              ·
                refine ⟨3353077055147910808857539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8941538813727762156953437 3353077055147910808857539)
                ·
                  refine ⟨5029615582721866213286309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353077055147910808857539 5029615582721866213286309)
                  ·
                    refine ⟨943052921760349914991183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5029615582721866213286309 943052921760349914991183)
                    ·
                      rfl

theorem cell23_5509767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_5509767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509767 prefixEnd_5509767 := by exact prefixLift 5509767
  have htrace : WordTrace (prefixWord ++ tailWord_5509767) baseStart_5509767 baseEnd_5509767 := by
    simpa [prefixWord, tailWord_5509767, baseEnd_5509767] using wordTrace_append hprefix tailTrace_5509767
  have hstable : (prefixWord ++ tailWord_5509767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509767).length < 2 ^ (prefixWord ++ tailWord_5509767).sum := by decide
  have hdescent : baseEnd_5509767 < baseStart_5509767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509780 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 8]
def baseStart_5509780 : Nat := 118140960795 + 5509780 * 2 ^ 59
def prefixEnd_5509780 : Nat := 4983230072969 + 3 ^ 40 * 5509780 * 2
def baseEnd_5509780 : Nat := 314351715614395354901221

theorem tailTrace_5509780 : CollatzResearch.WordTrace tailWord_5509780 prefixEnd_5509780 314351715614395354901221 := by
  unfold tailWord_5509780
  simp only [CollatzResearch.WordTrace]
  refine ⟨100479092989507765176315397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133972123986010353568420529 100479092989507765176315397)
  ·
    refine ⟨18839829935532705970559137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100479092989507765176315397 18839829935532705970559137)
    ·
      refine ⟨14129872451649529477919353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18839829935532705970559137 14129872451649529477919353)
      ·
        refine ⟨10597404338737147108439515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14129872451649529477919353 10597404338737147108439515)
        ·
          refine ⟨15896106508105720662659273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597404338737147108439515 15896106508105720662659273)
          ·
            refine ⟨11922079881079290496994455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15896106508105720662659273 11922079881079290496994455)
            ·
              refine ⟨17883119821618935745491683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11922079881079290496994455 17883119821618935745491683)
              ·
                refine ⟨26824679732428403618237525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17883119821618935745491683 26824679732428403618237525)
                ·
                  refine ⟨314351715614395354901221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26824679732428403618237525 314351715614395354901221)
                  ·
                    rfl

theorem cell23_5509780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_5509780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509780 prefixEnd_5509780 := by exact prefixLift 5509780
  have htrace : WordTrace (prefixWord ++ tailWord_5509780) baseStart_5509780 baseEnd_5509780 := by
    simpa [prefixWord, tailWord_5509780, baseEnd_5509780] using wordTrace_append hprefix tailTrace_5509780
  have hstable : (prefixWord ++ tailWord_5509780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509780).length < 2 ^ (prefixWord ++ tailWord_5509780).sum := by decide
  have hdescent : baseEnd_5509780 < baseStart_5509780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509824 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 1, 1, 3]
def baseStart_5509824 : Nat := 118140960795 + 5509824 * 2 ^ 59
def prefixEnd_5509824 : Nat := 4983230072969 + 3 ^ 40 * 5509824 * 2
def baseEnd_5509824 : Nat := 2829188033678356021960787

theorem tailTrace_5509824 : CollatzResearch.WordTrace tailWord_5509824 prefixEnd_5509824 2829188033678356021960787 := by
  unfold tailWord_5509824
  simp only [CollatzResearch.WordTrace]
  refine ⟨100479895395428062933616263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133973193860570750578155017 100479895395428062933616263)
  ·
    refine ⟨150719843093142094400424395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100479895395428062933616263 150719843093142094400424395)
    ·
      refine ⟨226079764639713141600636593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150719843093142094400424395 226079764639713141600636593)
      ·
        refine ⟨169559823479784856200477445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226079764639713141600636593 169559823479784856200477445)
        ·
          refine ⟨31792466902459660537589521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169559823479784856200477445 31792466902459660537589521)
          ·
            refine ⟨23844350176844745403192141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31792466902459660537589521 23844350176844745403192141)
            ·
              refine ⟨8941631316316779526197053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23844350176844745403192141 8941631316316779526197053)
              ·
                refine ⟨3353111743618792322323895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8941631316316779526197053 3353111743618792322323895)
                ·
                  refine ⟨5029667615428188483485843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3353111743618792322323895 5029667615428188483485843)
                  ·
                    refine ⟨7544501423142282725228765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5029667615428188483485843 7544501423142282725228765)
                    ·
                      refine ⟨2829188033678356021960787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544501423142282725228765 2829188033678356021960787)
                      ·
                        rfl

theorem cell23_5509824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_5509824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509824 prefixEnd_5509824 := by exact prefixLift 5509824
  have htrace : WordTrace (prefixWord ++ tailWord_5509824) baseStart_5509824 baseEnd_5509824 := by
    simpa [prefixWord, tailWord_5509824, baseEnd_5509824] using wordTrace_append hprefix tailTrace_5509824
  have hstable : (prefixWord ++ tailWord_5509824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509824).length < 2 ^ (prefixWord ++ tailWord_5509824).sum := by decide
  have hdescent : baseEnd_5509824 < baseStart_5509824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509850 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_5509850 : Nat := 118140960795 + 5509850 * 2 ^ 59
def prefixEnd_5509850 : Nat := 4983230072969 + 3 ^ 40 * 5509850 * 2
def baseEnd_5509850 : Nat := 2829201384175372920235667

theorem tailTrace_5509850 : CollatzResearch.WordTrace tailWord_5509850 prefixEnd_5509850 2829201384175372920235667 := by
  unfold tailWord_5509850
  simp only [CollatzResearch.WordTrace]
  refine ⟨50240184772190483076919751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133973826059174621538452669 50240184772190483076919751)
  ·
    refine ⟨75360277158285724615379627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50240184772190483076919751 75360277158285724615379627)
    ·
      refine ⟨113040415737428586923069441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75360277158285724615379627 113040415737428586923069441)
      ·
        refine ⟨84780311803071440192302081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113040415737428586923069441 84780311803071440192302081)
        ·
          refine ⟨63585233852303580144226561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84780311803071440192302081 63585233852303580144226561)
          ·
            refine ⟨47688925389227685108169921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63585233852303580144226561 47688925389227685108169921)
            ·
              refine ⟨35766694041920763831127441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47688925389227685108169921 35766694041920763831127441)
              ·
                refine ⟨26825020531440572873345581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35766694041920763831127441 26825020531440572873345581)
                ·
                  refine ⟨10059382699290214827504593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26825020531440572873345581 10059382699290214827504593)
                  ·
                    refine ⟨7544537024467661120628445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10059382699290214827504593 7544537024467661120628445)
                    ·
                      refine ⟨2829201384175372920235667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7544537024467661120628445 2829201384175372920235667)
                      ·
                        rfl

theorem cell23_5509850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_5509850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509850 prefixEnd_5509850 := by exact prefixLift 5509850
  have htrace : WordTrace (prefixWord ++ tailWord_5509850) baseStart_5509850 baseEnd_5509850 := by
    simpa [prefixWord, tailWord_5509850, baseEnd_5509850] using wordTrace_append hprefix tailTrace_5509850
  have hstable : (prefixWord ++ tailWord_5509850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509850).length < 2 ^ (prefixWord ++ tailWord_5509850).sum := by decide
  have hdescent : baseEnd_5509850 < baseStart_5509850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5509857 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_5509857 : Nat := 118140960795 + 5509857 * 2 ^ 59
def prefixEnd_5509857 : Nat := 4983230072969 + 3 ^ 40 * 5509857 * 2
def baseEnd_5509857 : Nat := 943068326179984797616045

theorem tailTrace_5509857 : CollatzResearch.WordTrace tailWord_5509857 prefixEnd_5509857 943068326179984797616045 := by
  unfold tailWord_5509857
  simp only [CollatzResearch.WordTrace]
  refine ⟨200960994399736572503183825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133973996266491048335455883 200960994399736572503183825)
  ·
    refine ⟨150720745799802429377387869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200960994399736572503183825 150720745799802429377387869)
    ·
      refine ⟨56520279674925911016520451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150720745799802429377387869 56520279674925911016520451)
      ·
        refine ⟨84780419512388866524780677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56520279674925911016520451 84780419512388866524780677)
        ·
          refine ⟨15896328658572912473396377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84780419512388866524780677 15896328658572912473396377)
          ·
            refine ⟨11922246493929684355047283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15896328658572912473396377 11922246493929684355047283)
            ·
              refine ⟨17883369740894526532570925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11922246493929684355047283 17883369740894526532570925)
              ·
                refine ⟨6706263652835447449714097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17883369740894526532570925 6706263652835447449714097)
                ·
                  refine ⟨5029697739626585587285573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6706263652835447449714097 5029697739626585587285573)
                  ·
                    refine ⟨943068326179984797616045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5029697739626585587285573 943068326179984797616045)
                    ·
                      rfl

theorem cell23_5509857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_5509857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5509857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5509857 prefixEnd_5509857 := by exact prefixLift 5509857
  have htrace : WordTrace (prefixWord ++ tailWord_5509857) baseStart_5509857 baseEnd_5509857 := by
    simpa [prefixWord, tailWord_5509857, baseEnd_5509857] using wordTrace_append hprefix tailTrace_5509857
  have hstable : (prefixWord ++ tailWord_5509857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5509857).length < 2 ^ (prefixWord ++ tailWord_5509857).sum := by decide
  have hdescent : baseEnd_5509857 < baseStart_5509857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5509857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
