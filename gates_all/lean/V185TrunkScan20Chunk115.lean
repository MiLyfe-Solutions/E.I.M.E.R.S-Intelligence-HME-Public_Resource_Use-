import V185TrunkScan20Chunk114

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_699130 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_699130 : Nat := 118140960795 + 699130 * 2 ^ 59
def prefixEnd_699130 : Nat := 4983230072969 + 3 ^ 40 * 699130 * 2
def baseEnd_699130 : Nat := 319101982202626563875347

theorem tailTrace_699130 : CollatzResearch.WordTrace tailWord_699130 prefixEnd_699130 319101982202626563875347 := by
  unfold tailWord_699130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374841489294721685759711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16999577304785924495359229 6374841489294721685759711)
  ·
    refine ⟨9562262233942082528639567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6374841489294721685759711 9562262233942082528639567)
    ·
      refine ⟨14343393350913123792959351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9562262233942082528639567 14343393350913123792959351)
      ·
        refine ⟨21515090026369685689439027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14343393350913123792959351 21515090026369685689439027)
        ·
          refine ⟨32272635039554528534158541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21515090026369685689439027 32272635039554528534158541)
          ·
            refine ⟨12102238139832948200309453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32272635039554528534158541 12102238139832948200309453)
            ·
              refine ⟨4538339302437355575116045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12102238139832948200309453 4538339302437355575116045)
              ·
                refine ⟨1701877238414008340668517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4538339302437355575116045 1701877238414008340668517)
                ·
                  refine ⟨319101982202626563875347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701877238414008340668517 319101982202626563875347)
                  ·
                    rfl

theorem cell20_699130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_699130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699130 prefixEnd_699130 := by exact prefixLift 699130
  have htrace : WordTrace (prefixWord ++ tailWord_699130) baseStart_699130 baseEnd_699130 := by
    simpa [prefixWord, tailWord_699130, baseEnd_699130] using wordTrace_append hprefix tailTrace_699130
  have hstable : (prefixWord ++ tailWord_699130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699130).length < 2 ^ (prefixWord ++ tailWord_699130).sum := by decide
  have hdescent : baseEnd_699130 < baseStart_699130 := by decide
  rcases family_descends (prefixWord ++ tailWord_699130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699137 : List Nat := [1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_699137 : Nat := 118140960795 + 699137 * 2 ^ 59
def prefixEnd_699137 : Nat := 4983230072969 + 3 ^ 40 * 699137 * 2
def baseEnd_699137 : Nat := 106368392397788550213995

theorem tailTrace_699137 : CollatzResearch.WordTrace tailWord_699137 prefixEnd_699137 106368392397788550213995 := by
  unfold tailWord_699137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25499621268153526938543665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16999747512102351292362443 25499621268153526938543665)
  ·
    refine ⟨19124715951115145203907749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25499621268153526938543665 19124715951115145203907749)
    ·
      refine ⟨3585884240834089725732703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19124715951115145203907749 3585884240834089725732703)
      ·
        refine ⟨5378826361251134588599055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585884240834089725732703 5378826361251134588599055)
        ·
          refine ⟨8068239541876701882898583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378826361251134588599055 8068239541876701882898583)
          ·
            refine ⟨12102359312815052824347875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8068239541876701882898583 12102359312815052824347875)
            ·
              refine ⟨18153538969222579236521813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12102359312815052824347875 18153538969222579236521813)
              ·
                refine ⟨106368392397788550213995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18153538969222579236521813 106368392397788550213995)
                ·
                  rfl

theorem cell20_699137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_699137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699137 prefixEnd_699137 := by exact prefixLift 699137
  have htrace : WordTrace (prefixWord ++ tailWord_699137) baseStart_699137 baseEnd_699137 := by
    simpa [prefixWord, tailWord_699137, baseEnd_699137] using wordTrace_append hprefix tailTrace_699137
  have hstable : (prefixWord ++ tailWord_699137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699137).length < 2 ^ (prefixWord ++ tailWord_699137).sum := by decide
  have hdescent : baseEnd_699137 < baseStart_699137 := by decide
  rcases family_descends (prefixWord ++ tailWord_699137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699164 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_699164 : Nat := 118140960795 + 699164 * 2 ^ 59
def prefixEnd_699164 : Nat := 4983230072969 + 3 ^ 40 * 699164 * 2
def baseEnd_699164 : Nat := 319117500729073556741875

theorem tailTrace_699164 : CollatzResearch.WordTrace tailWord_699164 prefixEnd_699164 319117500729073556741875 := by
  unfold tailWord_699164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750303019527855274888273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17000404026037140366517697 12750303019527855274888273)
  ·
    refine ⟨9562727264645891456166205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12750303019527855274888273 9562727264645891456166205)
    ·
      refine ⟨3586022724242209296062327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9562727264645891456166205 3586022724242209296062327)
      ·
        refine ⟨5379034086363313944093491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586022724242209296062327 5379034086363313944093491)
        ·
          refine ⟨8068551129544970916140237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379034086363313944093491 8068551129544970916140237)
          ·
            refine ⟨3025706673579364093552589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8068551129544970916140237 3025706673579364093552589)
            ·
              refine ⟨1134640002592261535082221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3025706673579364093552589 1134640002592261535082221)
              ·
                refine ⟨425490000972098075655833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1134640002592261535082221 425490000972098075655833)
                ·
                  refine ⟨319117500729073556741875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425490000972098075655833 319117500729073556741875)
                  ·
                    rfl

theorem cell20_699164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_699164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699164 prefixEnd_699164 := by exact prefixLift 699164
  have htrace : WordTrace (prefixWord ++ tailWord_699164) baseStart_699164 baseEnd_699164 := by
    simpa [prefixWord, tailWord_699164, baseEnd_699164] using wordTrace_append hprefix tailTrace_699164
  have hstable : (prefixWord ++ tailWord_699164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699164).length < 2 ^ (prefixWord ++ tailWord_699164).sum := by decide
  have hdescent : baseEnd_699164 < baseStart_699164 := by decide
  rcases family_descends (prefixWord ++ tailWord_699164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699237 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_699237 : Nat := 118140960795 + 699237 * 2 ^ 59
def prefixEnd_699237 : Nat := 4983230072969 + 3 ^ 40 * 699237 * 2
def baseEnd_699237 : Nat := 319150819918209747308243

theorem tailTrace_699237 : CollatzResearch.WordTrace tailWord_699237 prefixEnd_699237 319150819918209747308243 := by
  unfold tailWord_699237
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503268567791244017183965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002179045194162678122643 25503268567791244017183965)
  ·
    refine ⟨9563725712921716506443987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25503268567791244017183965 9563725712921716506443987)
    ·
      refine ⟨14345588569382574759665981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9563725712921716506443987 14345588569382574759665981)
      ·
        refine ⟨5379595713518465534874743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14345588569382574759665981 5379595713518465534874743)
        ·
          refine ⟨8069393570277698302312115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379595713518465534874743 8069393570277698302312115)
          ·
            refine ⟨12104090355416547453468173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8069393570277698302312115 12104090355416547453468173)
            ·
              refine ⟨4539033883281205295050565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12104090355416547453468173 4539033883281205295050565)
              ·
                refine ⟨851068853115225992821981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4539033883281205295050565 851068853115225992821981)
                ·
                  refine ⟨319150819918209747308243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851068853115225992821981 319150819918209747308243)
                  ·
                    rfl

theorem cell20_699237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_699237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699237 prefixEnd_699237 := by exact prefixLift 699237
  have htrace : WordTrace (prefixWord ++ tailWord_699237) baseStart_699237 baseEnd_699237 := by
    simpa [prefixWord, tailWord_699237, baseEnd_699237] using wordTrace_append hprefix tailTrace_699237
  have hstable : (prefixWord ++ tailWord_699237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699237).length < 2 ^ (prefixWord ++ tailWord_699237).sum := by decide
  have hdescent : baseEnd_699237 < baseStart_699237 := by decide
  rcases family_descends (prefixWord ++ tailWord_699237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699240 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_699240 : Nat := 118140960795 + 699240 * 2 ^ 59
def prefixEnd_699240 : Nat := 4983230072969 + 3 ^ 40 * 699240 * 2
def baseEnd_699240 : Nat := 319152189199955070208231

theorem tailTrace_699240 : CollatzResearch.WordTrace tailWord_699240 prefixEnd_699240 319152189199955070208231 := by
  unfold tailWord_699240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12751688993390187764771587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17002251991186917019695449 12751688993390187764771587)
  ·
    refine ⟨19127533490085281647157381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12751688993390187764771587 19127533490085281647157381)
    ·
      refine ⟨3586412529390990308842009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19127533490085281647157381 3586412529390990308842009)
      ·
        refine ⟨2689809397043242731631507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3586412529390990308842009 2689809397043242731631507)
        ·
          refine ⟨4034714095564864097447261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689809397043242731631507 4034714095564864097447261)
          ·
            refine ⟨1513017785836824036542723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4034714095564864097447261 1513017785836824036542723)
            ·
              refine ⟨2269526678755236054814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513017785836824036542723 2269526678755236054814085)
              ·
                refine ⟨425536252266606760277641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2269526678755236054814085 425536252266606760277641)
                ·
                  refine ⟨319152189199955070208231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425536252266606760277641 319152189199955070208231)
                  ·
                    rfl

theorem cell20_699240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_699240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699240 prefixEnd_699240 := by exact prefixLift 699240
  have htrace : WordTrace (prefixWord ++ tailWord_699240) baseStart_699240 baseEnd_699240 := by
    simpa [prefixWord, tailWord_699240, baseEnd_699240] using wordTrace_append hprefix tailTrace_699240
  have hstable : (prefixWord ++ tailWord_699240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699240).length < 2 ^ (prefixWord ++ tailWord_699240).sum := by decide
  have hdescent : baseEnd_699240 < baseStart_699240 := by decide
  rcases family_descends (prefixWord ++ tailWord_699240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699244 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_699244 : Nat := 118140960795 + 699244 * 2 ^ 59
def prefixEnd_699244 : Nat := 4983230072969 + 3 ^ 40 * 699244 * 2
def baseEnd_699244 : Nat := 319154014908948834074881

theorem tailTrace_699244 : CollatzResearch.WordTrace tailWord_699244 prefixEnd_699244 319154014908948834074881 := by
  unfold tailWord_699244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12751761939382942106344393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17002349252510589475125857 12751761939382942106344393)
  ·
    refine ⟨9563821454537206579758295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12751761939382942106344393 9563821454537206579758295)
    ·
      refine ⟨14345732181805809869637443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9563821454537206579758295 14345732181805809869637443)
      ·
        refine ⟨21518598272708714804456165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345732181805809869637443 21518598272708714804456165)
        ·
          refine ⟨4034737176132884025835531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21518598272708714804456165 4034737176132884025835531)
          ·
            refine ⟨6052105764199326038753297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034737176132884025835531 6052105764199326038753297)
            ·
              refine ⟨4539079323149494529064973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6052105764199326038753297 4539079323149494529064973)
              ·
                refine ⟨1702154746181060448399365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4539079323149494529064973 1702154746181060448399365)
                ·
                  refine ⟨319154014908948834074881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702154746181060448399365 319154014908948834074881)
                  ·
                    rfl

theorem cell20_699244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_699244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699244 prefixEnd_699244 := by exact prefixLift 699244
  have htrace : WordTrace (prefixWord ++ tailWord_699244) baseStart_699244 baseEnd_699244 := by
    simpa [prefixWord, tailWord_699244, baseEnd_699244] using wordTrace_append hprefix tailTrace_699244
  have hstable : (prefixWord ++ tailWord_699244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699244).length < 2 ^ (prefixWord ++ tailWord_699244).sum := by decide
  have hdescent : baseEnd_699244 < baseStart_699244 := by decide
  rcases family_descends (prefixWord ++ tailWord_699244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699251 : List Nat := [1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_699251 : Nat := 118140960795 + 699251 * 2 ^ 59
def prefixEnd_699251 : Nat := 4983230072969 + 3 ^ 40 * 699251 * 2
def baseEnd_699251 : Nat := 106385736633229306947173

theorem tailTrace_699251 : CollatzResearch.WordTrace tailWord_699251 prefixEnd_699251 106385736633229306947173 := by
  unfold tailWord_699251
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503779189740524408193607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002519459827016272129071 25503779189740524408193607)
  ·
    refine ⟨38255668784610786612290411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25503779189740524408193607 38255668784610786612290411)
    ·
      refine ⟨57383503176916179918435617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38255668784610786612290411 57383503176916179918435617)
      ·
        refine ⟨43037627382687134938826713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57383503176916179918435617 43037627382687134938826713)
        ·
          refine ⟨32278220537015351204120035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43037627382687134938826713 32278220537015351204120035)
          ·
            refine ⟨48417330805523026806180053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32278220537015351204120035 48417330805523026806180053)
            ·
              refine ⟨1134781190754445940769845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48417330805523026806180053 1134781190754445940769845)
              ·
                refine ⟨106385736633229306947173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1134781190754445940769845 106385736633229306947173)
                ·
                  rfl

theorem cell20_699251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_699251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699251 prefixEnd_699251 := by exact prefixLift 699251
  have htrace : WordTrace (prefixWord ++ tailWord_699251) baseStart_699251 baseEnd_699251 := by
    simpa [prefixWord, tailWord_699251, baseEnd_699251] using wordTrace_append hprefix tailTrace_699251
  have hstable : (prefixWord ++ tailWord_699251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699251).length < 2 ^ (prefixWord ++ tailWord_699251).sum := by decide
  have hdescent : baseEnd_699251 < baseStart_699251 := by decide
  rcases family_descends (prefixWord ++ tailWord_699251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699258 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_699258 : Nat := 118140960795 + 699258 * 2 ^ 59
def prefixEnd_699258 : Nat := 4983230072969 + 3 ^ 40 * 699258 * 2
def baseEnd_699258 : Nat := 319160404890427007608157

theorem tailTrace_699258 : CollatzResearch.WordTrace tailWord_699258 prefixEnd_699258 319160404890427007608157 := by
  unfold tailWord_699258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376008625178791150924607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17002689667143443069132285 6376008625178791150924607)
  ·
    refine ⟨9564012937768186726386911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376008625178791150924607 9564012937768186726386911)
    ·
      refine ⟨14346019406652280089580367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9564012937768186726386911 14346019406652280089580367)
      ·
        refine ⟨21519029109978420134370551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14346019406652280089580367 21519029109978420134370551)
        ·
          refine ⟨32278543664967630201555827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21519029109978420134370551 32278543664967630201555827)
          ·
            refine ⟨48417815497451445302333741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32278543664967630201555827 48417815497451445302333741)
            ·
              refine ⟨18156680811544291988375153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48417815497451445302333741 18156680811544291988375153)
              ·
                refine ⟨13617510608658218991281365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18156680811544291988375153 13617510608658218991281365)
                ·
                  refine ⟨319160404890427007608157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13617510608658218991281365 319160404890427007608157)
                  ·
                    rfl

theorem cell20_699258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_699258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699258 prefixEnd_699258 := by exact prefixLift 699258
  have htrace : WordTrace (prefixWord ++ tailWord_699258) baseStart_699258 baseEnd_699258 := by
    simpa [prefixWord, tailWord_699258, baseEnd_699258] using wordTrace_append hprefix tailTrace_699258
  have hstable : (prefixWord ++ tailWord_699258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699258).length < 2 ^ (prefixWord ++ tailWord_699258).sum := by decide
  have hdescent : baseEnd_699258 < baseStart_699258 := by decide
  rcases family_descends (prefixWord ++ tailWord_699258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699292 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_699292 : Nat := 118140960795 + 699292 * 2 ^ 59
def prefixEnd_699292 : Nat := 4983230072969 + 3 ^ 40 * 699292 * 2
def baseEnd_699292 : Nat := 319175923416874000474685

theorem tailTrace_699292 : CollatzResearch.WordTrace tailWord_699292 prefixEnd_699292 319175923416874000474685 := by
  unfold tailWord_699292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12752637291295994205218065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17003516388394658940290753 12752637291295994205218065)
  ·
    refine ⟨9564477968471995653913549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12752637291295994205218065 9564477968471995653913549)
    ·
      refine ⟨3586679238176998370217581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9564477968471995653913549 3586679238176998370217581)
      ·
        refine ⟨1345004714316374388831593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3586679238176998370217581 1345004714316374388831593)
        ·
          refine ⟨1008753535737280791623695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345004714316374388831593 1008753535737280791623695)
          ·
            refine ⟨1513130303605921187435543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008753535737280791623695 1513130303605921187435543)
            ·
              refine ⟨2269695455408881781153315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513130303605921187435543 2269695455408881781153315)
              ·
                refine ⟨3404543183113322671729973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269695455408881781153315 3404543183113322671729973)
                ·
                  refine ⟨319175923416874000474685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3404543183113322671729973 319175923416874000474685)
                  ·
                    rfl

theorem cell20_699292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_699292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699292 prefixEnd_699292 := by exact prefixLift 699292
  have htrace : WordTrace (prefixWord ++ tailWord_699292) baseStart_699292 baseEnd_699292 := by
    simpa [prefixWord, tailWord_699292, baseEnd_699292] using wordTrace_append hprefix tailTrace_699292
  have hstable : (prefixWord ++ tailWord_699292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699292).length < 2 ^ (prefixWord ++ tailWord_699292).sum := by decide
  have hdescent : baseEnd_699292 < baseStart_699292 := by decide
  rcases family_descends (prefixWord ++ tailWord_699292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699299 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 2]
def baseStart_699299 : Nat := 118140960795 + 699299 * 2 ^ 59
def prefixEnd_699299 : Nat := 4983230072969 + 3 ^ 40 * 699299 * 2
def baseEnd_699299 : Nat := 319179118407613087241323

theorem tailTrace_699299 : CollatzResearch.WordTrace tailWord_699299 prefixEnd_699299 319179118407613087241323 := by
  unfold tailWord_699299
  simp only [CollatzResearch.WordTrace]
  refine ⟨25505529893566628605940951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17003686595711085737293967 25505529893566628605940951)
  ·
    refine ⟨38258294840349942908911427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25505529893566628605940951 38258294840349942908911427)
    ·
      refine ⟨57387442260524914363367141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38258294840349942908911427 57387442260524914363367141)
      ·
        refine ⟨10760145423848421443131339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57387442260524914363367141 10760145423848421443131339)
        ·
          refine ⟨16140218135772632164697009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760145423848421443131339 16140218135772632164697009)
          ·
            refine ⟨12105163601829474123522757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16140218135772632164697009 12105163601829474123522757)
            ·
              refine ⟨2269718175343026398160517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12105163601829474123522757 2269718175343026398160517)
              ·
                refine ⟨425572157876817449655097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2269718175343026398160517 425572157876817449655097)
                ·
                  refine ⟨319179118407613087241323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425572157876817449655097 319179118407613087241323)
                  ·
                    rfl

theorem cell20_699299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2].length) (baseStart_699299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699299 prefixEnd_699299 := by exact prefixLift 699299
  have htrace : WordTrace (prefixWord ++ tailWord_699299) baseStart_699299 baseEnd_699299 := by
    simpa [prefixWord, tailWord_699299, baseEnd_699299] using wordTrace_append hprefix tailTrace_699299
  have hstable : (prefixWord ++ tailWord_699299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699299).length < 2 ^ (prefixWord ++ tailWord_699299).sum := by decide
  have hdescent : baseEnd_699299 < baseStart_699299 := by decide
  rcases family_descends (prefixWord ++ tailWord_699299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699316 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_699316 : Nat := 118140960795 + 699316 * 2 ^ 59
def prefixEnd_699316 : Nat := 4983230072969 + 3 ^ 40 * 699316 * 2
def baseEnd_699316 : Nat := 319186877670836583674587

theorem tailTrace_699316 : CollatzResearch.WordTrace tailWord_699316 prefixEnd_699316 319186877670836583674587 := by
  unfold tailWord_699316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753074967252520254654901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17004099956336693672873201 12753074967252520254654901)
  ·
    refine ⟨1195600778179923773873897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12753074967252520254654901 1195600778179923773873897)
    ·
      refine ⟨896700583634942830405423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1195600778179923773873897 896700583634942830405423)
      ·
        refine ⟨1345050875452414245608135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896700583634942830405423 1345050875452414245608135)
        ·
          refine ⟨2017576313178621368412203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345050875452414245608135 2017576313178621368412203)
          ·
            refine ⟨3026364469767932052618305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017576313178621368412203 3026364469767932052618305)
            ·
              refine ⟨2269773352325949039463729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026364469767932052618305 2269773352325949039463729)
              ·
                refine ⟨1702330014244461779597797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269773352325949039463729 1702330014244461779597797)
                ·
                  refine ⟨319186877670836583674587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702330014244461779597797 319186877670836583674587)
                  ·
                    rfl

theorem cell20_699316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_699316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699316 prefixEnd_699316 := by exact prefixLift 699316
  have htrace : WordTrace (prefixWord ++ tailWord_699316) baseStart_699316 baseEnd_699316 := by
    simpa [prefixWord, tailWord_699316, baseEnd_699316] using wordTrace_append hprefix tailTrace_699316
  have hstable : (prefixWord ++ tailWord_699316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699316).length < 2 ^ (prefixWord ++ tailWord_699316).sum := by decide
  have hdescent : baseEnd_699316 < baseStart_699316 := by decide
  rcases family_descends (prefixWord ++ tailWord_699316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699320 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_699320 : Nat := 118140960795 + 699320 * 2 ^ 59
def prefixEnd_699320 : Nat := 4983230072969 + 3 ^ 40 * 699320 * 2
def baseEnd_699320 : Nat := 319188703379830347541237

theorem tailTrace_699320 : CollatzResearch.WordTrace tailWord_699320 prefixEnd_699320 319188703379830347541237 := by
  unfold tailWord_699320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753147913245274596227707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17004197217660366128303609 12753147913245274596227707)
  ·
    refine ⟨19129721869867911894341561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12753147913245274596227707 19129721869867911894341561)
    ·
      refine ⟨14347291402400933920756171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19129721869867911894341561 14347291402400933920756171)
      ·
        refine ⟨21520937103601400881134257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14347291402400933920756171 21520937103601400881134257)
        ·
          refine ⟨16140702827701050660850693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21520937103601400881134257 16140702827701050660850693)
          ·
            refine ⟨3026381780193946998909505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16140702827701050660850693 3026381780193946998909505)
            ·
              refine ⟨2269786335145460249182129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026381780193946998909505 2269786335145460249182129)
              ·
                refine ⟨1702339751359095186886597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269786335145460249182129 1702339751359095186886597)
                ·
                  refine ⟨319188703379830347541237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702339751359095186886597 319188703379830347541237)
                  ·
                    rfl

theorem cell20_699320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_699320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699320 prefixEnd_699320 := by exact prefixLift 699320
  have htrace : WordTrace (prefixWord ++ tailWord_699320) baseStart_699320 baseEnd_699320 := by
    simpa [prefixWord, tailWord_699320, baseEnd_699320] using wordTrace_append hprefix tailTrace_699320
  have hstable : (prefixWord ++ tailWord_699320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699320).length < 2 ^ (prefixWord ++ tailWord_699320).sum := by decide
  have hdescent : baseEnd_699320 < baseStart_699320 := by decide
  rcases family_descends (prefixWord ++ tailWord_699320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699350 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_699350 : Nat := 118140960795 + 699350 * 2 ^ 59
def prefixEnd_699350 : Nat := 4983230072969 + 3 ^ 40 * 699350 * 2
def baseEnd_699350 : Nat := 319202396197283576541115

theorem tailTrace_699350 : CollatzResearch.WordTrace tailWord_699350 prefixEnd_699350 319202396197283576541115 := by
  unfold tailWord_699350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594211876023866519752969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17004926677587909544031669 1594211876023866519752969)
  ·
    refine ⟨1195658907017899889814727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1594211876023866519752969 1195658907017899889814727)
    ·
      refine ⟨1793488360526849834722091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195658907017899889814727 1793488360526849834722091)
      ·
        refine ⟨2690232540790274752083137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793488360526849834722091 2690232540790274752083137)
        ·
          refine ⟨2017674405592706064062353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2690232540790274752083137 2017674405592706064062353)
          ·
            refine ⟨1513255804194529548046765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017674405592706064062353 1513255804194529548046765)
            ·
              refine ⟨567470926572948580517537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513255804194529548046765 567470926572948580517537)
              ·
                refine ⟨425603194929711435388153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567470926572948580517537 425603194929711435388153)
                ·
                  refine ⟨319202396197283576541115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425603194929711435388153 319202396197283576541115)
                  ·
                    rfl

theorem cell20_699350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_699350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699350 prefixEnd_699350 := by exact prefixLift 699350
  have htrace : WordTrace (prefixWord ++ tailWord_699350) baseStart_699350 baseEnd_699350 := by
    simpa [prefixWord, tailWord_699350, baseEnd_699350] using wordTrace_append hprefix tailTrace_699350
  have hstable : (prefixWord ++ tailWord_699350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699350).length < 2 ^ (prefixWord ++ tailWord_699350).sum := by decide
  have hdescent : baseEnd_699350 < baseStart_699350 := by decide
  rcases family_descends (prefixWord ++ tailWord_699350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699368 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_699368 : Nat := 118140960795 + 699368 * 2 ^ 59
def prefixEnd_699368 : Nat := 4983230072969 + 3 ^ 40 * 699368 * 2
def baseEnd_699368 : Nat := 319210611887755513941041

theorem tailTrace_699368 : CollatzResearch.WordTrace tailWord_699368 prefixEnd_699368 319210611887755513941041 := by
  unfold tailWord_699368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12754023265158326695101379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17005364353544435593468505 12754023265158326695101379)
  ·
    refine ⟨19131034897737490042652069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12754023265158326695101379 19131034897737490042652069)
    ·
      refine ⟨3587069043325779382997263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19131034897737490042652069 3587069043325779382997263)
      ·
        refine ⟨5380603564988669074495895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587069043325779382997263 5380603564988669074495895)
        ·
          refine ⟨8070905347483003611743843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5380603564988669074495895 8070905347483003611743843)
          ·
            refine ⟨12106358021224505417615765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070905347483003611743843 12106358021224505417615765)
            ·
              refine ⟨567485532244898691450739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12106358021224505417615765 567485532244898691450739)
              ·
                refine ⟨851228298367348037176109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567485532244898691450739 851228298367348037176109)
                ·
                  refine ⟨319210611887755513941041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851228298367348037176109 319210611887755513941041)
                  ·
                    rfl

theorem cell20_699368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_699368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699368 prefixEnd_699368 := by exact prefixLift 699368
  have htrace : WordTrace (prefixWord ++ tailWord_699368) baseStart_699368 baseEnd_699368 := by
    simpa [prefixWord, tailWord_699368, baseEnd_699368] using wordTrace_append hprefix tailTrace_699368
  have hstable : (prefixWord ++ tailWord_699368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699368).length < 2 ^ (prefixWord ++ tailWord_699368).sum := by decide
  have hdescent : baseEnd_699368 < baseStart_699368 := by decide
  rcases family_descends (prefixWord ++ tailWord_699368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699382 : List Nat := [5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_699382 : Nat := 118140960795 + 699382 * 2 ^ 59
def prefixEnd_699382 : Nat := 4983230072969 + 3 ^ 40 * 699382 * 2
def baseEnd_699382 : Nat := 106405667289744562491439

theorem tailTrace_699382 : CollatzResearch.WordTrace tailWord_699382 prefixEnd_699382 106405667289744562491439 := by
  unfold tailWord_699382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594284822016620861325775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17005704768177289187474933 1594284822016620861325775)
  ·
    refine ⟨2391427233024931291988663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594284822016620861325775 2391427233024931291988663)
    ·
      refine ⟨3587140849537396937982995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391427233024931291988663 3587140849537396937982995)
      ·
        refine ⟨5380711274306095406974493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587140849537396937982995 5380711274306095406974493)
        ·
          refine ⟨2017766727864785777615435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5380711274306095406974493 2017766727864785777615435)
          ·
            refine ⟨3026650091797178666423153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017766727864785777615435 3026650091797178666423153)
            ·
              refine ⟨2269987568847883999817365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026650091797178666423153 2269987568847883999817365)
              ·
                refine ⟨106405667289744562491439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2269987568847883999817365 106405667289744562491439)
                ·
                  rfl

theorem cell20_699382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_699382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699382 prefixEnd_699382 := by exact prefixLift 699382
  have htrace : WordTrace (prefixWord ++ tailWord_699382) baseStart_699382 baseEnd_699382 := by
    simpa [prefixWord, tailWord_699382, baseEnd_699382] using wordTrace_append hprefix tailTrace_699382
  have hstable : (prefixWord ++ tailWord_699382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699382).length < 2 ^ (prefixWord ++ tailWord_699382).sum := by decide
  have hdescent : baseEnd_699382 < baseStart_699382 := by decide
  rcases family_descends (prefixWord ++ tailWord_699382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699406 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_699406 : Nat := 118140960795 + 699406 * 2 ^ 59
def prefixEnd_699406 : Nat := 4983230072969 + 3 ^ 40 * 699406 * 2
def baseEnd_699406 : Nat := 319227956123196270674219

theorem tailTrace_699406 : CollatzResearch.WordTrace tailWord_699406 prefixEnd_699406 319227956123196270674219 := by
  unfold tailWord_699406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188679063022373235010759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17006288336119323920057381 3188679063022373235010759)
  ·
    refine ⟨4783018594533559852516139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3188679063022373235010759 4783018594533559852516139)
    ·
      refine ⟨7174527891800339778774209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783018594533559852516139 7174527891800339778774209)
      ·
        refine ⟨5380895918850254834080657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7174527891800339778774209 5380895918850254834080657)
        ·
          refine ⟨4035671939137691125560493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5380895918850254834080657 4035671939137691125560493)
          ·
            refine ⟨1513376977176634172085185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4035671939137691125560493 1513376977176634172085185)
            ·
              refine ⟨1135032732882475629063889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513376977176634172085185 1135032732882475629063889)
              ·
                refine ⟨851274549661856721797917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135032732882475629063889 851274549661856721797917)
                ·
                  refine ⟨319227956123196270674219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851274549661856721797917 319227956123196270674219)
                  ·
                    rfl

theorem cell20_699406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_699406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699406 prefixEnd_699406 := by exact prefixLift 699406
  have htrace : WordTrace (prefixWord ++ tailWord_699406) baseStart_699406 baseEnd_699406 := by
    simpa [prefixWord, tailWord_699406, baseEnd_699406] using wordTrace_append hprefix tailTrace_699406
  have hstable : (prefixWord ++ tailWord_699406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699406).length < 2 ^ (prefixWord ++ tailWord_699406).sum := by decide
  have hdescent : baseEnd_699406 < baseStart_699406 := by decide
  rcases family_descends (prefixWord ++ tailWord_699406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699427 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_699427 : Nat := 118140960795 + 699427 * 2 ^ 59
def prefixEnd_699427 : Nat := 4983230072969 + 3 ^ 40 * 699427 * 2
def baseEnd_699427 : Nat := 319237541095413530974133

theorem tailTrace_699427 : CollatzResearch.WordTrace tailWord_699427 prefixEnd_699427 319237541095413530974133 := by
  unfold tailWord_699427
  simp only [CollatzResearch.WordTrace]
  refine ⟨25510198437102906466600535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17006798958068604311067023 25510198437102906466600535)
  ·
    refine ⟨38265297655654359699900803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25510198437102906466600535 38265297655654359699900803)
    ·
      refine ⟨57397946483481539549851205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38265297655654359699900803 57397946483481539549851205)
      ·
        refine ⟨10762114965652788665597101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57397946483481539549851205 10762114965652788665597101)
        ·
          refine ⟨4035793112119795749598913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10762114965652788665597101 4035793112119795749598913)
          ·
            refine ⟨3026844834089846812199185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4035793112119795749598913 3026844834089846812199185)
            ·
              refine ⟨2270133625567385109149389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026844834089846812199185 2270133625567385109149389)
              ·
                refine ⟨851300109587769415931021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2270133625567385109149389 851300109587769415931021)
                ·
                  refine ⟨319237541095413530974133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851300109587769415931021 319237541095413530974133)
                  ·
                    rfl

theorem cell20_699427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_699427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699427 prefixEnd_699427 := by exact prefixLift 699427
  have htrace : WordTrace (prefixWord ++ tailWord_699427) baseStart_699427 baseEnd_699427 := by
    simpa [prefixWord, tailWord_699427, baseEnd_699427] using wordTrace_append hprefix tailTrace_699427
  have hstable : (prefixWord ++ tailWord_699427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699427).length < 2 ^ (prefixWord ++ tailWord_699427).sum := by decide
  have hdescent : baseEnd_699427 < baseStart_699427 := by decide
  rcases family_descends (prefixWord ++ tailWord_699427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699455 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_699455 : Nat := 118140960795 + 699455 * 2 ^ 59
def prefixEnd_699455 : Nat := 4983230072969 + 3 ^ 40 * 699455 * 2
def baseEnd_699455 : Nat := 319250321058369878040685

theorem tailTrace_699455 : CollatzResearch.WordTrace tailWord_699455 prefixEnd_699455 319250321058369878040685 := by
  unfold tailWord_699455
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511219681001467248619819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17007479787334311499079879 25511219681001467248619819)
  ·
    refine ⟨38266829521502200872929729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25511219681001467248619819 38266829521502200872929729)
    ·
      refine ⟨28700122141126650654697297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38266829521502200872929729 28700122141126650654697297)
      ·
        refine ⟨21525091605844987991022973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28700122141126650654697297 21525091605844987991022973)
        ·
          refine ⟨8071909352191870496633615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21525091605844987991022973 8071909352191870496633615)
          ·
            refine ⟨12107864028287805744950423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8071909352191870496633615 12107864028287805744950423)
            ·
              refine ⟨18161796042431708617425635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12107864028287805744950423 18161796042431708617425635)
              ·
                refine ⟨27242694063647562926138453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18161796042431708617425635 27242694063647562926138453)
                ·
                  refine ⟨319250321058369878040685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27242694063647562926138453 319250321058369878040685)
                  ·
                    rfl

theorem cell20_699455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_699455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699455 prefixEnd_699455 := by exact prefixLift 699455
  have htrace : WordTrace (prefixWord ++ tailWord_699455) baseStart_699455 baseEnd_699455 := by
    simpa [prefixWord, tailWord_699455, baseEnd_699455] using wordTrace_append hprefix tailTrace_699455
  have hstable : (prefixWord ++ tailWord_699455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699455).length < 2 ^ (prefixWord ++ tailWord_699455).sum := by decide
  have hdescent : baseEnd_699455 < baseStart_699455 := by decide
  rcases family_descends (prefixWord ++ tailWord_699455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699534 : List Nat := [4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_699534 : Nat := 118140960795 + 699534 * 2 ^ 59
def prefixEnd_699534 : Nat := 4983230072969 + 3 ^ 40 * 699534 * 2
def baseEnd_699534 : Nat := 106428792936998904802343

theorem tailTrace_699534 : CollatzResearch.WordTrace tailWord_699534 prefixEnd_699534 106428792936998904802343 := by
  unfold tailWord_699534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189262630964407967593207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17009400698476842493830437 3189262630964407967593207)
  ·
    refine ⟨4783893946446611951389811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3189262630964407967593207 4783893946446611951389811)
    ·
      refine ⟨7175840919669917927084717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783893946446611951389811 7175840919669917927084717)
      ·
        refine ⟨2690940344876219222656769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7175840919669917927084717 2690940344876219222656769)
        ·
          refine ⟨2018205258657164416992577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2690940344876219222656769 2018205258657164416992577)
          ·
            refine ⟨1513653943992873312744433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018205258657164416992577 1513653943992873312744433)
            ·
              refine ⟨1135240457994654984558325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513653943992873312744433 1135240457994654984558325)
              ·
                refine ⟨106428792936998904802343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1135240457994654984558325 106428792936998904802343)
                ·
                  rfl

theorem cell20_699534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_699534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699534 prefixEnd_699534 := by exact prefixLift 699534
  have htrace : WordTrace (prefixWord ++ tailWord_699534) baseStart_699534 baseEnd_699534 := by
    simpa [prefixWord, tailWord_699534, baseEnd_699534] using wordTrace_append hprefix tailTrace_699534
  have hstable : (prefixWord ++ tailWord_699534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699534).length < 2 ^ (prefixWord ++ tailWord_699534).sum := by decide
  have hdescent : baseEnd_699534 < baseStart_699534 := by decide
  rcases family_descends (prefixWord ++ tailWord_699534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699572 : List Nat := [2, 5, 3, 10]
def baseStart_699572 : Nat := 118140960795 + 699572 * 2 ^ 59
def prefixEnd_699572 : Nat := 4983230072969 + 3 ^ 40 * 699572 * 2
def baseEnd_699572 : Nat := 1314007090726080128149

theorem tailTrace_699572 : CollatzResearch.WordTrace tailWord_699572 prefixEnd_699572 1314007090726080128149 := by
  unfold tailWord_699572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757743510788798115314485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17010324681051730820419313 12757743510788798115314485)
  ·
    refine ⟨1196038454136449823310733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12757743510788798115314485 1196038454136449823310733)
    ·
      refine ⟨448514420301168683741525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1196038454136449823310733 448514420301168683741525)
      ·
        refine ⟨1314007090726080128149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 448514420301168683741525 1314007090726080128149)
        ·
          rfl

theorem cell20_699572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 10].length) (baseStart_699572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699572 prefixEnd_699572 := by exact prefixLift 699572
  have htrace : WordTrace (prefixWord ++ tailWord_699572) baseStart_699572 baseEnd_699572 := by
    simpa [prefixWord, tailWord_699572, baseEnd_699572] using wordTrace_append hprefix tailTrace_699572
  have hstable : (prefixWord ++ tailWord_699572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699572).length < 2 ^ (prefixWord ++ tailWord_699572).sum := by decide
  have hdescent : baseEnd_699572 < baseStart_699572 := by decide
  rcases family_descends (prefixWord ++ tailWord_699572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699574 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_699574 : Nat := 118140960795 + 699574 * 2 ^ 59
def prefixEnd_699574 : Nat := 4983230072969 + 3 ^ 40 * 699574 * 2
def baseEnd_699574 : Nat := 319304635900934353073533

theorem tailTrace_699574 : CollatzResearch.WordTrace tailWord_699574 prefixEnd_699574 319304635900934353073533 := by
  unfold tailWord_699574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594722497973146910762611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17010373311713567048134517 1594722497973146910762611)
  ·
    refine ⟨2392083746959720366143917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594722497973146910762611 2392083746959720366143917)
    ·
      refine ⟨897031405109895137303969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2392083746959720366143917 897031405109895137303969)
      ·
        refine ⟨672773553832421352977977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897031405109895137303969 672773553832421352977977)
        ·
          refine ⟨504580165374316014733483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672773553832421352977977 504580165374316014733483)
          ·
            refine ⟨756870248061474022100225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504580165374316014733483 756870248061474022100225)
            ·
              refine ⟨567652686046105516575169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756870248061474022100225 567652686046105516575169)
              ·
                refine ⟨425739514534579137431377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567652686046105516575169 425739514534579137431377)
                ·
                  refine ⟨319304635900934353073533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425739514534579137431377 319304635900934353073533)
                  ·
                    rfl

theorem cell20_699574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_699574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699574 prefixEnd_699574 := by exact prefixLift 699574
  have htrace : WordTrace (prefixWord ++ tailWord_699574) baseStart_699574 baseEnd_699574 := by
    simpa [prefixWord, tailWord_699574, baseEnd_699574] using wordTrace_append hprefix tailTrace_699574
  have hstable : (prefixWord ++ tailWord_699574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699574).length < 2 ^ (prefixWord ++ tailWord_699574).sum := by decide
  have hdescent : baseEnd_699574 < baseStart_699574 := by decide
  rcases family_descends (prefixWord ++ tailWord_699574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699582 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_699582 : Nat := 118140960795 + 699582 * 2 ^ 59
def prefixEnd_699582 : Nat := 4983230072969 + 3 ^ 40 * 699582 * 2
def baseEnd_699582 : Nat := 319308287318921880806833

theorem tailTrace_699582 : CollatzResearch.WordTrace tailWord_699582 prefixEnd_699582 319308287318921880806833 := by
  unfold tailWord_699582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189481468942670992311625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17010567834360911958995333 3189481468942670992311625)
  ·
    refine ⟨2392111101707003244233719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3189481468942670992311625 2392111101707003244233719)
    ·
      refine ⟨3588166652560504866350579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392111101707003244233719 3588166652560504866350579)
      ·
        refine ⟨5382249978840757299525869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588166652560504866350579 5382249978840757299525869)
        ·
          refine ⟨2018343742065283987322201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5382249978840757299525869 2018343742065283987322201)
          ·
            refine ⟨1513757806548962990491651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018343742065283987322201 1513757806548962990491651)
            ·
              refine ⟨2270636709823444485737477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513757806548962990491651 2270636709823444485737477)
              ·
                refine ⟨425744383091895841075777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2270636709823444485737477 425744383091895841075777)
                ·
                  refine ⟨319308287318921880806833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425744383091895841075777 319308287318921880806833)
                  ·
                    rfl

theorem cell20_699582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_699582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699582 prefixEnd_699582 := by exact prefixLift 699582
  have htrace : WordTrace (prefixWord ++ tailWord_699582) baseStart_699582 baseEnd_699582 := by
    simpa [prefixWord, tailWord_699582, baseEnd_699582] using wordTrace_append hprefix tailTrace_699582
  have hstable : (prefixWord ++ tailWord_699582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699582).length < 2 ^ (prefixWord ++ tailWord_699582).sum := by decide
  have hdescent : baseEnd_699582 < baseStart_699582 := by decide
  rcases family_descends (prefixWord ++ tailWord_699582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699606 : List Nat := [5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_699606 : Nat := 118140960795 + 699606 * 2 ^ 59
def prefixEnd_699606 : Nat := 4983230072969 + 3 ^ 40 * 699606 * 2
def baseEnd_699606 : Nat := 106439747190961488002245

theorem tailTrace_699606 : CollatzResearch.WordTrace tailWord_699606 prefixEnd_699606 106439747190961488002245 := by
  unfold tailWord_699606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594795443965901252335417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17011151402302946691577781 1594795443965901252335417)
  ·
    refine ⟨1196096582974425939251563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1594795443965901252335417 1196096582974425939251563)
    ·
      refine ⟨1794144874461638908877345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196096582974425939251563 1794144874461638908877345)
      ·
        refine ⟨1345608655846229181658009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794144874461638908877345 1345608655846229181658009)
        ·
          refine ⟨1009206491884671886243507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345608655846229181658009 1009206491884671886243507)
          ·
            refine ⟨1513809737827007829365261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009206491884671886243507 1513809737827007829365261)
            ·
              refine ⟨567678651685127936011973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513809737827007829365261 567678651685127936011973)
              ·
                refine ⟨106439747190961488002245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567678651685127936011973 106439747190961488002245)
                ·
                  rfl

theorem cell20_699606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_699606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699606 prefixEnd_699606 := by exact prefixLift 699606
  have htrace : WordTrace (prefixWord ++ tailWord_699606) baseStart_699606 baseEnd_699606 := by
    simpa [prefixWord, tailWord_699606, baseEnd_699606] using wordTrace_append hprefix tailTrace_699606
  have hstable : (prefixWord ++ tailWord_699606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699606).length < 2 ^ (prefixWord ++ tailWord_699606).sum := by decide
  have hdescent : baseEnd_699606 < baseStart_699606 := by decide
  rcases family_descends (prefixWord ++ tailWord_699606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699607 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_699607 : Nat := 118140960795 + 699607 * 2 ^ 59
def prefixEnd_699607 : Nat := 4983230072969 + 3 ^ 40 * 699607 * 2
def baseEnd_699607 : Nat := 319319698000132904973397

theorem tailTrace_699607 : CollatzResearch.WordTrace tailWord_699607 prefixEnd_699607 319319698000132904973397 := by
  unfold tailWord_699607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25516763576450797208153075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17011175717633864805435383 25516763576450797208153075)
  ·
    refine ⟨38275145364676195812229613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25516763576450797208153075 38275145364676195812229613)
    ·
      refine ⟨14353179511753573429586105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38275145364676195812229613 14353179511753573429586105)
      ·
        refine ⟨10764884633815180072189579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14353179511753573429586105 10764884633815180072189579)
        ·
          refine ⟨16147326950722770108284369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10764884633815180072189579 16147326950722770108284369)
          ·
            refine ⟨12110495213042077581213277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16147326950722770108284369 12110495213042077581213277)
            ·
              refine ⟨4541435704890779092954979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12110495213042077581213277 4541435704890779092954979)
              ·
                refine ⟨6812153557336168639432469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541435704890779092954979 6812153557336168639432469)
                ·
                  refine ⟨319319698000132904973397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6812153557336168639432469 319319698000132904973397)
                  ·
                    rfl

theorem cell20_699607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_699607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699607 prefixEnd_699607 := by exact prefixLift 699607
  have htrace : WordTrace (prefixWord ++ tailWord_699607) baseStart_699607 baseEnd_699607 := by
    simpa [prefixWord, tailWord_699607, baseEnd_699607] using wordTrace_append hprefix tailTrace_699607
  have hstable : (prefixWord ++ tailWord_699607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699607).length < 2 ^ (prefixWord ++ tailWord_699607).sum := by decide
  have hdescent : baseEnd_699607 < baseStart_699607 := by decide
  rcases family_descends (prefixWord ++ tailWord_699607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699631 : List Nat := [1, 1, 2, 1, 7, 1, 7]
def baseStart_699631 : Nat := 118140960795 + 699631 * 2 ^ 59
def prefixEnd_699631 : Nat := 4983230072969 + 3 ^ 40 * 699631 * 2
def baseEnd_699631 : Nat := 35481183583788387574811

theorem tailTrace_699631 : CollatzResearch.WordTrace tailWord_699631 prefixEnd_699631 35481183583788387574811 := by
  unfold tailWord_699631
  simp only [CollatzResearch.WordTrace]
  refine ⟨25517638928363849307026747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17011759285575899538017831 25517638928363849307026747)
  ·
    refine ⟨38276458392545773960540121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25517638928363849307026747 38276458392545773960540121)
    ·
      refine ⟨28707343794409330470405091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38276458392545773960540121 28707343794409330470405091)
      ·
        refine ⟨43061015691613995705607637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28707343794409330470405091 43061015691613995705607637)
        ·
          refine ⟨1009242555272203024350179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43061015691613995705607637 1009242555272203024350179)
          ·
            refine ⟨1513863832908304536525269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009242555272203024350179 1513863832908304536525269)
            ·
              refine ⟨35481183583788387574811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1513863832908304536525269 35481183583788387574811)
              ·
                rfl

theorem cell20_699631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_699631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699631 prefixEnd_699631 := by exact prefixLift 699631
  have htrace : WordTrace (prefixWord ++ tailWord_699631) baseStart_699631 baseEnd_699631 := by
    simpa [prefixWord, tailWord_699631, baseEnd_699631] using wordTrace_append hprefix tailTrace_699631
  have hstable : (prefixWord ++ tailWord_699631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699631).length < 2 ^ (prefixWord ++ tailWord_699631).sum := by decide
  have hdescent : baseEnd_699631 < baseStart_699631 := by decide
  rcases family_descends (prefixWord ++ tailWord_699631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699662 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_699662 : Nat := 118140960795 + 699662 * 2 ^ 59
def prefixEnd_699662 : Nat := 4983230072969 + 3 ^ 40 * 699662 * 2
def baseEnd_699662 : Nat := 319344801498797158139839

theorem tailTrace_699662 : CollatzResearch.WordTrace tailWord_699662 prefixEnd_699662 319344801498797158139839 := by
  unfold tailWord_699662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189846198906442700175655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17012513060834361067603493 3189846198906442700175655)
  ·
    refine ⟨4784769298359664050263483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3189846198906442700175655 4784769298359664050263483)
    ·
      refine ⟨7177153947539496075395225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4784769298359664050263483 7177153947539496075395225)
      ·
        refine ⟨5382865460654622056546419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7177153947539496075395225 5382865460654622056546419)
        ·
          refine ⟨8074298190981933084819629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382865460654622056546419 8074298190981933084819629)
          ·
            refine ⟨3027861821618224906807361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8074298190981933084819629 3027861821618224906807361)
            ·
              refine ⟨2270896366213668680105521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3027861821618224906807361 2270896366213668680105521)
              ·
                refine ⟨1703172274660251510079141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270896366213668680105521 1703172274660251510079141)
                ·
                  refine ⟨319344801498797158139839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703172274660251510079141 319344801498797158139839)
                  ·
                    rfl

theorem cell20_699662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_699662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699662 prefixEnd_699662 := by exact prefixLift 699662
  have htrace : WordTrace (prefixWord ++ tailWord_699662) baseStart_699662 baseEnd_699662 := by
    simpa [prefixWord, tailWord_699662, baseEnd_699662] using wordTrace_append hprefix tailTrace_699662
  have hstable : (prefixWord ++ tailWord_699662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699662).length < 2 ^ (prefixWord ++ tailWord_699662).sum := by decide
  have hdescent : baseEnd_699662 < baseStart_699662 := by decide
  rcases family_descends (prefixWord ++ tailWord_699662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699676 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_699676 : Nat := 118140960795 + 699676 * 2 ^ 59
def prefixEnd_699676 : Nat := 4983230072969 + 3 ^ 40 * 699676 * 2
def baseEnd_699676 : Nat := 319351191480275331673115

theorem tailTrace_699676 : CollatzResearch.WordTrace tailWord_699676 prefixEnd_699676 319351191480275331673115 := by
  unfold tailWord_699676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759640106600410996207441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17012853475467214661609921 12759640106600410996207441)
  ·
    refine ⟨9569730079950308247155581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12759640106600410996207441 9569730079950308247155581)
    ·
      refine ⟨3588648779981365592683343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9569730079950308247155581 3588648779981365592683343)
      ·
        refine ⟨5382973169972048389025015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588648779981365592683343 5382973169972048389025015)
        ·
          refine ⟨8074459754958072583537523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382973169972048389025015 8074459754958072583537523)
          ·
            refine ⟨12111689632437108875306285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074459754958072583537523 12111689632437108875306285)
            ·
              refine ⟨4541883612163915828239857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12111689632437108875306285 4541883612163915828239857)
              ·
                refine ⟨3406412709122936871179893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541883612163915828239857 3406412709122936871179893)
                ·
                  refine ⟨319351191480275331673115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3406412709122936871179893 319351191480275331673115)
                  ·
                    rfl

theorem cell20_699676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_699676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699676 prefixEnd_699676 := by exact prefixLift 699676
  have htrace : WordTrace (prefixWord ++ tailWord_699676) baseStart_699676 baseEnd_699676 := by
    simpa [prefixWord, tailWord_699676, baseEnd_699676] using wordTrace_append hprefix tailTrace_699676
  have hstable : (prefixWord ++ tailWord_699676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699676).length < 2 ^ (prefixWord ++ tailWord_699676).sum := by decide
  have hdescent : baseEnd_699676 < baseStart_699676 := by decide
  rcases family_descends (prefixWord ++ tailWord_699676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699721 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_699721 : Nat := 118140960795 + 699721 * 2 ^ 59
def prefixEnd_699721 : Nat := 4983230072969 + 3 ^ 40 * 699721 * 2
def baseEnd_699721 : Nat := 319371730706455175172931

theorem tailTrace_699721 : CollatzResearch.WordTrace tailWord_699721 prefixEnd_699721 319371730706455175172931 := by
  unfold tailWord_699721
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520921498037794677803017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17013947665358529785202011 25520921498037794677803017)
  ·
    refine ⟨19140691123528346008352263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25520921498037794677803017 19140691123528346008352263)
    ·
      refine ⟨28711036685292519012528395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19140691123528346008352263 28711036685292519012528395)
      ·
        refine ⟨43066555027938778518792593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28711036685292519012528395 43066555027938778518792593)
        ·
          refine ⟨32299916270954083889094445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43066555027938778518792593 32299916270954083889094445)
          ·
            refine ⟨12112468601607781458410417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32299916270954083889094445 12112468601607781458410417)
            ·
              refine ⟨9084351451205836093807813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12112468601607781458410417 9084351451205836093807813)
              ·
                refine ⟨1703315897101094267588965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9084351451205836093807813 1703315897101094267588965)
                ·
                  refine ⟨319371730706455175172931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703315897101094267588965 319371730706455175172931)
                  ·
                    rfl

theorem cell20_699721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_699721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699721 prefixEnd_699721 := by exact prefixLift 699721
  have htrace : WordTrace (prefixWord ++ tailWord_699721) baseStart_699721 baseEnd_699721 := by
    simpa [prefixWord, tailWord_699721, baseEnd_699721] using wordTrace_append hprefix tailTrace_699721
  have hstable : (prefixWord ++ tailWord_699721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699721).length < 2 ^ (prefixWord ++ tailWord_699721).sum := by decide
  have hdescent : baseEnd_699721 < baseStart_699721 := by decide
  rcases family_descends (prefixWord ++ tailWord_699721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699728 : List Nat := [2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_699728 : Nat := 118140960795 + 699728 * 2 ^ 59
def prefixEnd_699728 : Nat := 4983230072969 + 3 ^ 40 * 699728 * 2
def baseEnd_699728 : Nat := 106458308565731420646523

theorem tailTrace_699728 : CollatzResearch.WordTrace tailWord_699728 prefixEnd_699728 106458308565731420646523 := by
  unfold tailWord_699728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12760588404506217436653919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17014117872674956582205225 12760588404506217436653919)
  ·
    refine ⟨19140882606759326154980879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12760588404506217436653919 19140882606759326154980879)
    ·
      refine ⟨28711323910138989232471319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19140882606759326154980879 28711323910138989232471319)
      ·
        refine ⟨43066985865208483848706979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28711323910138989232471319 43066985865208483848706979)
        ·
          refine ⟨64600478797812725773060469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43066985865208483848706979 64600478797812725773060469)
          ·
            refine ⟨6056294887294943041224419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64600478797812725773060469 6056294887294943041224419)
            ·
              refine ⟨9084442330942414561836629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056294887294943041224419 9084442330942414561836629)
              ·
                refine ⟨106458308565731420646523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9084442330942414561836629 106458308565731420646523)
                ·
                  rfl

theorem cell20_699728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_699728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699728 prefixEnd_699728 := by exact prefixLift 699728
  have htrace : WordTrace (prefixWord ++ tailWord_699728) baseStart_699728 baseEnd_699728 := by
    simpa [prefixWord, tailWord_699728, baseEnd_699728] using wordTrace_append hprefix tailTrace_699728
  have hstable : (prefixWord ++ tailWord_699728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699728).length < 2 ^ (prefixWord ++ tailWord_699728).sum := by decide
  have hdescent : baseEnd_699728 < baseStart_699728 := by decide
  rcases family_descends (prefixWord ++ tailWord_699728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699741 : List Nat := [1, 4, 5, 1, 1, 8]
def baseStart_699741 : Nat := 118140960795 + 699741 * 2 ^ 59
def prefixEnd_699741 : Nat := 4983230072969 + 3 ^ 40 * 699741 * 2
def baseEnd_699741 : Nat := 11828920713015703500229

theorem tailTrace_699741 : CollatzResearch.WordTrace tailWord_699741 prefixEnd_699741 11828920713015703500229 := by
  unfold tailWord_699741
  simp only [CollatzResearch.WordTrace]
  refine ⟨25521650957965338093531077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17014433971976892062354051 25521650957965338093531077)
  ·
    refine ⟨4785309554618500892537077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25521650957965338093531077 4785309554618500892537077)
    ·
      refine ⟨448622770745484458675351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4785309554618500892537077 448622770745484458675351)
      ·
        refine ⟨672934156118226688013027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448622770745484458675351 672934156118226688013027)
        ·
          refine ⟨1009401234177340032019541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672934156118226688013027 1009401234177340032019541)
          ·
            refine ⟨11828920713015703500229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1009401234177340032019541 11828920713015703500229)
            ·
              rfl

theorem cell20_699741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 8].length) (baseStart_699741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699741 prefixEnd_699741 := by exact prefixLift 699741
  have htrace : WordTrace (prefixWord ++ tailWord_699741) baseStart_699741 baseEnd_699741 := by
    simpa [prefixWord, tailWord_699741, baseEnd_699741] using wordTrace_append hprefix tailTrace_699741
  have hstable : (prefixWord ++ tailWord_699741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699741).length < 2 ^ (prefixWord ++ tailWord_699741).sum := by decide
  have hdescent : baseEnd_699741 < baseStart_699741 := by decide
  rcases family_descends (prefixWord ++ tailWord_699741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699751 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 2]
def baseStart_699751 : Nat := 118140960795 + 699751 * 2 ^ 59
def prefixEnd_699751 : Nat := 4983230072969 + 3 ^ 40 * 699751 * 2
def baseEnd_699751 : Nat := 319385423523908404172809

theorem tailTrace_699751 : CollatzResearch.WordTrace tailWord_699751 prefixEnd_699751 319385423523908404172809 := by
  unfold tailWord_699751
  simp only [CollatzResearch.WordTrace]
  refine ⟨25522015687929109801395107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17014677125286073200930071 25522015687929109801395107)
  ·
    refine ⟨38283023531893664702092661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25522015687929109801395107 38283023531893664702092661)
    ·
      refine ⟨3589033456115031065821187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38283023531893664702092661 3589033456115031065821187)
      ·
        refine ⟨5383550184172546598731781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589033456115031065821187 5383550184172546598731781)
        ·
          refine ⟨1009415659532352487262209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5383550184172546598731781 1009415659532352487262209)
          ·
            refine ⟨757061744649264365446657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009415659532352487262209 757061744649264365446657)
            ·
              refine ⟨567796308486948274084993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757061744649264365446657 567796308486948274084993)
              ·
                refine ⟨425847231365211205563745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567796308486948274084993 425847231365211205563745)
                ·
                  refine ⟨319385423523908404172809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425847231365211205563745 319385423523908404172809)
                  ·
                    rfl

theorem cell20_699751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2].length) (baseStart_699751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699751 prefixEnd_699751 := by exact prefixLift 699751
  have htrace : WordTrace (prefixWord ++ tailWord_699751) baseStart_699751 baseEnd_699751 := by
    simpa [prefixWord, tailWord_699751, baseEnd_699751] using wordTrace_append hprefix tailTrace_699751
  have hstable : (prefixWord ++ tailWord_699751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699751).length < 2 ^ (prefixWord ++ tailWord_699751).sum := by decide
  have hdescent : baseEnd_699751 < baseStart_699751 := by decide
  rcases family_descends (prefixWord ++ tailWord_699751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699758 : List Nat := [4, 1, 2, 4, 2, 1, 1, 5]
def baseStart_699758 : Nat := 118140960795 + 699758 * 2 ^ 59
def prefixEnd_699758 : Nat := 4983230072969 + 3 ^ 40 * 699758 * 2
def baseEnd_699758 : Nat := 106462872838215830313149

theorem tailTrace_699758 : CollatzResearch.WordTrace tailWord_699758 prefixEnd_699758 106462872838215830313149 := by
  unfold tailWord_699758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190283874862968749612491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17014847332602499997933285 3190283874862968749612491)
  ·
    refine ⟨4785425812294453124418737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190283874862968749612491 4785425812294453124418737)
    ·
      refine ⟨3589069359220839843314053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4785425812294453124418737 3589069359220839843314053)
      ·
        refine ⟨672950504853907470621385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3589069359220839843314053 672950504853907470621385)
        ·
          refine ⟨504712878640430602966039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672950504853907470621385 504712878640430602966039)
          ·
            refine ⟨757069317960645904449059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504712878640430602966039 757069317960645904449059)
            ·
              refine ⟨1135603976940968856673589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757069317960645904449059 1135603976940968856673589)
              ·
                refine ⟨106462872838215830313149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1135603976940968856673589 106462872838215830313149)
                ·
                  rfl

theorem cell20_699758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_699758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699758 prefixEnd_699758 := by exact prefixLift 699758
  have htrace : WordTrace (prefixWord ++ tailWord_699758) baseStart_699758 baseEnd_699758 := by
    simpa [prefixWord, tailWord_699758, baseEnd_699758] using wordTrace_append hprefix tailTrace_699758
  have hstable : (prefixWord ++ tailWord_699758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699758).length < 2 ^ (prefixWord ++ tailWord_699758).sum := by decide
  have hdescent : baseEnd_699758 < baseStart_699758 := by decide
  rcases family_descends (prefixWord ++ tailWord_699758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699759 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_699759 : Nat := 118140960795 + 699759 * 2 ^ 59
def prefixEnd_699759 : Nat := 4983230072969 + 3 ^ 40 * 699759 * 2
def baseEnd_699759 : Nat := 319389074941895931906109

theorem tailTrace_699759 : CollatzResearch.WordTrace tailWord_699759 prefixEnd_699759 319389074941895931906109 := by
  unfold tailWord_699759
  simp only [CollatzResearch.WordTrace]
  refine ⟨25522307471900127167686331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17014871647933418111790887 25522307471900127167686331)
  ·
    refine ⟨38283461207850190751529497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25522307471900127167686331 38283461207850190751529497)
    ·
      refine ⟨28712595905887643063647123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38283461207850190751529497 28712595905887643063647123)
      ·
        refine ⟨43068893858831464595470685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28712595905887643063647123 43068893858831464595470685)
        ·
          refine ⟨16150835197061799223301507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43068893858831464595470685 16150835197061799223301507)
          ·
            refine ⟨24226252795592698834952261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16150835197061799223301507 24226252795592698834952261)
            ·
              refine ⟨4542422399173631031553549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24226252795592698834952261 4542422399173631031553549)
              ·
                refine ⟨1703408399690111636832581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4542422399173631031553549 1703408399690111636832581)
                ·
                  refine ⟨319389074941895931906109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703408399690111636832581 319389074941895931906109)
                  ·
                    rfl

theorem cell20_699759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_699759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699759 prefixEnd_699759 := by exact prefixLift 699759
  have htrace : WordTrace (prefixWord ++ tailWord_699759) baseStart_699759 baseEnd_699759 := by
    simpa [prefixWord, tailWord_699759, baseEnd_699759] using wordTrace_append hprefix tailTrace_699759
  have hstable : (prefixWord ++ tailWord_699759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699759).length < 2 ^ (prefixWord ++ tailWord_699759).sum := by decide
  have hdescent : baseEnd_699759 < baseStart_699759 := by decide
  rcases family_descends (prefixWord ++ tailWord_699759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699807 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_699807 : Nat := 118140960795 + 699807 * 2 ^ 59
def prefixEnd_699807 : Nat := 4983230072969 + 3 ^ 40 * 699807 * 2
def baseEnd_699807 : Nat := 319410983449821098305913

theorem tailTrace_699807 : CollatzResearch.WordTrace tailWord_699807 prefixEnd_699807 319410983449821098305913 := by
  unfold tailWord_699807
  simp only [CollatzResearch.WordTrace]
  refine ⟨25524058175726231365433675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17016038783817487576955783 25524058175726231365433675)
  ·
    refine ⟨38286087263589347048150513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25524058175726231365433675 38286087263589347048150513)
    ·
      refine ⟨28714565447692010286112885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38286087263589347048150513 28714565447692010286112885)
      ·
        refine ⟨2691990510721125964323083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28714565447692010286112885 2691990510721125964323083)
        ·
          refine ⟨4037985766081688946484625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691990510721125964323083 4037985766081688946484625)
          ·
            refine ⟨3028489324561266709863469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4037985766081688946484625 3028489324561266709863469)
            ·
              refine ⟨1135683496710475016198801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3028489324561266709863469 1135683496710475016198801)
              ·
                refine ⟨851762622532856262149101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135683496710475016198801 851762622532856262149101)
                ·
                  refine ⟨319410983449821098305913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851762622532856262149101 319410983449821098305913)
                  ·
                    rfl

theorem cell20_699807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_699807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699807 prefixEnd_699807 := by exact prefixLift 699807
  have htrace : WordTrace (prefixWord ++ tailWord_699807) baseStart_699807 baseEnd_699807 := by
    simpa [prefixWord, tailWord_699807, baseEnd_699807] using wordTrace_append hprefix tailTrace_699807
  have hstable : (prefixWord ++ tailWord_699807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699807).length < 2 ^ (prefixWord ++ tailWord_699807).sum := by decide
  have hdescent : baseEnd_699807 < baseStart_699807 := by decide
  rcases family_descends (prefixWord ++ tailWord_699807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699866 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_699866 : Nat := 118140960795 + 699866 * 2 ^ 59
def prefixEnd_699866 : Nat := 4983230072969 + 3 ^ 40 * 699866 * 2
def baseEnd_699866 : Nat := 319437912657479115339005

theorem tailTrace_699866 : CollatzResearch.WordTrace tailWord_699866 prefixEnd_699866 319437912657479115339005 := by
  unfold tailWord_699866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381552520628121110457863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17017473388341656294554301 6381552520628121110457863)
  ·
    refine ⟨9572328780942181665686795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381552520628121110457863 9572328780942181665686795)
    ·
      refine ⟨14358493171413272498530193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572328780942181665686795 14358493171413272498530193)
      ·
        refine ⟨10768869878559954373897645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14358493171413272498530193 10768869878559954373897645)
        ·
          refine ⟨4038326204459982890211617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10768869878559954373897645 4038326204459982890211617)
          ·
            refine ⟨3028744653344987167658713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4038326204459982890211617 3028744653344987167658713)
            ·
              refine ⟨2271558490008740375744035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028744653344987167658713 2271558490008740375744035)
              ·
                refine ⟨3407337735013110563616053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271558490008740375744035 3407337735013110563616053)
                ·
                  refine ⟨319437912657479115339005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407337735013110563616053 319437912657479115339005)
                  ·
                    rfl

theorem cell20_699866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_699866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699866 prefixEnd_699866 := by exact prefixLift 699866
  have htrace : WordTrace (prefixWord ++ tailWord_699866) baseStart_699866 baseEnd_699866 := by
    simpa [prefixWord, tailWord_699866, baseEnd_699866] using wordTrace_append hprefix tailTrace_699866
  have hstable : (prefixWord ++ tailWord_699866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699866).length < 2 ^ (prefixWord ++ tailWord_699866).sum := by decide
  have hdescent : baseEnd_699866 < baseStart_699866 := by decide
  rcases family_descends (prefixWord ++ tailWord_699866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699869 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_699869 : Nat := 118140960795 + 699869 * 2 ^ 59
def prefixEnd_699869 : Nat := 4983230072969 + 3 ^ 40 * 699869 * 2
def baseEnd_699869 : Nat := 319439281939224438238993

theorem tailTrace_699869 : CollatzResearch.WordTrace tailWord_699869 prefixEnd_699869 319439281939224438238993 := by
  unfold tailWord_699869
  simp only [CollatzResearch.WordTrace]
  refine ⟨25526319501501615954190661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17017546334334410636127107 25526319501501615954190661)
  ·
    refine ⟨4786184906531552991410749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25526319501501615954190661 4786184906531552991410749)
    ·
      refine ⟨1794819339949332371779031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4786184906531552991410749 1794819339949332371779031)
      ·
        refine ⟨2692229009923998557668547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794819339949332371779031 2692229009923998557668547)
        ·
          refine ⟨4038343514885997836502821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692229009923998557668547 4038343514885997836502821)
          ·
            refine ⟨757189409041124594344279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4038343514885997836502821 757189409041124594344279)
            ·
              refine ⟨1135784113561686891516419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757189409041124594344279 1135784113561686891516419)
              ·
                refine ⟨1703676170342530337274629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135784113561686891516419 1703676170342530337274629)
                ·
                  refine ⟨319439281939224438238993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703676170342530337274629 319439281939224438238993)
                  ·
                    rfl

theorem cell20_699869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_699869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699869 prefixEnd_699869 := by exact prefixLift 699869
  have htrace : WordTrace (prefixWord ++ tailWord_699869) baseStart_699869 baseEnd_699869 := by
    simpa [prefixWord, tailWord_699869, baseEnd_699869] using wordTrace_append hprefix tailTrace_699869
  have hstable : (prefixWord ++ tailWord_699869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699869).length < 2 ^ (prefixWord ++ tailWord_699869).sum := by decide
  have hdescent : baseEnd_699869 < baseStart_699869 := by decide
  rcases family_descends (prefixWord ++ tailWord_699869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699910 : List Nat := [6, 2, 1, 1, 3, 7]
def baseStart_699910 : Nat := 118140960795 + 699910 * 2 ^ 59
def prefixEnd_699910 : Nat := 4983230072969 + 3 ^ 40 * 699910 * 2
def baseEnd_699910 : Nat := 11831777609496685847117

theorem tailTrace_699910 : CollatzResearch.WordTrace tailWord_699910 prefixEnd_699910 11831777609496685847117 := by
  unfold tailWord_699910
  simp only [CollatzResearch.WordTrace]
  refine ⟨797744215448533748638537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17018543262902053304288789 797744215448533748638537)
  ·
    refine ⟨598308161586400311478903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 797744215448533748638537 598308161586400311478903)
    ·
      refine ⟨897462242379600467218355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598308161586400311478903 897462242379600467218355)
      ·
        refine ⟨1346193363569400700827533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897462242379600467218355 1346193363569400700827533)
        ·
          refine ⟨504822511338525262810325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1346193363569400700827533 504822511338525262810325)
          ·
            refine ⟨11831777609496685847117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 504822511338525262810325 11831777609496685847117)
            ·
              rfl

theorem cell20_699910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 7].length) (baseStart_699910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699910 prefixEnd_699910 := by exact prefixLift 699910
  have htrace : WordTrace (prefixWord ++ tailWord_699910) baseStart_699910 baseEnd_699910 := by
    simpa [prefixWord, tailWord_699910, baseEnd_699910] using wordTrace_append hprefix tailTrace_699910
  have hstable : (prefixWord ++ tailWord_699910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699910).length < 2 ^ (prefixWord ++ tailWord_699910).sum := by decide
  have hdescent : baseEnd_699910 < baseStart_699910 := by decide
  rcases family_descends (prefixWord ++ tailWord_699910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699918 : List Nat := [4, 1, 1, 2, 12]
def baseStart_699918 : Nat := 118140960795 + 699918 * 2 ^ 59
def prefixEnd_699918 : Nat := 4983230072969 + 3 ^ 40 * 699918 * 2
def baseEnd_699918 : Nat := 3943970949066642538339

theorem tailTrace_699918 : CollatzResearch.WordTrace tailWord_699918 prefixEnd_699918 3943970949066642538339 := by
  unfold tailWord_699918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191013334790512165340551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17018737785549398215149605 3191013334790512165340551)
  ·
    refine ⟨4786520002185768248010827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3191013334790512165340551 4786520002185768248010827)
    ·
      refine ⟨7179780003278652372016241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786520002185768248010827 7179780003278652372016241)
      ·
        refine ⟨5384835002458989279012181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7179780003278652372016241 5384835002458989279012181)
        ·
          refine ⟨3943970949066642538339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5384835002458989279012181 3943970949066642538339)
          ·
            rfl

theorem cell20_699918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 12].length) (baseStart_699918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699918 prefixEnd_699918 := by exact prefixLift 699918
  have htrace : WordTrace (prefixWord ++ tailWord_699918) baseStart_699918 baseEnd_699918 := by
    simpa [prefixWord, tailWord_699918, baseEnd_699918] using wordTrace_append hprefix tailTrace_699918
  have hstable : (prefixWord ++ tailWord_699918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699918).length < 2 ^ (prefixWord ++ tailWord_699918).sum := by decide
  have hdescent : baseEnd_699918 < baseStart_699918 := by decide
  rcases family_descends (prefixWord ++ tailWord_699918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699980 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_699980 : Nat := 118140960795 + 699980 * 2 ^ 59
def prefixEnd_699980 : Nat := 4983230072969 + 3 ^ 40 * 699980 * 2
def baseEnd_699980 : Nat := 319489945363801385538539

theorem tailTrace_699980 : CollatzResearch.WordTrace tailWord_699980 prefixEnd_699980 319489945363801385538539 := by
  unfold tailWord_699980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765184002049740955740697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17020245336066321274320929 12765184002049740955740697)
  ·
    refine ⟨9573888001537305716805523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12765184002049740955740697 9573888001537305716805523)
    ·
      refine ⟨14360832002305958575208285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9573888001537305716805523 14360832002305958575208285)
      ·
        refine ⟨5385312000864734465703107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14360832002305958575208285 5385312000864734465703107)
        ·
          refine ⟨8077968001297101698554661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385312000864734465703107 8077968001297101698554661)
          ·
            refine ⟨1514619000243206568478999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8077968001297101698554661 1514619000243206568478999)
            ·
              refine ⟨2271928500364809852718499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514619000243206568478999 2271928500364809852718499)
              ·
                refine ⟨3407892750547214779077749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271928500364809852718499 3407892750547214779077749)
                ·
                  refine ⟨319489945363801385538539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407892750547214779077749 319489945363801385538539)
                  ·
                    rfl

theorem cell20_699980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_699980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699980 prefixEnd_699980 := by exact prefixLift 699980
  have htrace : WordTrace (prefixWord ++ tailWord_699980) baseStart_699980 baseEnd_699980 := by
    simpa [prefixWord, tailWord_699980, baseEnd_699980] using wordTrace_append hprefix tailTrace_699980
  have hstable : (prefixWord ++ tailWord_699980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699980).length < 2 ^ (prefixWord ++ tailWord_699980).sum := by decide
  have hdescent : baseEnd_699980 < baseStart_699980 := by decide
  rcases family_descends (prefixWord ++ tailWord_699980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700018 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_700018 : Nat := 118140960795 + 700018 * 2 ^ 59
def prefixEnd_700018 : Nat := 4983230072969 + 3 ^ 40 * 700018 * 2
def baseEnd_700018 : Nat := 319507289599242142271717

theorem tailTrace_700018 : CollatzResearch.WordTrace tailWord_700018 prefixEnd_700018 319507289599242142271717 := by
  unfold tailWord_700018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382938494490453600341177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17021169318641209600909805 6382938494490453600341177)
  ·
    refine ⟨4787203870867840200255883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6382938494490453600341177 4787203870867840200255883)
    ·
      refine ⟨7180805806301760300383825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787203870867840200255883 7180805806301760300383825)
      ·
        refine ⟨5385604354726320225287869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7180805806301760300383825 5385604354726320225287869)
        ·
          refine ⟨2019601633022370084482951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5385604354726320225287869 2019601633022370084482951)
          ·
            refine ⟨3029402449533555126724427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019601633022370084482951 3029402449533555126724427)
            ·
              refine ⟨4544103674300332690086641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029402449533555126724427 4544103674300332690086641)
              ·
                refine ⟨3408077755725249517564981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544103674300332690086641 3408077755725249517564981)
                ·
                  refine ⟨319507289599242142271717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3408077755725249517564981 319507289599242142271717)
                  ·
                    rfl

theorem cell20_700018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_700018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700018 prefixEnd_700018 := by exact prefixLift 700018
  have htrace : WordTrace (prefixWord ++ tailWord_700018) baseStart_700018 baseEnd_700018 := by
    simpa [prefixWord, tailWord_700018, baseEnd_700018] using wordTrace_append hprefix tailTrace_700018
  have hstable : (prefixWord ++ tailWord_700018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700018).length < 2 ^ (prefixWord ++ tailWord_700018).sum := by decide
  have hdescent : baseEnd_700018 < baseStart_700018 := by decide
  rcases family_descends (prefixWord ++ tailWord_700018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700042 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_700042 : Nat := 118140960795 + 700042 * 2 ^ 59
def prefixEnd_700042 : Nat := 4983230072969 + 3 ^ 40 * 700042 * 2
def baseEnd_700042 : Nat := 319518243853204725471619

theorem tailTrace_700042 : CollatzResearch.WordTrace tailWord_700042 prefixEnd_700042 319518243853204725471619 := by
  unfold tailWord_700042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383157332468716625059595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17021752886583244333492253 6383157332468716625059595)
  ·
    refine ⟨9574735998703074937589393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383157332468716625059595 9574735998703074937589393)
    ·
      refine ⟨7181051999027306203192045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9574735998703074937589393 7181051999027306203192045)
      ·
        refine ⟨2692894499635239826197017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7181051999027306203192045 2692894499635239826197017)
        ·
          refine ⟨2019670874726429869647763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2692894499635239826197017 2019670874726429869647763)
          ·
            refine ⟨3029506312089644804471645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019670874726429869647763 3029506312089644804471645)
            ·
              refine ⟨1136064867033616801676867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3029506312089644804471645 1136064867033616801676867)
              ·
                refine ⟨1704097300550425202515301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136064867033616801676867 1704097300550425202515301)
                ·
                  refine ⟨319518243853204725471619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704097300550425202515301 319518243853204725471619)
                  ·
                    rfl

theorem cell20_700042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_700042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700042 prefixEnd_700042 := by exact prefixLift 700042
  have htrace : WordTrace (prefixWord ++ tailWord_700042) baseStart_700042 baseEnd_700042 := by
    simpa [prefixWord, tailWord_700042, baseEnd_700042] using wordTrace_append hprefix tailTrace_700042
  have hstable : (prefixWord ++ tailWord_700042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700042).length < 2 ^ (prefixWord ++ tailWord_700042).sum := by decide
  have hdescent : baseEnd_700042 < baseStart_700042 := by decide
  rcases family_descends (prefixWord ++ tailWord_700042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700052 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_700052 : Nat := 118140960795 + 700052 * 2 ^ 59
def prefixEnd_700052 : Nat := 4983230072969 + 3 ^ 40 * 700052 * 2
def baseEnd_700052 : Nat := 319522808125689135138245

theorem tailTrace_700052 : CollatzResearch.WordTrace tailWord_700052 prefixEnd_700052 319522808125689135138245 := by
  unfold tailWord_700052
  simp only [CollatzResearch.WordTrace]
  refine ⟨12766497029919319104051205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17021996039892425472068273 12766497029919319104051205)
  ·
    refine ⟨2393718193109872332009601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12766497029919319104051205 2393718193109872332009601)
    ·
      refine ⟨1795288644832404249007201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2393718193109872332009601 1795288644832404249007201)
      ·
        refine ⟨1346466483624303186755401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795288644832404249007201 1346466483624303186755401)
        ·
          refine ⟨1009849862718227390066551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346466483624303186755401 1009849862718227390066551)
          ·
            refine ⟨1514774794077341085099827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009849862718227390066551 1514774794077341085099827)
            ·
              refine ⟨2272162191116011627649741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514774794077341085099827 2272162191116011627649741)
              ·
                refine ⟨852060821668504360368653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272162191116011627649741 852060821668504360368653)
                ·
                  refine ⟨319522808125689135138245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852060821668504360368653 319522808125689135138245)
                  ·
                    rfl

theorem cell20_700052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_700052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700052 prefixEnd_700052 := by exact prefixLift 700052
  have htrace : WordTrace (prefixWord ++ tailWord_700052) baseStart_700052 baseEnd_700052 := by
    simpa [prefixWord, tailWord_700052, baseEnd_700052] using wordTrace_append hprefix tailTrace_700052
  have hstable : (prefixWord ++ tailWord_700052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700052).length < 2 ^ (prefixWord ++ tailWord_700052).sum := by decide
  have hdescent : baseEnd_700052 < baseStart_700052 := by decide
  rcases family_descends (prefixWord ++ tailWord_700052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700146 : List Nat := [3, 2, 1, 3, 1, 1, 9]
def baseStart_700146 : Nat := 118140960795 + 700146 * 2 ^ 59
def prefixEnd_700146 : Nat := 4983230072969 + 3 ^ 40 * 700146 * 2
def baseEnd_700146 : Nat := 35507301365226954000503

theorem tailTrace_700146 : CollatzResearch.WordTrace tailWord_700146 prefixEnd_700146 35507301365226954000503 := by
  unfold tailWord_700146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384105630374523065506073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17024281680998728174682861 6384105630374523065506073)
  ·
    refine ⟨4788079222780892299129555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6384105630374523065506073 4788079222780892299129555)
    ·
      refine ⟨7182118834171338448694333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788079222780892299129555 7182118834171338448694333)
      ·
        refine ⟨2693294562814251918260375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7182118834171338448694333 2693294562814251918260375)
        ·
          refine ⟨4039941844221377877390563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693294562814251918260375 4039941844221377877390563)
          ·
            refine ⟨6059912766332066816085845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039941844221377877390563 6059912766332066816085845)
            ·
              refine ⟨35507301365226954000503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6059912766332066816085845 35507301365226954000503)
              ·
                rfl

theorem cell20_700146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_700146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700146 prefixEnd_700146 := by exact prefixLift 700146
  have htrace : WordTrace (prefixWord ++ tailWord_700146) baseStart_700146 baseEnd_700146 := by
    simpa [prefixWord, tailWord_700146, baseEnd_700146] using wordTrace_append hprefix tailTrace_700146
  have hstable : (prefixWord ++ tailWord_700146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700146).length < 2 ^ (prefixWord ++ tailWord_700146).sum := by decide
  have hdescent : baseEnd_700146 < baseStart_700146 := by decide
  rcases family_descends (prefixWord ++ tailWord_700146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700156 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_700156 : Nat := 118140960795 + 700156 * 2 ^ 59
def prefixEnd_700156 : Nat := 4983230072969 + 3 ^ 40 * 700156 * 2
def baseEnd_700156 : Nat := 319570276559526995671153

theorem tailTrace_700156 : CollatzResearch.WordTrace tailWord_700156 prefixEnd_700156 319570276559526995671153 := by
  unfold tailWord_700156
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768393625730931984944161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17024524834307909313258881 12768393625730931984944161)
  ·
    refine ⟨9576295219298198988708121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12768393625730931984944161 9576295219298198988708121)
    ·
      refine ⟨7182221414473649241531091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9576295219298198988708121 7182221414473649241531091)
      ·
        refine ⟨10773332121710473862296637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182221414473649241531091 10773332121710473862296637)
        ·
          refine ⟨4039999545641427698361239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10773332121710473862296637 4039999545641427698361239)
          ·
            refine ⟨6059999318462141547541859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039999545641427698361239 6059999318462141547541859)
            ·
              refine ⟨9089998977693212321312789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059999318462141547541859 9089998977693212321312789)
              ·
                refine ⟨426093702079369327561537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9089998977693212321312789 426093702079369327561537)
                ·
                  refine ⟨319570276559526995671153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426093702079369327561537 319570276559526995671153)
                  ·
                    rfl

theorem cell20_700156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_700156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700156 prefixEnd_700156 := by exact prefixLift 700156
  have htrace : WordTrace (prefixWord ++ tailWord_700156) baseStart_700156 baseEnd_700156 := by
    simpa [prefixWord, tailWord_700156, baseEnd_700156] using wordTrace_append hprefix tailTrace_700156
  have hstable : (prefixWord ++ tailWord_700156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700156).length < 2 ^ (prefixWord ++ tailWord_700156).sum := by decide
  have hdescent : baseEnd_700156 < baseStart_700156 := by decide
  rcases family_descends (prefixWord ++ tailWord_700156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700160 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_700160 : Nat := 118140960795 + 700160 * 2 ^ 59
def prefixEnd_700160 : Nat := 4983230072969 + 3 ^ 40 * 700160 * 2
def baseEnd_700160 : Nat := 319572102268520759537803

theorem tailTrace_700160 : CollatzResearch.WordTrace tailWord_700160 prefixEnd_700160 319572102268520759537803 := by
  unfold tailWord_700160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768466571723686326516967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17024622095631581768689289 12768466571723686326516967)
  ·
    refine ⟨19152699857585529489775451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12768466571723686326516967 19152699857585529489775451)
    ·
      refine ⟨28729049786378294234663177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19152699857585529489775451 28729049786378294234663177)
      ·
        refine ⟨21546787339783720675997383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28729049786378294234663177 21546787339783720675997383)
        ·
          refine ⟨32320181009675581013996075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21546787339783720675997383 32320181009675581013996075)
          ·
            refine ⟨48480271514513371520994113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32320181009675581013996075 48480271514513371520994113)
            ·
              refine ⟨36360203635885028640745585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48480271514513371520994113 36360203635885028640745585)
              ·
                refine ⟨27270152726913771480559189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36360203635885028640745585 27270152726913771480559189)
                ·
                  refine ⟨319572102268520759537803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27270152726913771480559189 319572102268520759537803)
                  ·
                    rfl

theorem cell20_700160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_700160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700160 prefixEnd_700160 := by exact prefixLift 700160
  have htrace : WordTrace (prefixWord ++ tailWord_700160) baseStart_700160 baseEnd_700160 := by
    simpa [prefixWord, tailWord_700160, baseEnd_700160] using wordTrace_append hprefix tailTrace_700160
  have hstable : (prefixWord ++ tailWord_700160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700160).length < 2 ^ (prefixWord ++ tailWord_700160).sum := by decide
  have hdescent : baseEnd_700160 < baseStart_700160 := by decide
  rcases family_descends (prefixWord ++ tailWord_700160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700191 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_700191 : Nat := 118140960795 + 700191 * 2 ^ 59
def prefixEnd_700191 : Nat := 4983230072969 + 3 ^ 40 * 700191 * 2
def baseEnd_700191 : Nat := 319586251513222429504343

theorem tailTrace_700191 : CollatzResearch.WordTrace tailWord_700191 prefixEnd_700191 319586251513222429504343 := by
  unfold tailWord_700191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25538063806335064947412427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17025375870890043298274951 25538063806335064947412427)
  ·
    refine ⟨38307095709502597421118641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25538063806335064947412427 38307095709502597421118641)
    ·
      refine ⟨28730321782126948065838981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38307095709502597421118641 28730321782126948065838981)
      ·
        refine ⟨5386935334148802762344809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28730321782126948065838981 5386935334148802762344809)
        ·
          refine ⟨4040201500611602071758607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386935334148802762344809 4040201500611602071758607)
          ·
            refine ⟨6060302250917403107637911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040201500611602071758607 6060302250917403107637911)
            ·
              refine ⟨9090453376376104661456867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060302250917403107637911 9090453376376104661456867)
              ·
                refine ⟨13635680064564156992185301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090453376376104661456867 13635680064564156992185301)
                ·
                  refine ⟨319586251513222429504343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13635680064564156992185301 319586251513222429504343)
                  ·
                    rfl

theorem cell20_700191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_700191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700191 prefixEnd_700191 := by exact prefixLift 700191
  have htrace : WordTrace (prefixWord ++ tailWord_700191) baseStart_700191 baseEnd_700191 := by
    simpa [prefixWord, tailWord_700191, baseEnd_700191] using wordTrace_append hprefix tailTrace_700191
  have hstable : (prefixWord ++ tailWord_700191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700191).length < 2 ^ (prefixWord ++ tailWord_700191).sum := by decide
  have hdescent : baseEnd_700191 < baseStart_700191 := by decide
  rcases family_descends (prefixWord ++ tailWord_700191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700211 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 4]
def baseStart_700211 : Nat := 118140960795 + 700211 * 2 ^ 59
def prefixEnd_700211 : Nat := 4983230072969 + 3 ^ 40 * 700211 * 2
def baseEnd_700211 : Nat := 319595380058191248837595

theorem tailTrace_700211 : CollatzResearch.WordTrace tailWord_700211 prefixEnd_700211 319595380058191248837595 := by
  unfold tailWord_700211
  simp only [CollatzResearch.WordTrace]
  refine ⟨25538793266262608363140487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17025862177508405575426991 25538793266262608363140487)
  ·
    refine ⟨38308189899393912544710731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25538793266262608363140487 38308189899393912544710731)
    ·
      refine ⟨57462284849090868817066097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38308189899393912544710731 57462284849090868817066097)
      ·
        refine ⟨43096713636818151612799573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57462284849090868817066097 43096713636818151612799573)
        ·
          refine ⟨505039612931462714212495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 43096713636818151612799573 505039612931462714212495)
          ·
            refine ⟨757559419397194071318743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505039612931462714212495 757559419397194071318743)
            ·
              refine ⟨1136339129095791106978115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757559419397194071318743 1136339129095791106978115)
              ·
                refine ⟨1704508693643686660467173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136339129095791106978115 1704508693643686660467173)
                ·
                  refine ⟨319595380058191248837595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704508693643686660467173 319595380058191248837595)
                  ·
                    rfl

theorem cell20_700211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4].length) (baseStart_700211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700211 prefixEnd_700211 := by exact prefixLift 700211
  have htrace : WordTrace (prefixWord ++ tailWord_700211) baseStart_700211 baseEnd_700211 := by
    simpa [prefixWord, tailWord_700211, baseEnd_700211] using wordTrace_append hprefix tailTrace_700211
  have hstable : (prefixWord ++ tailWord_700211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700211).length < 2 ^ (prefixWord ++ tailWord_700211).sum := by decide
  have hdescent : baseEnd_700211 < baseStart_700211 := by decide
  rcases family_descends (prefixWord ++ tailWord_700211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700260 : List Nat := [2, 3, 1, 1, 5, 8]
def baseStart_700260 : Nat := 118140960795 + 700260 * 2 ^ 59
def prefixEnd_700260 : Nat := 4983230072969 + 3 ^ 40 * 700260 * 2
def baseEnd_700260 : Nat := 11837694259013513192743

theorem tailTrace_700260 : CollatzResearch.WordTrace tailWord_700260 prefixEnd_700260 11837694259013513192743 := by
  unfold tailWord_700260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12770290221542544865837117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17027053628723393154449489 12770290221542544865837117)
  ·
    refine ⟨4788858833078454324688919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12770290221542544865837117 4788858833078454324688919)
    ·
      refine ⟨7183288249617681487033379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788858833078454324688919 7183288249617681487033379)
      ·
        refine ⟨10774932374426522230550069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183288249617681487033379 10774932374426522230550069)
        ·
          refine ⟨1010149910102486459114069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10774932374426522230550069 1010149910102486459114069)
          ·
            refine ⟨11837694259013513192743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1010149910102486459114069 11837694259013513192743)
            ·
              rfl

theorem cell20_700260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 8].length) (baseStart_700260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700260 prefixEnd_700260 := by exact prefixLift 700260
  have htrace : WordTrace (prefixWord ++ tailWord_700260) baseStart_700260 baseEnd_700260 := by
    simpa [prefixWord, tailWord_700260, baseEnd_700260] using wordTrace_append hprefix tailTrace_700260
  have hstable : (prefixWord ++ tailWord_700260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700260).length < 2 ^ (prefixWord ++ tailWord_700260).sum := by decide
  have hdescent : baseEnd_700260 < baseStart_700260 := by decide
  rcases family_descends (prefixWord ++ tailWord_700260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700266 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_700266 : Nat := 118140960795 + 700266 * 2 ^ 59
def prefixEnd_700266 : Nat := 4983230072969 + 3 ^ 40 * 700266 * 2
def baseEnd_700266 : Nat := 319620483556855502004037

theorem tailTrace_700266 : CollatzResearch.WordTrace tailWord_700266 prefixEnd_700266 319620483556855502004037 := by
  unfold tailWord_700266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385199820265838189098163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17027199520708901837595101 6385199820265838189098163)
  ·
    refine ⟨9577799730398757283647245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6385199820265838189098163 9577799730398757283647245)
    ·
      refine ⟨3591674898899533981367717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9577799730398757283647245 3591674898899533981367717)
      ·
        refine ⟨673439043543662621506447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3591674898899533981367717 673439043543662621506447)
        ·
          refine ⟨1010158565315493932259671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673439043543662621506447 1010158565315493932259671)
          ·
            refine ⟨1515237847973240898389507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010158565315493932259671 1515237847973240898389507)
            ·
              refine ⟨2272856771959861347584261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515237847973240898389507 2272856771959861347584261)
              ·
                refine ⟨426160644742474002672049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2272856771959861347584261 426160644742474002672049)
                ·
                  refine ⟨319620483556855502004037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426160644742474002672049 319620483556855502004037)
                  ·
                    rfl

theorem cell20_700266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_700266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700266 prefixEnd_700266 := by exact prefixLift 700266
  have htrace : WordTrace (prefixWord ++ tailWord_700266) baseStart_700266 baseEnd_700266 := by
    simpa [prefixWord, tailWord_700266, baseEnd_700266] using wordTrace_append hprefix tailTrace_700266
  have hstable : (prefixWord ++ tailWord_700266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700266).length < 2 ^ (prefixWord ++ tailWord_700266).sum := by decide
  have hdescent : baseEnd_700266 < baseStart_700266 := by decide
  rcases family_descends (prefixWord ++ tailWord_700266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700291 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_700291 : Nat := 118140960795 + 700291 * 2 ^ 59
def prefixEnd_700291 : Nat := 4983230072969 + 3 ^ 40 * 700291 * 2
def baseEnd_700291 : Nat := 319631894238066526170601

theorem tailTrace_700291 : CollatzResearch.WordTrace tailWord_700291 prefixEnd_700291 319631894238066526170601 := by
  unfold tailWord_700291
  simp only [CollatzResearch.WordTrace]
  refine ⟨25541711105972782026052727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17027807403981854684035151 25541711105972782026052727)
  ·
    refine ⟨38312566658959173039079091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25541711105972782026052727 38312566658959173039079091)
    ·
      refine ⟨57468849988438759558618637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38312566658959173039079091 57468849988438759558618637)
      ·
        refine ⟨21550818745664534834481989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57468849988438759558618637 21550818745664534834481989)
        ·
          refine ⟨4040778514812100281465373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21550818745664534834481989 4040778514812100281465373)
          ·
            refine ⟨1515291943054537605549515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4040778514812100281465373 1515291943054537605549515)
            ·
              refine ⟨2272937914581806408324273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515291943054537605549515 2272937914581806408324273)
              ·
                refine ⟨1704703435936354806243205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272937914581806408324273 1704703435936354806243205)
                ·
                  refine ⟨319631894238066526170601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704703435936354806243205 319631894238066526170601)
                  ·
                    rfl

theorem cell20_700291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_700291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700291 prefixEnd_700291 := by exact prefixLift 700291
  have htrace : WordTrace (prefixWord ++ tailWord_700291) baseStart_700291 baseEnd_700291 := by
    simpa [prefixWord, tailWord_700291, baseEnd_700291] using wordTrace_append hprefix tailTrace_700291
  have hstable : (prefixWord ++ tailWord_700291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700291).length < 2 ^ (prefixWord ++ tailWord_700291).sum := by decide
  have hdescent : baseEnd_700291 < baseStart_700291 := by decide
  rcases family_descends (prefixWord ++ tailWord_700291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700318 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_700318 : Nat := 118140960795 + 700318 * 2 ^ 59
def prefixEnd_700318 : Nat := 4983230072969 + 3 ^ 40 * 700318 * 2
def baseEnd_700318 : Nat := 319644217773774432270491

theorem tailTrace_700318 : CollatzResearch.WordTrace tailWord_700318 prefixEnd_700318 319644217773774432270491 := by
  unfold tailWord_700318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192836984609370704660701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17028463917916643758190405 3192836984609370704660701)
  ·
    refine ⟨1197313869228514014247763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3192836984609370704660701 1197313869228514014247763)
    ·
      refine ⟨1795970803842771021371645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197313869228514014247763 1795970803842771021371645)
      ·
        refine ⟨673489051441039133014367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1795970803842771021371645 673489051441039133014367)
        ·
          refine ⟨1010233577161558699521551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673489051441039133014367 1010233577161558699521551)
          ·
            refine ⟨1515350365742338049282327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010233577161558699521551 1515350365742338049282327)
            ·
              refine ⟨2273025548613507073923491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515350365742338049282327 2273025548613507073923491)
              ·
                refine ⟨3409538322920260610885237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273025548613507073923491 3409538322920260610885237)
                ·
                  refine ⟨319644217773774432270491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409538322920260610885237 319644217773774432270491)
                  ·
                    rfl

theorem cell20_700318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_700318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700318 prefixEnd_700318 := by exact prefixLift 700318
  have htrace : WordTrace (prefixWord ++ tailWord_700318) baseStart_700318 baseEnd_700318 := by
    simpa [prefixWord, tailWord_700318, baseEnd_700318] using wordTrace_append hprefix tailTrace_700318
  have hstable : (prefixWord ++ tailWord_700318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700318).length < 2 ^ (prefixWord ++ tailWord_700318).sum := by decide
  have hdescent : baseEnd_700318 < baseStart_700318 := by decide
  rcases family_descends (prefixWord ++ tailWord_700318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700370 : List Nat := [3, 2, 2, 3, 3, 1, 6]
def baseStart_700370 : Nat := 118140960795 + 700370 * 2 ^ 59
def prefixEnd_700370 : Nat := 4983230072969 + 3 ^ 40 * 700370 * 2
def baseEnd_700370 : Nat := 35518661332299262504105

theorem tailTrace_700370 : CollatzResearch.WordTrace tailWord_700370 prefixEnd_700370 35518661332299262504105 := by
  unfold tailWord_700370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386148118171644629544641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17029728315124385678785709 6386148118171644629544641)
  ·
    refine ⟨4789611088628733472158481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6386148118171644629544641 4789611088628733472158481)
    ·
      refine ⟨3592208316471550104118861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789611088628733472158481 3592208316471550104118861)
      ·
        refine ⟨1347078118676831289044573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3592208316471550104118861 1347078118676831289044573)
        ·
          refine ⟨505154294503811733391715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1347078118676831289044573 505154294503811733391715)
          ·
            refine ⟨757731441755717600087573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505154294503811733391715 757731441755717600087573)
            ·
              refine ⟨35518661332299262504105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 757731441755717600087573 35518661332299262504105)
              ·
                rfl

theorem cell20_700370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 6].length) (baseStart_700370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700370 prefixEnd_700370 := by exact prefixLift 700370
  have htrace : WordTrace (prefixWord ++ tailWord_700370) baseStart_700370 baseEnd_700370 := by
    simpa [prefixWord, tailWord_700370, baseEnd_700370] using wordTrace_append hprefix tailTrace_700370
  have hstable : (prefixWord ++ tailWord_700370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700370).length < 2 ^ (prefixWord ++ tailWord_700370).sum := by decide
  have hdescent : baseEnd_700370 < baseStart_700370 := by decide
  rcases family_descends (prefixWord ++ tailWord_700370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700391 : List Nat := [1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_700391 : Nat := 118140960795 + 700391 * 2 ^ 59
def prefixEnd_700391 : Nat := 4983230072969 + 3 ^ 40 * 700391 * 2
def baseEnd_700391 : Nat := 106559178987636874278953

theorem tailTrace_700391 : CollatzResearch.WordTrace tailWord_700391 prefixEnd_700391 106559178987636874278953 := by
  unfold tailWord_700391
  simp only [CollatzResearch.WordTrace]
  refine ⟨25545358405610499104693027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17030238937073666069795351 25545358405610499104693027)
  ·
    refine ⟨38318037608415748657039541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25545358405610499104693027 38318037608415748657039541)
    ·
      refine ⟨3592316025788976436597457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38318037608415748657039541 3592316025788976436597457)
      ·
        refine ⟨2694237019341732327448093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592316025788976436597457 2694237019341732327448093)
        ·
          refine ⟨1010338882253149622793035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2694237019341732327448093 1010338882253149622793035)
          ·
            refine ⟨1515508323379724434189553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010338882253149622793035 1515508323379724434189553)
            ·
              refine ⟨1136631242534793325642165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515508323379724434189553 1136631242534793325642165)
              ·
                refine ⟨106559178987636874278953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1136631242534793325642165 106559178987636874278953)
                ·
                  rfl

theorem cell20_700391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_700391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700391 prefixEnd_700391 := by exact prefixLift 700391
  have htrace : WordTrace (prefixWord ++ tailWord_700391) baseStart_700391 baseEnd_700391 := by
    simpa [prefixWord, tailWord_700391, baseEnd_700391] using wordTrace_append hprefix tailTrace_700391
  have hstable : (prefixWord ++ tailWord_700391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700391).length < 2 ^ (prefixWord ++ tailWord_700391).sum := by decide
  have hdescent : baseEnd_700391 < baseStart_700391 := by decide
  rcases family_descends (prefixWord ++ tailWord_700391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700439 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 2]
def baseStart_700439 : Nat := 118140960795 + 700439 * 2 ^ 59
def prefixEnd_700439 : Nat := 4983230072969 + 3 ^ 40 * 700439 * 2
def baseEnd_700439 : Nat := 319699445470835789236663

theorem tailTrace_700439 : CollatzResearch.WordTrace tailWord_700439 prefixEnd_700439 319699445470835789236663 := by
  unfold tailWord_700439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25547109109436603302440371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17031406072957735534960247 25547109109436603302440371)
  ·
    refine ⟨38320663664154904953660557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25547109109436603302440371 38320663664154904953660557)
    ·
      refine ⟨14370248874058089357622709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38320663664154904953660557 14370248874058089357622709)
      ·
        refine ⟨1347210831942945877277129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14370248874058089357622709 1347210831942945877277129)
        ·
          refine ⟨1010408123957209407957847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347210831942945877277129 1010408123957209407957847)
          ·
            refine ⟨1515612185935814111936771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010408123957209407957847 1515612185935814111936771)
            ·
              refine ⟨2273418278903721167905157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515612185935814111936771 2273418278903721167905157)
              ·
                refine ⟨426265927294447718982217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2273418278903721167905157 426265927294447718982217)
                ·
                  refine ⟨319699445470835789236663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426265927294447718982217 319699445470835789236663)
                  ·
                    rfl

theorem cell20_700439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2].length) (baseStart_700439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700439 prefixEnd_700439 := by exact prefixLift 700439
  have htrace : WordTrace (prefixWord ++ tailWord_700439) baseStart_700439 baseEnd_700439 := by
    simpa [prefixWord, tailWord_700439, baseEnd_700439] using wordTrace_append hprefix tailTrace_700439
  have hstable : (prefixWord ++ tailWord_700439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700439).length < 2 ^ (prefixWord ++ tailWord_700439).sum := by decide
  have hdescent : baseEnd_700439 < baseStart_700439 := by decide
  rcases family_descends (prefixWord ++ tailWord_700439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700464 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_700464 : Nat := 118140960795 + 700464 * 2 ^ 59
def prefixEnd_700464 : Nat := 4983230072969 + 3 ^ 40 * 700464 * 2
def baseEnd_700464 : Nat := 319710856152046813403227

theorem tailTrace_700464 : CollatzResearch.WordTrace tailWord_700464 prefixEnd_700464 319710856152046813403227 := by
  unfold tailWord_700464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12774010467173016286050223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17032013956230688381400297 12774010467173016286050223)
  ·
    refine ⟨19161015700759524429075335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12774010467173016286050223 19161015700759524429075335)
    ·
      refine ⟨28741523551139286643613003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19161015700759524429075335 28741523551139286643613003)
      ·
        refine ⟨43112285326708929965419505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28741523551139286643613003 43112285326708929965419505)
        ·
          refine ⟨32334213995031697474064629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43112285326708929965419505 32334213995031697474064629)
          ·
            refine ⟨3031332562034221638193559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32334213995031697474064629 3031332562034221638193559)
            ·
              refine ⟨4546998843051332457290339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031332562034221638193559 4546998843051332457290339)
              ·
                refine ⟨6820498264576998685935509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546998843051332457290339 6820498264576998685935509)
                ·
                  refine ⟨319710856152046813403227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6820498264576998685935509 319710856152046813403227)
                  ·
                    rfl

theorem cell20_700464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_700464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700464 prefixEnd_700464 := by exact prefixLift 700464
  have htrace : WordTrace (prefixWord ++ tailWord_700464) baseStart_700464 baseEnd_700464 := by
    simpa [prefixWord, tailWord_700464, baseEnd_700464] using wordTrace_append hprefix tailTrace_700464
  have hstable : (prefixWord ++ tailWord_700464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700464).length < 2 ^ (prefixWord ++ tailWord_700464).sum := by decide
  have hdescent : baseEnd_700464 < baseStart_700464 := by decide
  rcases family_descends (prefixWord ++ tailWord_700464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700471 : List Nat := [1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_700471 : Nat := 118140960795 + 700471 * 2 ^ 59
def prefixEnd_700471 : Nat := 4983230072969 + 3 ^ 40 * 700471 * 2
def baseEnd_700471 : Nat := 106571350380928633389955

theorem tailTrace_700471 : CollatzResearch.WordTrace tailWord_700471 prefixEnd_700471 106571350380928633389955 := by
  unfold tailWord_700471
  simp only [CollatzResearch.WordTrace]
  refine ⟨25548276245320672767605267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17032184163547115178403511 25548276245320672767605267)
  ·
    refine ⟨38322414367981009151407901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25548276245320672767605267 38322414367981009151407901)
    ·
      refine ⟨14370905387992878431777963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38322414367981009151407901 14370905387992878431777963)
      ·
        refine ⟨21556358081989317647666945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14370905387992878431777963 21556358081989317647666945)
        ·
          refine ⟨16167268561491988235750209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21556358081989317647666945 16167268561491988235750209)
          ·
            refine ⟨12125451421118991176812657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16167268561491988235750209 12125451421118991176812657)
            ·
              refine ⟨9094088565839243382609493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12125451421118991176812657 9094088565839243382609493)
              ·
                refine ⟨106571350380928633389955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9094088565839243382609493 106571350380928633389955)
                ·
                  rfl

theorem cell20_700471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_700471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700471 prefixEnd_700471 := by exact prefixLift 700471
  have htrace : WordTrace (prefixWord ++ tailWord_700471) baseStart_700471 baseEnd_700471 := by
    simpa [prefixWord, tailWord_700471, baseEnd_700471] using wordTrace_append hprefix tailTrace_700471
  have hstable : (prefixWord ++ tailWord_700471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700471).length < 2 ^ (prefixWord ++ tailWord_700471).sum := by decide
  have hdescent : baseEnd_700471 < baseStart_700471 := by decide
  rcases family_descends (prefixWord ++ tailWord_700471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700498 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_700498 : Nat := 118140960795 + 700498 * 2 ^ 59
def prefixEnd_700498 : Nat := 4983230072969 + 3 ^ 40 * 700498 * 2
def baseEnd_700498 : Nat := 319726374678493806269755

theorem tailTrace_700498 : CollatzResearch.WordTrace tailWord_700498 prefixEnd_700498 319726374678493806269755 := by
  unfold tailWord_700498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387315254055714094709537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17032840677481904252558765 6387315254055714094709537)
  ·
    refine ⟨4790486440541785571032153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6387315254055714094709537 4790486440541785571032153)
    ·
      refine ⟨3592864830406339178274115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4790486440541785571032153 3592864830406339178274115)
      ·
        refine ⟨5389297245609508767411173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3592864830406339178274115 5389297245609508767411173)
        ·
          refine ⟨1010493233551782893889595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5389297245609508767411173 1010493233551782893889595)
          ·
            refine ⟨1515739850327674340834393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010493233551782893889595 1515739850327674340834393)
            ·
              refine ⟨1136804887745755755625795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515739850327674340834393 1136804887745755755625795)
              ·
                refine ⟨1705207331618633633438693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136804887745755755625795 1705207331618633633438693)
                ·
                  refine ⟨319726374678493806269755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705207331618633633438693 319726374678493806269755)
                  ·
                    rfl

theorem cell20_700498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_700498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700498 prefixEnd_700498 := by exact prefixLift 700498
  have htrace : WordTrace (prefixWord ++ tailWord_700498) baseStart_700498 baseEnd_700498 := by
    simpa [prefixWord, tailWord_700498, baseEnd_700498] using wordTrace_append hprefix tailTrace_700498
  have hstable : (prefixWord ++ tailWord_700498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700498).length < 2 ^ (prefixWord ++ tailWord_700498).sum := by decide
  have hdescent : baseEnd_700498 < baseStart_700498 := by decide
  rcases family_descends (prefixWord ++ tailWord_700498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700522 : List Nat := [3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_700522 : Nat := 118140960795 + 700522 * 2 ^ 59
def prefixEnd_700522 : Nat := 4983230072969 + 3 ^ 40 * 700522 * 2
def baseEnd_700522 : Nat := 106579109644152129823219

theorem tailTrace_700522 : CollatzResearch.WordTrace tailWord_700522 prefixEnd_700522 106579109644152129823219 := by
  unfold tailWord_700522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387534092033977119427955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17033424245423938985141213 6387534092033977119427955)
  ·
    refine ⟨9581301138050965679141933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387534092033977119427955 9581301138050965679141933)
    ·
      refine ⟨3592987926769112129678225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9581301138050965679141933 3592987926769112129678225)
      ·
        refine ⟨2694740945076834097258669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592987926769112129678225 2694740945076834097258669)
        ·
          refine ⟨1010527854403812786472001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2694740945076834097258669 1010527854403812786472001)
          ·
            refine ⟨757895890802859589854001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010527854403812786472001 757895890802859589854001)
            ·
              refine ⟨568421918102144692390501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757895890802859589854001 568421918102144692390501)
              ·
                refine ⟨106579109644152129823219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568421918102144692390501 106579109644152129823219)
                ·
                  rfl

theorem cell20_700522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_700522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700522 prefixEnd_700522 := by exact prefixLift 700522
  have htrace : WordTrace (prefixWord ++ tailWord_700522) baseStart_700522 baseEnd_700522 := by
    simpa [prefixWord, tailWord_700522, baseEnd_700522] using wordTrace_append hprefix tailTrace_700522
  have hstable : (prefixWord ++ tailWord_700522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700522).length < 2 ^ (prefixWord ++ tailWord_700522).sum := by decide
  have hdescent : baseEnd_700522 < baseStart_700522 := by decide
  rcases family_descends (prefixWord ++ tailWord_700522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700526 : List Nat := [4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_700526 : Nat := 118140960795 + 700526 * 2 ^ 59
def prefixEnd_700526 : Nat := 4983230072969 + 3 ^ 40 * 700526 * 2
def baseEnd_700526 : Nat := 106579718213816717778769

theorem tailTrace_700526 : CollatzResearch.WordTrace tailWord_700526 prefixEnd_700526 106579718213816717778769 := by
  unfold tailWord_700526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193785282515177145107179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17033521506747611440571621 3193785282515177145107179)
  ·
    refine ⟨4790677923772765717660769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3193785282515177145107179 4790677923772765717660769)
    ·
      refine ⟨3593008442829574288245577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4790677923772765717660769 3593008442829574288245577)
      ·
        refine ⟨2694756332122180716184183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3593008442829574288245577 2694756332122180716184183)
        ·
          refine ⟨4042134498183271074276275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694756332122180716184183 4042134498183271074276275)
          ·
            refine ⟨6063201747274906611414413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042134498183271074276275 6063201747274906611414413)
            ·
              refine ⟨2273700655228089979280405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6063201747274906611414413 2273700655228089979280405)
              ·
                refine ⟨106579718213816717778769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2273700655228089979280405 106579718213816717778769)
                ·
                  rfl

theorem cell20_700526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_700526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700526 prefixEnd_700526 := by exact prefixLift 700526
  have htrace : WordTrace (prefixWord ++ tailWord_700526) baseStart_700526 baseEnd_700526 := by
    simpa [prefixWord, tailWord_700526, baseEnd_700526] using wordTrace_append hprefix tailTrace_700526
  have hstable : (prefixWord ++ tailWord_700526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700526).length < 2 ^ (prefixWord ++ tailWord_700526).sum := by decide
  have hdescent : baseEnd_700526 < baseStart_700526 := by decide
  rcases family_descends (prefixWord ++ tailWord_700526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700547 : List Nat := [1, 1, 1, 3, 3, 3, 8]
def baseStart_700547 : Nat := 118140960795 + 700547 * 2 ^ 59
def prefixEnd_700547 : Nat := 4983230072969 + 3 ^ 40 * 700547 * 2
def baseEnd_700547 : Nat := 35527637734851934848469

theorem tailTrace_700547 : CollatzResearch.WordTrace tailWord_700547 prefixEnd_700547 35527637734851934848469 := by
  unfold tailWord_700547
  simp only [CollatzResearch.WordTrace]
  refine ⟨25551048193045337747371895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17034032128696891831581263 25551048193045337747371895)
  ·
    refine ⟨38326572289568006621057843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25551048193045337747371895 38326572289568006621057843)
    ·
      refine ⟨57489858434352009931586765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38326572289568006621057843 57489858434352009931586765)
      ·
        refine ⟨21558696912882003724345037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57489858434352009931586765 21558696912882003724345037)
        ·
          refine ⟨8084511342330751396629389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21558696912882003724345037 8084511342330751396629389)
          ·
            refine ⟨3031691753374031773736021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8084511342330751396629389 3031691753374031773736021)
            ·
              refine ⟨35527637734851934848469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3031691753374031773736021 35527637734851934848469)
              ·
                rfl

theorem cell20_700547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_700547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700547 prefixEnd_700547 := by exact prefixLift 700547
  have htrace : WordTrace (prefixWord ++ tailWord_700547) baseStart_700547 baseEnd_700547 := by
    simpa [prefixWord, tailWord_700547, baseEnd_700547] using wordTrace_append hprefix tailTrace_700547
  have hstable : (prefixWord ++ tailWord_700547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700547).length < 2 ^ (prefixWord ++ tailWord_700547).sum := by decide
  have hdescent : baseEnd_700547 < baseStart_700547 := by decide
  rcases family_descends (prefixWord ++ tailWord_700547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700595 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 2]
def baseStart_700595 : Nat := 118140960795 + 700595 * 2 ^ 59
def prefixEnd_700595 : Nat := 4983230072969 + 3 ^ 40 * 700595 * 2
def baseEnd_700595 : Nat := 319770648121592580036025

theorem tailTrace_700595 : CollatzResearch.WordTrace tailWord_700595 prefixEnd_700595 319770648121592580036025 := by
  unfold tailWord_700595
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552798896871441945119239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17035199264580961296746159 25552798896871441945119239)
  ·
    refine ⟨38329198345307162917678859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25552798896871441945119239 38329198345307162917678859)
    ·
      refine ⟨57493797517960744376518289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38329198345307162917678859 57493797517960744376518289)
      ·
        refine ⟨43120348138470558282388717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57493797517960744376518289 43120348138470558282388717)
        ·
          refine ⟨16170130551926459355895769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43120348138470558282388717 16170130551926459355895769)
          ·
            refine ⟨12127597913944844516921827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16170130551926459355895769 12127597913944844516921827)
            ·
              refine ⟨18191396870917266775382741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127597913944844516921827 18191396870917266775382741)
              ·
                refine ⟨426360864162123440048033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18191396870917266775382741 426360864162123440048033)
                ·
                  refine ⟨319770648121592580036025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426360864162123440048033 319770648121592580036025)
                  ·
                    rfl

theorem cell20_700595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2].length) (baseStart_700595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700595 prefixEnd_700595 := by exact prefixLift 700595
  have htrace : WordTrace (prefixWord ++ tailWord_700595) baseStart_700595 baseEnd_700595 := by
    simpa [prefixWord, tailWord_700595, baseEnd_700595] using wordTrace_append hprefix tailTrace_700595
  have hstable : (prefixWord ++ tailWord_700595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700595).length < 2 ^ (prefixWord ++ tailWord_700595).sum := by decide
  have hdescent : baseEnd_700595 < baseStart_700595 := by decide
  rcases family_descends (prefixWord ++ tailWord_700595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700616 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_700616 : Nat := 118140960795 + 700616 * 2 ^ 59
def prefixEnd_700616 : Nat := 4983230072969 + 3 ^ 40 * 700616 * 2
def baseEnd_700616 : Nat := 319780233093809840335939

theorem tailTrace_700616 : CollatzResearch.WordTrace tailWord_700616 prefixEnd_700616 319780233093809840335939 := by
  unfold tailWord_700616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12776782414897681265816851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17035709886530241687755801 12776782414897681265816851)
  ·
    refine ⟨19165173622346521898725277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12776782414897681265816851 19165173622346521898725277)
    ·
      refine ⟨7186940108379945712021979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19165173622346521898725277 7186940108379945712021979)
      ·
        refine ⟨10780410162569918568032969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186940108379945712021979 10780410162569918568032969)
        ·
          refine ⟨8085307621927438926024727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780410162569918568032969 8085307621927438926024727)
          ·
            refine ⟨12127961432891158389037091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085307621927438926024727 12127961432891158389037091)
            ·
              refine ⟨18191942149336737583555637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127961432891158389037091 18191942149336737583555637)
              ·
                refine ⟨1705494576500319148458341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18191942149336737583555637 1705494576500319148458341)
                ·
                  refine ⟨319780233093809840335939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705494576500319148458341 319780233093809840335939)
                  ·
                    rfl

theorem cell20_700616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_700616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700616 prefixEnd_700616 := by exact prefixLift 700616
  have htrace : WordTrace (prefixWord ++ tailWord_700616) baseStart_700616 baseEnd_700616 := by
    simpa [prefixWord, tailWord_700616, baseEnd_700616] using wordTrace_append hprefix tailTrace_700616
  have hstable : (prefixWord ++ tailWord_700616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700616).length < 2 ^ (prefixWord ++ tailWord_700616).sum := by decide
  have hdescent : baseEnd_700616 < baseStart_700616 := by decide
  rcases family_descends (prefixWord ++ tailWord_700616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700626 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_700626 : Nat := 118140960795 + 700626 * 2 ^ 59
def prefixEnd_700626 : Nat := 4983230072969 + 3 ^ 40 * 700626 * 2
def baseEnd_700626 : Nat := 319784797366294250002565

theorem tailTrace_700626 : CollatzResearch.WordTrace tailWord_700626 prefixEnd_700626 319784797366294250002565 := by
  unfold tailWord_700626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388482389939783559874433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17035953039839422826331821 6388482389939783559874433)
  ·
    refine ⟨4791361792454837669905825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6388482389939783559874433 4791361792454837669905825)
    ·
      refine ⟨3593521344341128252429369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4791361792454837669905825 3593521344341128252429369)
      ·
        refine ⟨2695141008255846189322027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3593521344341128252429369 2695141008255846189322027)
        ·
          refine ⟨4042711512383769283983041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695141008255846189322027 4042711512383769283983041)
          ·
            refine ⟨3032033634287826962987281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042711512383769283983041 3032033634287826962987281)
            ·
              refine ⟨2274025225715870222240461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032033634287826962987281 2274025225715870222240461)
              ·
                refine ⟨852759459643451333340173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2274025225715870222240461 852759459643451333340173)
                ·
                  refine ⟨319784797366294250002565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852759459643451333340173 319784797366294250002565)
                  ·
                    rfl

theorem cell20_700626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_700626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700626 prefixEnd_700626 := by exact prefixLift 700626
  have htrace : WordTrace (prefixWord ++ tailWord_700626) baseStart_700626 baseEnd_700626 := by
    simpa [prefixWord, tailWord_700626, baseEnd_700626] using wordTrace_append hprefix tailTrace_700626
  have hstable : (prefixWord ++ tailWord_700626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700626).length < 2 ^ (prefixWord ++ tailWord_700626).sum := by decide
  have hdescent : baseEnd_700626 < baseStart_700626 := by decide
  rcases family_descends (prefixWord ++ tailWord_700626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700640 : List Nat := [2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_700640 : Nat := 118140960795 + 700640 * 2 ^ 59
def prefixEnd_700640 : Nat := 4983230072969 + 3 ^ 40 * 700640 * 2
def baseEnd_700640 : Nat := 106597062449257474511947

theorem tailTrace_700640 : CollatzResearch.WordTrace tailWord_700640 prefixEnd_700640 106597062449257474511947 := by
  unfold tailWord_700640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777220090854207315253687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17036293454472276420338249 12777220090854207315253687)
  ·
    refine ⟨19165830136281310972880531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12777220090854207315253687 19165830136281310972880531)
    ·
      refine ⟨28748745204421966459320797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19165830136281310972880531 28748745204421966459320797)
      ·
        refine ⟨10780779451658237422245299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28748745204421966459320797 10780779451658237422245299)
        ·
          refine ⟨16171169177487356133367949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10780779451658237422245299 16171169177487356133367949)
          ·
            refine ⟨6064188441557758550012981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16171169177487356133367949 6064188441557758550012981)
            ·
              refine ⟨568517666396039864063717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6064188441557758550012981 568517666396039864063717)
              ·
                refine ⟨106597062449257474511947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568517666396039864063717 106597062449257474511947)
                ·
                  rfl

theorem cell20_700640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_700640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700640 prefixEnd_700640 := by exact prefixLift 700640
  have htrace : WordTrace (prefixWord ++ tailWord_700640) baseStart_700640 baseEnd_700640 := by
    simpa [prefixWord, tailWord_700640, baseEnd_700640] using wordTrace_append hprefix tailTrace_700640
  have hstable : (prefixWord ++ tailWord_700640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700640).length < 2 ^ (prefixWord ++ tailWord_700640).sum := by decide
  have hdescent : baseEnd_700640 < baseStart_700640 := by decide
  rcases family_descends (prefixWord ++ tailWord_700640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700650 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_700650 : Nat := 118140960795 + 700650 * 2 ^ 59
def prefixEnd_700650 : Nat := 4983230072969 + 3 ^ 40 * 700650 * 2
def baseEnd_700650 : Nat := 319795751620256833202467

theorem tailTrace_700650 : CollatzResearch.WordTrace tailWord_700650 prefixEnd_700650 319795751620256833202467 := by
  unfold tailWord_700650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388701227918046584592851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17036536607781457558914269 6388701227918046584592851)
  ·
    refine ⟨9583051841877069876889277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6388701227918046584592851 9583051841877069876889277)
    ·
      refine ⟨3593644440703901203833479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9583051841877069876889277 3593644440703901203833479)
      ·
        refine ⟨5390466661055851805750219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593644440703901203833479 5390466661055851805750219)
        ·
          refine ⟨8085699991583777708625329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390466661055851805750219 8085699991583777708625329)
          ·
            refine ⟨6064274993687833281468997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8085699991583777708625329 6064274993687833281468997)
            ·
              refine ⟨1137051561316468740275437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6064274993687833281468997 1137051561316468740275437)
              ·
                refine ⟨426394335493675777603289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137051561316468740275437 426394335493675777603289)
                ·
                  refine ⟨319795751620256833202467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426394335493675777603289 319795751620256833202467)
                  ·
                    rfl

theorem cell20_700650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_700650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700650 prefixEnd_700650 := by exact prefixLift 700650
  have htrace : WordTrace (prefixWord ++ tailWord_700650) baseStart_700650 baseEnd_700650 := by
    simpa [prefixWord, tailWord_700650, baseEnd_700650] using wordTrace_append hprefix tailTrace_700650
  have hstable : (prefixWord ++ tailWord_700650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700650).length < 2 ^ (prefixWord ++ tailWord_700650).sum := by decide
  have hdescent : baseEnd_700650 < baseStart_700650 := by decide
  rcases family_descends (prefixWord ++ tailWord_700650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700654 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_700654 : Nat := 118140960795 + 700654 * 2 ^ 59
def prefixEnd_700654 : Nat := 4983230072969 + 3 ^ 40 * 700654 * 2
def baseEnd_700654 : Nat := 319797577329250597069117

theorem tailTrace_700654 : CollatzResearch.WordTrace tailWord_700654 prefixEnd_700654 319797577329250597069117 := by
  unfold tailWord_700654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194368850457211877689627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17036633869105130014344677 3194368850457211877689627)
  ·
    refine ⟨4791553275685817816534441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194368850457211877689627 4791553275685817816534441)
    ·
      refine ⟨3593664956764363362400831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4791553275685817816534441 3593664956764363362400831)
      ·
        refine ⟨5390497435146545043601247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593664956764363362400831 5390497435146545043601247)
        ·
          refine ⟨8085746152719817565401871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390497435146545043601247 8085746152719817565401871)
          ·
            refine ⟨12128619229079726348102807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085746152719817565401871 12128619229079726348102807)
            ·
              refine ⟨18192928843619589522154211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12128619229079726348102807 18192928843619589522154211)
              ·
                refine ⟨27289393265429384283231317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18192928843619589522154211 27289393265429384283231317)
                ·
                  refine ⟨319797577329250597069117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27289393265429384283231317 319797577329250597069117)
                  ·
                    rfl

theorem cell20_700654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_700654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700654 prefixEnd_700654 := by exact prefixLift 700654
  have htrace : WordTrace (prefixWord ++ tailWord_700654) baseStart_700654 baseEnd_700654 := by
    simpa [prefixWord, tailWord_700654, baseEnd_700654] using wordTrace_append hprefix tailTrace_700654
  have hstable : (prefixWord ++ tailWord_700654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700654).length < 2 ^ (prefixWord ++ tailWord_700654).sum := by decide
  have hdescent : baseEnd_700654 < baseStart_700654 := by decide
  rcases family_descends (prefixWord ++ tailWord_700654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700671 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 2]
def baseStart_700671 : Nat := 118140960795 + 700671 * 2 ^ 59
def prefixEnd_700671 : Nat := 4983230072969 + 3 ^ 40 * 700671 * 2
def baseEnd_700671 : Nat := 319805336592474093502381

theorem tailTrace_700671 : CollatzResearch.WordTrace tailWord_700671 prefixEnd_700671 319805336592474093502381 := by
  unfold tailWord_700671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555570844596106924885867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037047229730737949923911 25555570844596106924885867)
  ·
    refine ⟨38333356266894160387328801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25555570844596106924885867 38333356266894160387328801)
    ·
      refine ⟨28750017200170620290496601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38333356266894160387328801 28750017200170620290496601)
      ·
        refine ⟨21562512900127965217872451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28750017200170620290496601 21562512900127965217872451)
        ·
          refine ⟨32343769350191947826808677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21562512900127965217872451 32343769350191947826808677)
          ·
            refine ⟨6064456753160990217526627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32343769350191947826808677 6064456753160990217526627)
            ·
              refine ⟨9096685129741485326289941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064456753160990217526627 9096685129741485326289941)
              ·
                refine ⟨426407115456632124669841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9096685129741485326289941 426407115456632124669841)
                ·
                  refine ⟨319805336592474093502381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426407115456632124669841 319805336592474093502381)
                  ·
                    rfl

theorem cell20_700671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2].length) (baseStart_700671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700671 prefixEnd_700671 := by exact prefixLift 700671
  have htrace : WordTrace (prefixWord ++ tailWord_700671) baseStart_700671 baseEnd_700671 := by
    simpa [prefixWord, tailWord_700671, baseEnd_700671] using wordTrace_append hprefix tailTrace_700671
  have hstable : (prefixWord ++ tailWord_700671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700671).length < 2 ^ (prefixWord ++ tailWord_700671).sum := by decide
  have hdescent : baseEnd_700671 < baseStart_700671 := by decide
  rcases family_descends (prefixWord ++ tailWord_700671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700695 : List Nat := [1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_700695 : Nat := 118140960795 + 700695 * 2 ^ 59
def prefixEnd_700695 : Nat := 4983230072969 + 3 ^ 40 * 700695 * 2
def baseEnd_700695 : Nat := 106605430282145558900761

theorem tailTrace_700695 : CollatzResearch.WordTrace tailWord_700695 prefixEnd_700695 106605430282145558900761 := by
  unfold tailWord_700695
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556446196509159023759539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037630797672772682506359 25556446196509159023759539)
  ·
    refine ⟨38334669294763738535639309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556446196509159023759539 38334669294763738535639309)
    ·
      refine ⟨14375500985536401950864741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38334669294763738535639309 14375500985536401950864741)
      ·
        refine ⟨2695406434788075365787139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14375500985536401950864741 2695406434788075365787139)
        ·
          refine ⟨4043109652182113048680709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695406434788075365787139 4043109652182113048680709)
          ·
            refine ⟨758083059784146196627633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4043109652182113048680709 758083059784146196627633)
            ·
              refine ⟨568562294838109647470725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758083059784146196627633 568562294838109647470725)
              ·
                refine ⟨106605430282145558900761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568562294838109647470725 106605430282145558900761)
                ·
                  rfl

theorem cell20_700695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_700695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700695 prefixEnd_700695 := by exact prefixLift 700695
  have htrace : WordTrace (prefixWord ++ tailWord_700695) baseStart_700695 baseEnd_700695 := by
    simpa [prefixWord, tailWord_700695, baseEnd_700695] using wordTrace_append hprefix tailTrace_700695
  have hstable : (prefixWord ++ tailWord_700695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700695).length < 2 ^ (prefixWord ++ tailWord_700695).sum := by decide
  have hdescent : baseEnd_700695 < baseStart_700695 := by decide
  rcases family_descends (prefixWord ++ tailWord_700695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700723 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_700723 : Nat := 118140960795 + 700723 * 2 ^ 59
def prefixEnd_700723 : Nat := 4983230072969 + 3 ^ 40 * 700723 * 2
def baseEnd_700723 : Nat := 319829070809393023768835

theorem tailTrace_700723 : CollatzResearch.WordTrace tailWord_700723 prefixEnd_700723 319829070809393023768835 := by
  unfold tailWord_700723
  simp only [CollatzResearch.WordTrace]
  refine ⟨25557467440407719805778823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17038311626938479870519215 25557467440407719805778823)
  ·
    refine ⟨38336201160611579708668235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25557467440407719805778823 38336201160611579708668235)
    ·
      refine ⟨57504301740917369563002353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38336201160611579708668235 57504301740917369563002353)
      ·
        refine ⟨43128226305688027172251765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57504301740917369563002353 43128226305688027172251765)
        ·
          refine ⟨4043271216158252547398603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43128226305688027172251765 4043271216158252547398603)
          ·
            refine ⟨6064906824237378821097905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043271216158252547398603 6064906824237378821097905)
            ·
              refine ⟨4548680118178034115823429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064906824237378821097905 4548680118178034115823429)
              ·
                refine ⟨852877522158381396716893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4548680118178034115823429 852877522158381396716893)
                ·
                  refine ⟨319829070809393023768835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852877522158381396716893 319829070809393023768835)
                  ·
                    rfl

theorem cell20_700723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_700723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700723 prefixEnd_700723 := by exact prefixLift 700723
  have htrace : WordTrace (prefixWord ++ tailWord_700723) baseStart_700723 baseEnd_700723 := by
    simpa [prefixWord, tailWord_700723, baseEnd_700723] using wordTrace_append hprefix tailTrace_700723
  have hstable : (prefixWord ++ tailWord_700723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700723).length < 2 ^ (prefixWord ++ tailWord_700723).sum := by decide
  have hdescent : baseEnd_700723 < baseStart_700723 := by decide
  rcases family_descends (prefixWord ++ tailWord_700723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700775 : List Nat := [1, 1, 5, 1, 3, 9]
def baseStart_700775 : Nat := 118140960795 + 700775 * 2 ^ 59
def prefixEnd_700775 : Nat := 4983230072969 + 3 ^ 40 * 700775 * 2
def baseEnd_700775 : Nat := 11846400186159702001307

theorem tailTrace_700775 : CollatzResearch.WordTrace tailWord_700775 prefixEnd_700775 11846400186159702001307 := by
  unfold tailWord_700775
  simp only [CollatzResearch.WordTrace]
  refine ⟨25559364036219332686671779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17039576024146221791114519 25559364036219332686671779)
  ·
    refine ⟨38339046054328999030007669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25559364036219332686671779 38339046054328999030007669)
    ·
      refine ⟨3594285567593343659063219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38339046054328999030007669 3594285567593343659063219)
      ·
        refine ⟨5391428351390015488594829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594285567593343659063219 5391428351390015488594829)
        ·
          refine ⟨2021785631771255808223061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5391428351390015488594829 2021785631771255808223061)
          ·
            refine ⟨11846400186159702001307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2021785631771255808223061 11846400186159702001307)
            ·
              rfl

theorem cell20_700775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 9].length) (baseStart_700775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700775 prefixEnd_700775 := by exact prefixLift 700775
  have htrace : WordTrace (prefixWord ++ tailWord_700775) baseStart_700775 baseEnd_700775 := by
    simpa [prefixWord, tailWord_700775, baseEnd_700775] using wordTrace_append hprefix tailTrace_700775
  have hstable : (prefixWord ++ tailWord_700775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700775).length < 2 ^ (prefixWord ++ tailWord_700775).sum := by decide
  have hdescent : baseEnd_700775 < baseStart_700775 := by decide
  rcases family_descends (prefixWord ++ tailWord_700775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700778 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_700778 : Nat := 118140960795 + 700778 * 2 ^ 59
def prefixEnd_700778 : Nat := 4983230072969 + 3 ^ 40 * 700778 * 2
def baseEnd_700778 : Nat := 319854174308057276935277

theorem tailTrace_700778 : CollatzResearch.WordTrace tailWord_700778 prefixEnd_700778 319854174308057276935277 := by
  unfold tailWord_700778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389868363802116049757747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17039648970138976132687325 6389868363802116049757747)
  ·
    refine ⟨9584802545703174074636621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389868363802116049757747 9584802545703174074636621)
    ·
      refine ⟨3594300954638690277988733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9584802545703174074636621 3594300954638690277988733)
      ·
        refine ⟨1347862857989508854245775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3594300954638690277988733 1347862857989508854245775)
        ·
          refine ⟨2021794286984263281368663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347862857989508854245775 2021794286984263281368663)
          ·
            refine ⟨3032691430476394922052995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021794286984263281368663 3032691430476394922052995)
            ·
              refine ⟨4549037145714592383079493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032691430476394922052995 4549037145714592383079493)
              ·
                refine ⟨852944464821486071827405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4549037145714592383079493 852944464821486071827405)
                ·
                  refine ⟨319854174308057276935277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852944464821486071827405 319854174308057276935277)
                  ·
                    rfl

theorem cell20_700778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_700778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700778 prefixEnd_700778 := by exact prefixLift 700778
  have htrace : WordTrace (prefixWord ++ tailWord_700778) baseStart_700778 baseEnd_700778 := by
    simpa [prefixWord, tailWord_700778, baseEnd_700778] using wordTrace_append hprefix tailTrace_700778
  have hstable : (prefixWord ++ tailWord_700778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700778).length < 2 ^ (prefixWord ++ tailWord_700778).sum := by decide
  have hdescent : baseEnd_700778 < baseStart_700778 := by decide
  rcases family_descends (prefixWord ++ tailWord_700778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700823 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 2]
def baseStart_700823 : Nat := 118140960795 + 700823 * 2 ^ 59
def prefixEnd_700823 : Nat := 4983230072969 + 3 ^ 40 * 700823 * 2
def baseEnd_700823 : Nat := 319874713534237120435093

theorem tailTrace_700823 : CollatzResearch.WordTrace tailWord_700823 prefixEnd_700823 319874713534237120435093 := by
  unfold tailWord_700823
  simp only [CollatzResearch.WordTrace]
  refine ⟨25561114740045436884419123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17040743160030291256279415 25561114740045436884419123)
  ·
    refine ⟨38341672110068155326628685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25561114740045436884419123 38341672110068155326628685)
    ·
      refine ⟨14378127041275558247485757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38341672110068155326628685 14378127041275558247485757)
      ·
        refine ⟨5391797640478334342807159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14378127041275558247485757 5391797640478334342807159)
        ·
          refine ⟨8087696460717501514210739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391797640478334342807159 8087696460717501514210739)
          ·
            refine ⟨12131544691076252271316109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087696460717501514210739 12131544691076252271316109)
            ·
              refine ⟨4549329259153594601743541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12131544691076252271316109 4549329259153594601743541)
              ·
                refine ⟨426499618045649493913457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4549329259153594601743541 426499618045649493913457)
                ·
                  refine ⟨319874713534237120435093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426499618045649493913457 319874713534237120435093)
                  ·
                    rfl

theorem cell20_700823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2].length) (baseStart_700823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700823 prefixEnd_700823 := by exact prefixLift 700823
  have htrace : WordTrace (prefixWord ++ tailWord_700823) baseStart_700823 baseEnd_700823 := by
    simpa [prefixWord, tailWord_700823, baseEnd_700823] using wordTrace_append hprefix tailTrace_700823
  have hstable : (prefixWord ++ tailWord_700823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700823).length < 2 ^ (prefixWord ++ tailWord_700823).sum := by decide
  have hdescent : baseEnd_700823 < baseStart_700823 := by decide
  rcases family_descends (prefixWord ++ tailWord_700823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700840 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_700840 : Nat := 118140960795 + 700840 * 2 ^ 59
def prefixEnd_700840 : Nat := 4983230072969 + 3 ^ 40 * 700840 * 2
def baseEnd_700840 : Nat := 319882472797460616868357

theorem tailTrace_700840 : CollatzResearch.WordTrace tailWord_700840 prefixEnd_700840 319882472797460616868357 := by
  unfold tailWord_700840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12780867390491924393893987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17041156520655899191858649 12780867390491924393893987)
  ·
    refine ⟨19171301085737886590840981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12780867390491924393893987 19171301085737886590840981)
    ·
      refine ⟨898654738393963433945671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19171301085737886590840981 898654738393963433945671)
      ·
        refine ⟨1347982107590945150918507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898654738393963433945671 1347982107590945150918507)
        ·
          refine ⟨2021973161386417726377761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347982107590945150918507 2021973161386417726377761)
          ·
            refine ⟨1516479871039813294783321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2021973161386417726377761 1516479871039813294783321)
            ·
              refine ⟨1137359903279859971087491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516479871039813294783321 1137359903279859971087491)
              ·
                refine ⟨1706039854919789956631237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137359903279859971087491 1706039854919789956631237)
                ·
                  refine ⟨319882472797460616868357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706039854919789956631237 319882472797460616868357)
                  ·
                    rfl

theorem cell20_700840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_700840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700840 prefixEnd_700840 := by exact prefixLift 700840
  have htrace : WordTrace (prefixWord ++ tailWord_700840) baseStart_700840 baseEnd_700840 := by
    simpa [prefixWord, tailWord_700840, baseEnd_700840] using wordTrace_append hprefix tailTrace_700840
  have hstable : (prefixWord ++ tailWord_700840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700840).length < 2 ^ (prefixWord ++ tailWord_700840).sum := by decide
  have hdescent : baseEnd_700840 < baseStart_700840 := by decide
  rcases family_descends (prefixWord ++ tailWord_700840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700896 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_700896 : Nat := 118140960795 + 700896 * 2 ^ 59
def prefixEnd_700896 : Nat := 4983230072969 + 3 ^ 40 * 700896 * 2
def baseEnd_700896 : Nat := 319908032723373311001461

theorem tailTrace_700896 : CollatzResearch.WordTrace tailWord_700896 prefixEnd_700896 319908032723373311001461 := by
  unfold tailWord_700896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781888634390485175913271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17042518179187313567884361 12781888634390485175913271)
  ·
    refine ⟨19172832951585727763869907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12781888634390485175913271 19172832951585727763869907)
    ·
      refine ⟨28759249427378591645804861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19172832951585727763869907 28759249427378591645804861)
      ·
        refine ⟨10784718535266971867176823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28759249427378591645804861 10784718535266971867176823)
        ·
          refine ⟨16177077802900457800765235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10784718535266971867176823 16177077802900457800765235)
          ·
            refine ⟨24265616704350686701147853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16177077802900457800765235 24265616704350686701147853)
            ·
              refine ⟨9099606264131507512930445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24265616704350686701147853 9099606264131507512930445)
              ·
                refine ⟨3412352349049315317348917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099606264131507512930445 3412352349049315317348917)
                ·
                  refine ⟨319908032723373311001461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412352349049315317348917 319908032723373311001461)
                  ·
                    rfl

theorem cell20_700896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_700896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700896 prefixEnd_700896 := by exact prefixLift 700896
  have htrace : WordTrace (prefixWord ++ tailWord_700896) baseStart_700896 baseEnd_700896 := by
    simpa [prefixWord, tailWord_700896, baseEnd_700896] using wordTrace_append hprefix tailTrace_700896
  have hstable : (prefixWord ++ tailWord_700896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700896).length < 2 ^ (prefixWord ++ tailWord_700896).sum := by decide
  have hdescent : baseEnd_700896 < baseStart_700896 := by decide
  rcases family_descends (prefixWord ++ tailWord_700896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700906 : List Nat := [3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_700906 : Nat := 118140960795 + 700906 * 2 ^ 59
def prefixEnd_700906 : Nat := 4983230072969 + 3 ^ 40 * 700906 * 2
def baseEnd_700906 : Nat := 106637532331952573556029

theorem tailTrace_700906 : CollatzResearch.WordTrace tailWord_700906 prefixEnd_700906 106637532331952573556029 := by
  unfold tailWord_700906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391035499686185514922643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17042761332496494706460381 6391035499686185514922643)
  ·
    refine ⟨9586553249529278272383965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391035499686185514922643 9586553249529278272383965)
    ·
      refine ⟨3594957468573479352143987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9586553249529278272383965 3594957468573479352143987)
      ·
        refine ⟨5392436202860219028215981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594957468573479352143987 5392436202860219028215981)
        ·
          refine ⟨2022163576072582135580993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5392436202860219028215981 2022163576072582135580993)
          ·
            refine ⟨1516622682054436601685745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022163576072582135580993 1516622682054436601685745)
            ·
              refine ⟨1137467011540827451264309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516622682054436601685745 1137467011540827451264309)
              ·
                refine ⟨106637532331952573556029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137467011540827451264309 106637532331952573556029)
                ·
                  rfl

theorem cell20_700906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_700906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700906 prefixEnd_700906 := by exact prefixLift 700906
  have htrace : WordTrace (prefixWord ++ tailWord_700906) baseStart_700906 baseEnd_700906 := by
    simpa [prefixWord, tailWord_700906, baseEnd_700906] using wordTrace_append hprefix tailTrace_700906
  have hstable : (prefixWord ++ tailWord_700906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700906).length < 2 ^ (prefixWord ++ tailWord_700906).sum := by decide
  have hdescent : baseEnd_700906 < baseStart_700906 := by decide
  rcases family_descends (prefixWord ++ tailWord_700906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700909 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 3]
def baseStart_700909 : Nat := 118140960795 + 700909 * 2 ^ 59
def prefixEnd_700909 : Nat := 4983230072969 + 3 ^ 40 * 700909 * 2
def baseEnd_700909 : Nat := 319913966277603043568075

theorem tailTrace_700909 : CollatzResearch.WordTrace tailWord_700909 prefixEnd_700909 319913966277603043568075 := by
  unfold tailWord_700909
  simp only [CollatzResearch.WordTrace]
  refine ⟨25564251417733873572049781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17042834278489249048033187 25564251417733873572049781)
  ·
    refine ⟨2396648570412550647379667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25564251417733873572049781 2396648570412550647379667)
    ·
      refine ⟨3594972855618825971069501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396648570412550647379667 3594972855618825971069501)
      ·
        refine ⟨1348114820857059739151063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3594972855618825971069501 1348114820857059739151063)
        ·
          refine ⟨2022172231285589608726595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348114820857059739151063 2022172231285589608726595)
          ·
            refine ⟨3033258346928384413089893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022172231285589608726595 3033258346928384413089893)
            ·
              refine ⟨568735940049072077454355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3033258346928384413089893 568735940049072077454355)
              ·
                refine ⟨853103910073608116181533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568735940049072077454355 853103910073608116181533)
                ·
                  refine ⟨319913966277603043568075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853103910073608116181533 319913966277603043568075)
                  ·
                    rfl

theorem cell20_700909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_700909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700909 prefixEnd_700909 := by exact prefixLift 700909
  have htrace : WordTrace (prefixWord ++ tailWord_700909) baseStart_700909 baseEnd_700909 := by
    simpa [prefixWord, tailWord_700909, baseEnd_700909] using wordTrace_append hprefix tailTrace_700909
  have hstable : (prefixWord ++ tailWord_700909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700909).length < 2 ^ (prefixWord ++ tailWord_700909).sum := by decide
  have hdescent : baseEnd_700909 < baseStart_700909 := by decide
  rcases family_descends (prefixWord ++ tailWord_700909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700913 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_700913 : Nat := 118140960795 + 700913 * 2 ^ 59
def prefixEnd_700913 : Nat := 4983230072969 + 3 ^ 40 * 700913 * 2
def baseEnd_700913 : Nat := 319915791986596807434725

theorem tailTrace_700913 : CollatzResearch.WordTrace tailWord_700913 prefixEnd_700913 319915791986596807434725 := by
  unfold tailWord_700913
  simp only [CollatzResearch.WordTrace]
  refine ⟨25564397309719382255195393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17042931539812921503463595 25564397309719382255195393)
  ·
    refine ⟨19173297982289536691396545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25564397309719382255195393 19173297982289536691396545)
    ·
      refine ⟨14379973486717152518547409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19173297982289536691396545 14379973486717152518547409)
      ·
        refine ⟨10784980115037864388910557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14379973486717152518547409 10784980115037864388910557)
        ·
          refine ⟨4044367543139199145841459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10784980115037864388910557 4044367543139199145841459)
          ·
            refine ⟨6066551314708798718762189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044367543139199145841459 6066551314708798718762189)
            ·
              refine ⟨2274956743015799519535821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6066551314708798718762189 2274956743015799519535821)
              ·
                refine ⟨853108778630924819825933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2274956743015799519535821 853108778630924819825933)
                ·
                  refine ⟨319915791986596807434725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853108778630924819825933 319915791986596807434725)
                  ·
                    rfl

theorem cell20_700913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_700913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700913 prefixEnd_700913 := by exact prefixLift 700913
  have htrace : WordTrace (prefixWord ++ tailWord_700913) baseStart_700913 baseEnd_700913 := by
    simpa [prefixWord, tailWord_700913, baseEnd_700913] using wordTrace_append hprefix tailTrace_700913
  have hstable : (prefixWord ++ tailWord_700913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700913).length < 2 ^ (prefixWord ++ tailWord_700913).sum := by decide
  have hdescent : baseEnd_700913 < baseStart_700913 := by decide
  rcases family_descends (prefixWord ++ tailWord_700913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700954 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_700954 : Nat := 118140960795 + 700954 * 2 ^ 59
def prefixEnd_700954 : Nat := 4983230072969 + 3 ^ 40 * 700954 * 2
def baseEnd_700954 : Nat := 319934505503782887067891

theorem tailTrace_700954 : CollatzResearch.WordTrace tailWord_700954 prefixEnd_700954 319934505503782887067891 := by
  unfold tailWord_700954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391473175642711564359479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17043928468380564171625277 6391473175642711564359479)
  ·
    refine ⟨9587209763464067346539219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391473175642711564359479 9587209763464067346539219)
    ·
      refine ⟨14380814645196101019808829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587209763464067346539219 14380814645196101019808829)
      ·
        refine ⟨5392805491948537882428311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14380814645196101019808829 5392805491948537882428311)
        ·
          refine ⟨8089208237922806823642467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5392805491948537882428311 8089208237922806823642467)
          ·
            refine ⟨12133812356884210235463701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089208237922806823642467 12133812356884210235463701)
            ·
              refine ⟨568772454228947354787361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12133812356884210235463701 568772454228947354787361)
              ·
                refine ⟨426579340671710516090521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568772454228947354787361 426579340671710516090521)
                ·
                  refine ⟨319934505503782887067891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426579340671710516090521 319934505503782887067891)
                  ·
                    rfl

theorem cell20_700954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_700954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700954 prefixEnd_700954 := by exact prefixLift 700954
  have htrace : WordTrace (prefixWord ++ tailWord_700954) baseStart_700954 baseEnd_700954 := by
    simpa [prefixWord, tailWord_700954, baseEnd_700954] using wordTrace_append hprefix tailTrace_700954
  have hstable : (prefixWord ++ tailWord_700954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700954).length < 2 ^ (prefixWord ++ tailWord_700954).sum := by decide
  have hdescent : baseEnd_700954 < baseStart_700954 := by decide
  rcases family_descends (prefixWord ++ tailWord_700954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700965 : List Nat := [1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_700965 : Nat := 118140960795 + 700965 * 2 ^ 59
def prefixEnd_700965 : Nat := 4983230072969 + 3 ^ 40 * 700965 * 2
def baseEnd_700965 : Nat := 106646508734505245900393

theorem tailTrace_700965 : CollatzResearch.WordTrace tailWord_700965 prefixEnd_700965 106646508734505245900393 := by
  unfold tailWord_700965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566293905530995136088349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17044195937020663424058899 25566293905530995136088349)
  ·
    refine ⟨9587360214574123176033131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25566293905530995136088349 9587360214574123176033131)
    ·
      refine ⟨14381040321861184764049697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587360214574123176033131 14381040321861184764049697)
      ·
        refine ⟨10785780241395888573037273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14381040321861184764049697 10785780241395888573037273)
        ·
          refine ⟨8089335181046916429777955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10785780241395888573037273 8089335181046916429777955)
          ·
            refine ⟨12134002771570374644666933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089335181046916429777955 12134002771570374644666933)
            ·
              refine ⟨1137562759834722622937525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12134002771570374644666933 1137562759834722622937525)
              ·
                refine ⟨106646508734505245900393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137562759834722622937525 106646508734505245900393)
                ·
                  rfl

theorem cell20_700965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_700965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700965 prefixEnd_700965 := by exact prefixLift 700965
  have htrace : WordTrace (prefixWord ++ tailWord_700965) baseStart_700965 baseEnd_700965 := by
    simpa [prefixWord, tailWord_700965, baseEnd_700965] using wordTrace_append hprefix tailTrace_700965
  have hstable : (prefixWord ++ tailWord_700965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700965).length < 2 ^ (prefixWord ++ tailWord_700965).sum := by decide
  have hdescent : baseEnd_700965 < baseStart_700965 := by decide
  rcases family_descends (prefixWord ++ tailWord_700965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700968 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_700968 : Nat := 118140960795 + 700968 * 2 ^ 59
def prefixEnd_700968 : Nat := 4983230072969 + 3 ^ 40 * 700968 * 2
def baseEnd_700968 : Nat := 319940895485261060601167

theorem tailTrace_700968 : CollatzResearch.WordTrace tailWord_700968 prefixEnd_700968 319940895485261060601167 := by
  unfold tailWord_700968
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783201662260063324223779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17044268883013417765631705 12783201662260063324223779)
  ·
    refine ⟨19174802493390094986335669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12783201662260063324223779 19174802493390094986335669)
    ·
      refine ⟨1797637733755321404968969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19174802493390094986335669 1797637733755321404968969)
      ·
        refine ⟨1348228300316491053726727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1797637733755321404968969 1348228300316491053726727)
        ·
          refine ⟨2022342450474736580590091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348228300316491053726727 2022342450474736580590091)
          ·
            refine ⟨3033513675712104870885137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022342450474736580590091 3033513675712104870885137)
            ·
              refine ⟨2275135256784078653163853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3033513675712104870885137 2275135256784078653163853)
              ·
                refine ⟨853175721294029494936445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275135256784078653163853 853175721294029494936445)
                ·
                  refine ⟨319940895485261060601167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853175721294029494936445 319940895485261060601167)
                  ·
                    rfl

theorem cell20_700968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_700968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_700968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_700968 prefixEnd_700968 := by exact prefixLift 700968
  have htrace : WordTrace (prefixWord ++ tailWord_700968) baseStart_700968 baseEnd_700968 := by
    simpa [prefixWord, tailWord_700968, baseEnd_700968] using wordTrace_append hprefix tailTrace_700968
  have hstable : (prefixWord ++ tailWord_700968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700968).length < 2 ^ (prefixWord ++ tailWord_700968).sum := by decide
  have hdescent : baseEnd_700968 < baseStart_700968 := by decide
  rcases family_descends (prefixWord ++ tailWord_700968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701013 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 2]
def baseStart_701013 : Nat := 118140960795 + 701013 * 2 ^ 59
def prefixEnd_701013 : Nat := 4983230072969 + 3 ^ 40 * 701013 * 2
def baseEnd_701013 : Nat := 319961434711440904100983

theorem tailTrace_701013 : CollatzResearch.WordTrace tailWord_701013 prefixEnd_701013 319961434711440904100983 := by
  unfold tailWord_701013
  simp only [CollatzResearch.WordTrace]
  refine ⟨25568044609357099333835693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17045363072904732889223795 25568044609357099333835693)
  ·
    refine ⟨9588016728508912250188385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25568044609357099333835693 9588016728508912250188385)
    ·
      refine ⟨7191012546381684187641289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9588016728508912250188385 7191012546381684187641289)
      ·
        refine ⟨5393259409786263140730967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7191012546381684187641289 5393259409786263140730967)
        ·
          refine ⟨8089889114679394711096451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393259409786263140730967 8089889114679394711096451)
          ·
            refine ⟨12134833672019092066644677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089889114679394711096451 12134833672019092066644677)
            ·
              refine ⟨2275281313503579762495877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12134833672019092066644677 2275281313503579762495877)
              ·
                refine ⟨426615246281921205467977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2275281313503579762495877 426615246281921205467977)
                ·
                  refine ⟨319961434711440904100983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426615246281921205467977 319961434711440904100983)
                  ·
                    rfl

theorem cell20_701013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_701013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701013 prefixEnd_701013 := by exact prefixLift 701013
  have htrace : WordTrace (prefixWord ++ tailWord_701013) baseStart_701013 baseEnd_701013 := by
    simpa [prefixWord, tailWord_701013, baseEnd_701013] using wordTrace_append hprefix tailTrace_701013
  have hstable : (prefixWord ++ tailWord_701013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701013).length < 2 ^ (prefixWord ++ tailWord_701013).sum := by decide
  have hdescent : baseEnd_701013 < baseStart_701013 := by decide
  rcases family_descends (prefixWord ++ tailWord_701013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701034 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_701034 : Nat := 118140960795 + 701034 * 2 ^ 59
def prefixEnd_701034 : Nat := 4983230072969 + 3 ^ 40 * 701034 * 2
def baseEnd_701034 : Nat := 319971019683658164400897

theorem tailTrace_701034 : CollatzResearch.WordTrace tailWord_701034 prefixEnd_701034 319971019683658164400897 := by
  unfold tailWord_701034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6392202635570254980087539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17045873694854013280233437 6392202635570254980087539)
  ·
    refine ⟨9588303953355382470131309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6392202635570254980087539 9588303953355382470131309)
    ·
      refine ⟨3595613982508268426299241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9588303953355382470131309 3595613982508268426299241)
      ·
        refine ⟨2696710486881201319724431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3595613982508268426299241 2696710486881201319724431)
        ·
          refine ⟨4045065730321801979586647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696710486881201319724431 4045065730321801979586647)
          ·
            refine ⟨6067598595482702969379971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045065730321801979586647 6067598595482702969379971)
            ·
              refine ⟨9101397893224054454069957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067598595482702969379971 9101397893224054454069957)
              ·
                refine ⟨1706512104979510210138117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9101397893224054454069957 1706512104979510210138117)
                ·
                  refine ⟨319971019683658164400897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706512104979510210138117 319971019683658164400897)
                  ·
                    rfl

theorem cell20_701034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_701034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701034 prefixEnd_701034 := by exact prefixLift 701034
  have htrace : WordTrace (prefixWord ++ tailWord_701034) baseStart_701034 baseEnd_701034 := by
    simpa [prefixWord, tailWord_701034, baseEnd_701034] using wordTrace_append hprefix tailTrace_701034
  have hstable : (prefixWord ++ tailWord_701034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701034).length < 2 ^ (prefixWord ++ tailWord_701034).sum := by decide
  have hdescent : baseEnd_701034 < baseStart_701034 := by decide
  rcases family_descends (prefixWord ++ tailWord_701034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701037 : List Nat := [1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_701037 : Nat := 118140960795 + 701037 * 2 ^ 59
def prefixEnd_701037 : Nat := 4983230072969 + 3 ^ 40 * 701037 * 2
def baseEnd_701037 : Nat := 106657462988467829100295

theorem tailTrace_701037 : CollatzResearch.WordTrace tailWord_701037 prefixEnd_701037 106657462988467829100295 := by
  unfold tailWord_701037
  simp only [CollatzResearch.WordTrace]
  refine ⟨25568919961270151432709365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17045946640846767621806243 25568919961270151432709365)
  ·
    refine ⟨2397086246369076696816503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25568919961270151432709365 2397086246369076696816503)
    ·
      refine ⟨3595629369553615045224755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397086246369076696816503 3595629369553615045224755)
      ·
        refine ⟨5393444054330422567837133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595629369553615045224755 5393444054330422567837133)
        ·
          refine ⟨2022541520373908462938925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5393444054330422567837133 2022541520373908462938925)
          ·
            refine ⟨758453070140215673602097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022541520373908462938925 758453070140215673602097)
            ·
              refine ⟨568839802605161755201573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758453070140215673602097 568839802605161755201573)
              ·
                refine ⟨106657462988467829100295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568839802605161755201573 106657462988467829100295)
                ·
                  rfl

theorem cell20_701037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_701037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701037 prefixEnd_701037 := by exact prefixLift 701037
  have htrace : WordTrace (prefixWord ++ tailWord_701037) baseStart_701037 baseEnd_701037 := by
    simpa [prefixWord, tailWord_701037, baseEnd_701037] using wordTrace_append hprefix tailTrace_701037
  have hstable : (prefixWord ++ tailWord_701037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701037).length < 2 ^ (prefixWord ++ tailWord_701037).sum := by decide
  have hdescent : baseEnd_701037 < baseStart_701037 := by decide
  rcases family_descends (prefixWord ++ tailWord_701037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701079 : List Nat := [1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_701079 : Nat := 118140960795 + 701079 * 2 ^ 59
def prefixEnd_701079 : Nat := 4983230072969 + 3 ^ 40 * 701079 * 2
def baseEnd_701079 : Nat := 106663852969946002633571

theorem tailTrace_701079 : CollatzResearch.WordTrace tailWord_701079 prefixEnd_701079 106663852969946002633571 := by
  unfold tailWord_701079
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570451827117992605738291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17046967884745328403825527 25570451827117992605738291)
  ·
    refine ⟨38355677740676988908607437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25570451827117992605738291 38355677740676988908607437)
    ·
      refine ⟨14383379152753870840727789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38355677740676988908607437 14383379152753870840727789)
      ·
        refine ⟨5393767182282701565272921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14383379152753870840727789 5393767182282701565272921)
        ·
          refine ⟨4045325386712026173954691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5393767182282701565272921 4045325386712026173954691)
          ·
            refine ⟨6067988080068039260932037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045325386712026173954691 6067988080068039260932037)
            ·
              refine ⟨1137747765012757361424757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6067988080068039260932037 1137747765012757361424757)
              ·
                refine ⟨106663852969946002633571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137747765012757361424757 106663852969946002633571)
                ·
                  rfl

theorem cell20_701079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_701079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701079 prefixEnd_701079 := by exact prefixLift 701079
  have htrace : WordTrace (prefixWord ++ tailWord_701079) baseStart_701079 baseEnd_701079 := by
    simpa [prefixWord, tailWord_701079, baseEnd_701079] using wordTrace_append hprefix tailTrace_701079
  have hstable : (prefixWord ++ tailWord_701079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701079).length < 2 ^ (prefixWord ++ tailWord_701079).sum := by decide
  have hdescent : baseEnd_701079 < baseStart_701079 := by decide
  rcases family_descends (prefixWord ++ tailWord_701079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701093 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_701093 : Nat := 118140960795 + 701093 * 2 ^ 59
def prefixEnd_701093 : Nat := 4983230072969 + 3 ^ 40 * 701093 * 2
def baseEnd_701093 : Nat := 319997948891316181433989

theorem tailTrace_701093 : CollatzResearch.WordTrace tailWord_701093 prefixEnd_701093 319997948891316181433989 := by
  unfold tailWord_701093
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570962449067272996747933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17047308299378181997831955 25570962449067272996747933)
  ·
    refine ⟨9589110918400227373780475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25570962449067272996747933 9589110918400227373780475)
    ·
      refine ⟨14383666377600341060670713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9589110918400227373780475 14383666377600341060670713)
      ·
        refine ⟨10787749783200255795503035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14383666377600341060670713 10787749783200255795503035)
        ·
          refine ⟨16181624674800383693254553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10787749783200255795503035 16181624674800383693254553)
          ·
            refine ⟨12136218506100287769940915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16181624674800383693254553 12136218506100287769940915)
            ·
              refine ⟨18204327759150431654911373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136218506100287769940915 18204327759150431654911373)
              ·
                refine ⟨6826622909681411870591765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18204327759150431654911373 6826622909681411870591765)
                ·
                  refine ⟨319997948891316181433989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6826622909681411870591765 319997948891316181433989)
                  ·
                    rfl

theorem cell20_701093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_701093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701093 prefixEnd_701093 := by exact prefixLift 701093
  have htrace : WordTrace (prefixWord ++ tailWord_701093) baseStart_701093 baseEnd_701093 := by
    simpa [prefixWord, tailWord_701093, baseEnd_701093] using wordTrace_append hprefix tailTrace_701093
  have hstable : (prefixWord ++ tailWord_701093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701093).length < 2 ^ (prefixWord ++ tailWord_701093).sum := by decide
  have hdescent : baseEnd_701093 < baseStart_701093 := by decide
  rcases family_descends (prefixWord ++ tailWord_701093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701134 : List Nat := [4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_701134 : Nat := 118140960795 + 701134 * 2 ^ 59
def prefixEnd_701134 : Nat := 4983230072969 + 3 ^ 40 * 701134 * 2
def baseEnd_701134 : Nat := 106672220802834087022385

theorem tailTrace_701134 : CollatzResearch.WordTrace tailWord_701134 prefixEnd_701134 106672220802834087022385 := by
  unfold tailWord_701134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196557230239842124873807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17048305227945824665993637 3196557230239842124873807)
  ·
    refine ⟨4794835845359763187310711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3196557230239842124873807 4794835845359763187310711)
    ·
      refine ⟨7192253768039644780966067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4794835845359763187310711 7192253768039644780966067)
      ·
        refine ⟨10788380652059467171449101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192253768039644780966067 10788380652059467171449101)
        ·
          refine ⟨4045642744522300189293413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10788380652059467171449101 4045642744522300189293413)
          ·
            refine ⟨758558014597931285492515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4045642744522300189293413 758558014597931285492515)
            ·
              refine ⟨1137837021896896928238773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758558014597931285492515 1137837021896896928238773)
              ·
                refine ⟨106672220802834087022385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137837021896896928238773 106672220802834087022385)
                ·
                  rfl

theorem cell20_701134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_701134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701134 prefixEnd_701134 := by exact prefixLift 701134
  have htrace : WordTrace (prefixWord ++ tailWord_701134) baseStart_701134 baseEnd_701134 := by
    simpa [prefixWord, tailWord_701134, baseEnd_701134] using wordTrace_append hprefix tailTrace_701134
  have hstable : (prefixWord ++ tailWord_701134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701134).length < 2 ^ (prefixWord ++ tailWord_701134).sum := by decide
  have hdescent : baseEnd_701134 < baseStart_701134 := by decide
  rcases family_descends (prefixWord ++ tailWord_701134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701162 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_701162 : Nat := 118140960795 + 701162 * 2 ^ 59
def prefixEnd_701162 : Nat := 4983230072969 + 3 ^ 40 * 701162 * 2
def baseEnd_701162 : Nat := 320029442371458608133707

theorem tailTrace_701162 : CollatzResearch.WordTrace tailWord_701162 prefixEnd_701162 320029442371458608133707 := by
  unfold tailWord_701162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393369771454324445252435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17048986057211531854006493 6393369771454324445252435)
  ·
    refine ⟨9590054657181486667878653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6393369771454324445252435 9590054657181486667878653)
    ·
      refine ⟨3596270496443057500454495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9590054657181486667878653 3596270496443057500454495)
      ·
        refine ⟨5394405744664586250681743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596270496443057500454495 5394405744664586250681743)
        ·
          refine ⟨8091608616996879376022615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394405744664586250681743 8091608616996879376022615)
          ·
            refine ⟨12137412925495319064033923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091608616996879376022615 12137412925495319064033923)
            ·
              refine ⟨18206119388242978596050885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137412925495319064033923 18206119388242978596050885)
              ·
                refine ⟨3413647385295558486759541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18206119388242978596050885 3413647385295558486759541)
                ·
                  refine ⟨320029442371458608133707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413647385295558486759541 320029442371458608133707)
                  ·
                    rfl

theorem cell20_701162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_701162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701162 prefixEnd_701162 := by exact prefixLift 701162
  have htrace : WordTrace (prefixWord ++ tailWord_701162) baseStart_701162 baseEnd_701162 := by
    simpa [prefixWord, tailWord_701162, baseEnd_701162] using wordTrace_append hprefix tailTrace_701162
  have hstable : (prefixWord ++ tailWord_701162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701162).length < 2 ^ (prefixWord ++ tailWord_701162).sum := by decide
  have hdescent : baseEnd_701162 < baseStart_701162 := by decide
  rcases family_descends (prefixWord ++ tailWord_701162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701169 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_701169 : Nat := 118140960795 + 701169 * 2 ^ 59
def prefixEnd_701169 : Nat := 4983230072969 + 3 ^ 40 * 701169 * 2
def baseEnd_701169 : Nat := 320032637362197694900345

theorem tailTrace_701169 : CollatzResearch.WordTrace tailWord_701169 prefixEnd_701169 320032637362197694900345 := by
  unfold tailWord_701169
  simp only [CollatzResearch.WordTrace]
  refine ⟨25573734396791937976514561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17049156264527958651009707 25573734396791937976514561)
  ·
    refine ⟨19180300797593953482385921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25573734396791937976514561 19180300797593953482385921)
    ·
      refine ⟨14385225598195465111789441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19180300797593953482385921 14385225598195465111789441)
      ·
        refine ⟨10788919198646598833842081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14385225598195465111789441 10788919198646598833842081)
        ·
          refine ⟨8091689398984949125381561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10788919198646598833842081 8091689398984949125381561)
          ·
            refine ⟨6068767049238711844036171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8091689398984949125381561 6068767049238711844036171)
            ·
              refine ⟨9103150573858067766054257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6068767049238711844036171 9103150573858067766054257)
              ·
                refine ⟨6827362930393550824540693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9103150573858067766054257 6827362930393550824540693)
                ·
                  refine ⟨320032637362197694900345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6827362930393550824540693 320032637362197694900345)
                  ·
                    rfl

theorem cell20_701169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_701169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701169 prefixEnd_701169 := by exact prefixLift 701169
  have htrace : WordTrace (prefixWord ++ tailWord_701169) baseStart_701169 baseEnd_701169 := by
    simpa [prefixWord, tailWord_701169, baseEnd_701169] using wordTrace_append hprefix tailTrace_701169
  have hstable : (prefixWord ++ tailWord_701169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701169).length < 2 ^ (prefixWord ++ tailWord_701169).sum := by decide
  have hdescent : baseEnd_701169 < baseStart_701169 := by decide
  rcases family_descends (prefixWord ++ tailWord_701169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701176 : List Nat := [2, 1, 2, 1, 1, 2, 11]
def baseStart_701176 : Nat := 118140960795 + 701176 * 2 ^ 59
def prefixEnd_701176 : Nat := 4983230072969 + 3 ^ 40 * 701176 * 2
def baseEnd_701176 : Nat := 35559536928104086851887

theorem tailTrace_701176 : CollatzResearch.WordTrace tailWord_701176 prefixEnd_701176 35559536928104086851887 := by
  unfold tailWord_701176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12786994853883289086009691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17049326471844385448012921 12786994853883289086009691)
  ·
    refine ⟨19180492280824933629014537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12786994853883289086009691 19180492280824933629014537)
    ·
      refine ⟨14385369210618700221760903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19180492280824933629014537 14385369210618700221760903)
      ·
        refine ⟨21578053815928050332641355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385369210618700221760903 21578053815928050332641355)
        ·
          refine ⟨32367080723892075498962033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21578053815928050332641355 32367080723892075498962033)
          ·
            refine ⟨24275310542919056624221525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32367080723892075498962033 24275310542919056624221525)
            ·
              refine ⟨35559536928104086851887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24275310542919056624221525 35559536928104086851887)
              ·
                rfl

theorem cell20_701176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_701176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701176 prefixEnd_701176 := by exact prefixLift 701176
  have htrace : WordTrace (prefixWord ++ tailWord_701176) baseStart_701176 baseEnd_701176 := by
    simpa [prefixWord, tailWord_701176, baseEnd_701176] using wordTrace_append hprefix tailTrace_701176
  have hstable : (prefixWord ++ tailWord_701176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701176).length < 2 ^ (prefixWord ++ tailWord_701176).sum := by decide
  have hdescent : baseEnd_701176 < baseStart_701176 := by decide
  rcases family_descends (prefixWord ++ tailWord_701176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701182 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_701182 : Nat := 118140960795 + 701182 * 2 ^ 59
def prefixEnd_701182 : Nat := 4983230072969 + 3 ^ 40 * 701182 * 2
def baseEnd_701182 : Nat := 320038570916427427466959

theorem tailTrace_701182 : CollatzResearch.WordTrace tailWord_701182 prefixEnd_701182 320038570916427427466959 := by
  unfold tailWord_701182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196776068218105149592225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17049472363829894131158533 3196776068218105149592225)
  ·
    refine ⟨2397582051163578862194169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3196776068218105149592225 2397582051163578862194169)
    ·
      refine ⟨1798186538372684146645627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2397582051163578862194169 1798186538372684146645627)
      ·
        refine ⟨2697279807559026219968441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798186538372684146645627 2697279807559026219968441)
        ·
          refine ⟨2022959855669269664976331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2697279807559026219968441 2022959855669269664976331)
          ·
            refine ⟨3034439783503904497464497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022959855669269664976331 3034439783503904497464497)
            ·
              refine ⟨2275829837627928373098373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034439783503904497464497 2275829837627928373098373)
              ·
                refine ⟨426718094555236569955945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2275829837627928373098373 426718094555236569955945)
                ·
                  refine ⟨320038570916427427466959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426718094555236569955945 320038570916427427466959)
                  ·
                    rfl

theorem cell20_701182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_701182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701182 prefixEnd_701182 := by exact prefixLift 701182
  have htrace : WordTrace (prefixWord ++ tailWord_701182) baseStart_701182 baseEnd_701182 := by
    simpa [prefixWord, tailWord_701182, baseEnd_701182] using wordTrace_append hprefix tailTrace_701182
  have hstable : (prefixWord ++ tailWord_701182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701182).length < 2 ^ (prefixWord ++ tailWord_701182).sum := by decide
  have hdescent : baseEnd_701182 < baseStart_701182 := by decide
  rcases family_descends (prefixWord ++ tailWord_701182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701290 : List Nat := [3, 1, 3, 13]
def baseStart_701290 : Nat := 118140960795 + 701290 * 2 ^ 59
def prefixEnd_701290 : Nat := 4983230072969 + 3 ^ 40 * 701290 * 2
def baseEnd_701290 : Nat := 1317234012589543423319

theorem tailTrace_701290 : CollatzResearch.WordTrace tailWord_701290 prefixEnd_701290 1317234012589543423319 := by
  unfold tailWord_701290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394536907338393910417331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17052098419569050427779549 6394536907338393910417331)
  ·
    refine ⟨9591805361007590865625997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6394536907338393910417331 9591805361007590865625997)
    ·
      refine ⟨3596927010377846574609749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9591805361007590865625997 3596927010377846574609749)
      ·
        refine ⟨1317234012589543423319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3596927010377846574609749 1317234012589543423319)
        ·
          rfl

theorem cell20_701290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 13].length) (baseStart_701290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701290 prefixEnd_701290 := by exact prefixLift 701290
  have htrace : WordTrace (prefixWord ++ tailWord_701290) baseStart_701290 baseEnd_701290 := by
    simpa [prefixWord, tailWord_701290, baseEnd_701290] using wordTrace_append hprefix tailTrace_701290
  have hstable : (prefixWord ++ tailWord_701290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701290).length < 2 ^ (prefixWord ++ tailWord_701290).sum := by decide
  have hdescent : baseEnd_701290 < baseStart_701290 := by decide
  rcases family_descends (prefixWord ++ tailWord_701290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701321 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_701321 : Nat := 118140960795 + 701321 * 2 ^ 59
def prefixEnd_701321 : Nat := 4983230072969 + 3 ^ 40 * 701321 * 2
def baseEnd_701321 : Nat := 320102014303960721833057

theorem tailTrace_701321 : CollatzResearch.WordTrace tailWord_701321 prefixEnd_701321 320102014303960721833057 := by
  unfold tailWord_701321
  simp only [CollatzResearch.WordTrace]
  refine ⟨25579278292241267936047817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17052852194827511957365211 25579278292241267936047817)
  ·
    refine ⟨19184458719180950952035863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25579278292241267936047817 19184458719180950952035863)
    ·
      refine ⟨28776688078771426428053795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19184458719180950952035863 28776688078771426428053795)
      ·
        refine ⟨43165032118157139642080693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28776688078771426428053795 43165032118157139642080693)
        ·
          refine ⟨4046721761077231841445065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43165032118157139642080693 4046721761077231841445065)
          ·
            refine ⟨3035041320807923881083799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4046721761077231841445065 3035041320807923881083799)
            ·
              refine ⟨4552561981211885821625699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035041320807923881083799 4552561981211885821625699)
              ·
                refine ⟨6828842971817828732438549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552561981211885821625699 6828842971817828732438549)
                ·
                  refine ⟨320102014303960721833057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6828842971817828732438549 320102014303960721833057)
                  ·
                    rfl

theorem cell20_701321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_701321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701321 prefixEnd_701321 := by exact prefixLift 701321
  have htrace : WordTrace (prefixWord ++ tailWord_701321) baseStart_701321 baseEnd_701321 := by
    simpa [prefixWord, tailWord_701321, baseEnd_701321] using wordTrace_append hprefix tailTrace_701321
  have hstable : (prefixWord ++ tailWord_701321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701321).length < 2 ^ (prefixWord ++ tailWord_701321).sum := by decide
  have hdescent : baseEnd_701321 < baseStart_701321 := by decide
  rcases family_descends (prefixWord ++ tailWord_701321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701345 : List Nat := [1, 2, 3, 4, 1, 2, 7]
def baseStart_701345 : Nat := 118140960795 + 701345 * 2 ^ 59
def prefixEnd_701345 : Nat := 4983230072969 + 3 ^ 40 * 701345 * 2
def baseEnd_701345 : Nat := 35568107617547033892551

theorem tailTrace_701345 : CollatzResearch.WordTrace tailWord_701345 prefixEnd_701345 35568107617547033892551 := by
  unfold tailWord_701345
  simp only [CollatzResearch.WordTrace]
  refine ⟨25580153644154320034921489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17053435762769546689947659 25580153644154320034921489)
  ·
    refine ⟨19185115233115740026191117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25580153644154320034921489 19185115233115740026191117)
    ·
      refine ⟨7194418212418402509821669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19185115233115740026191117 7194418212418402509821669)
      ·
        refine ⟨1348953414828450470591563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7194418212418402509821669 1348953414828450470591563)
        ·
          refine ⟨2023430122242675705887345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348953414828450470591563 2023430122242675705887345)
          ·
            refine ⟨1517572591682006779415509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023430122242675705887345 1517572591682006779415509)
            ·
              refine ⟨35568107617547033892551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1517572591682006779415509 35568107617547033892551)
              ·
                rfl

theorem cell20_701345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_701345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701345 prefixEnd_701345 := by exact prefixLift 701345
  have htrace : WordTrace (prefixWord ++ tailWord_701345) baseStart_701345 baseEnd_701345 := by
    simpa [prefixWord, tailWord_701345, baseEnd_701345] using wordTrace_append hprefix tailTrace_701345
  have hstable : (prefixWord ++ tailWord_701345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701345).length < 2 ^ (prefixWord ++ tailWord_701345).sum := by decide
  have hdescent : baseEnd_701345 < baseStart_701345 := by decide
  rcases family_descends (prefixWord ++ tailWord_701345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701383 : List Nat := [1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_701383 : Nat := 118140960795 + 701383 * 2 ^ 59
def prefixEnd_701383 : Nat := 4983230072969 + 3 ^ 40 * 701383 * 2
def baseEnd_701383 : Nat := 106710104264454687255379

theorem tailTrace_701383 : CollatzResearch.WordTrace tailWord_701383 prefixEnd_701383 106710104264454687255379 := by
  unfold tailWord_701383
  simp only [CollatzResearch.WordTrace]
  refine ⟨25581539618016652524804803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17054359745344435016536535 25581539618016652524804803)
  ·
    refine ⟨38372309427024978787207205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25581539618016652524804803 38372309427024978787207205)
    ·
      refine ⟨7194808017567183522601351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38372309427024978787207205 7194808017567183522601351)
      ·
        refine ⟨10792212026350775283902027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194808017567183522601351 10792212026350775283902027)
        ·
          refine ⟨16188318039526162925853041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10792212026350775283902027 16188318039526162925853041)
          ·
            refine ⟨12141238529644622194389781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16188318039526162925853041 12141238529644622194389781)
            ·
              refine ⟨569120556077091665362021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12141238529644622194389781 569120556077091665362021)
              ·
                refine ⟨106710104264454687255379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569120556077091665362021 106710104264454687255379)
                ·
                  rfl

theorem cell20_701383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_701383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701383 prefixEnd_701383 := by exact prefixLift 701383
  have htrace : WordTrace (prefixWord ++ tailWord_701383) baseStart_701383 baseEnd_701383 := by
    simpa [prefixWord, tailWord_701383, baseEnd_701383] using wordTrace_append hprefix tailTrace_701383
  have hstable : (prefixWord ++ tailWord_701383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701383).length < 2 ^ (prefixWord ++ tailWord_701383).sum := by decide
  have hdescent : baseEnd_701383 < baseStart_701383 := by decide
  rcases family_descends (prefixWord ++ tailWord_701383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701390 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_701390 : Nat := 118140960795 + 701390 * 2 ^ 59
def prefixEnd_701390 : Nat := 4983230072969 + 3 ^ 40 * 701390 * 2
def baseEnd_701390 : Nat := 320133507784103148532775

theorem tailTrace_701390 : CollatzResearch.WordTrace tailWord_701390 prefixEnd_701390 320133507784103148532775 := by
  unfold tailWord_701390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197724366123911590038703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17054529952660861813539749 3197724366123911590038703)
  ·
    refine ⟨4796586549185867385058055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3197724366123911590038703 4796586549185867385058055)
    ·
      refine ⟨7194879823778801077587083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796586549185867385058055 7194879823778801077587083)
      ·
        refine ⟨10792319735668201616380625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194879823778801077587083 10792319735668201616380625)
        ·
          refine ⟨8094239801751151212285469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10792319735668201616380625 8094239801751151212285469)
          ·
            refine ⟨3035339925656681704607051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8094239801751151212285469 3035339925656681704607051)
            ·
              refine ⟨4553009888485022556910577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035339925656681704607051 4553009888485022556910577)
              ·
                refine ⟨3414757416363766917682933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553009888485022556910577 3414757416363766917682933)
                ·
                  refine ⟨320133507784103148532775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3414757416363766917682933 320133507784103148532775)
                  ·
                    rfl

theorem cell20_701390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_701390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701390 prefixEnd_701390 := by exact prefixLift 701390
  have htrace : WordTrace (prefixWord ++ tailWord_701390) baseStart_701390 baseEnd_701390 := by
    simpa [prefixWord, tailWord_701390, baseEnd_701390] using wordTrace_append hprefix tailTrace_701390
  have hstable : (prefixWord ++ tailWord_701390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701390).length < 2 ^ (prefixWord ++ tailWord_701390).sum := by decide
  have hdescent : baseEnd_701390 < baseStart_701390 := by decide
  rcases family_descends (prefixWord ++ tailWord_701390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701410 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_701410 : Nat := 118140960795 + 701410 * 2 ^ 59
def prefixEnd_701410 : Nat := 4983230072969 + 3 ^ 40 * 701410 * 2
def baseEnd_701410 : Nat := 320142636329071967866027

theorem tailTrace_701410 : CollatzResearch.WordTrace tailWord_701410 prefixEnd_701410 320142636329071967866027 := by
  unfold tailWord_701410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395631097229709034009421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17055016259279224090691789 6395631097229709034009421)
  ·
    refine ⟨2398361661461140887753533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6395631097229709034009421 2398361661461140887753533)
    ·
      refine ⟨899385623047927832907575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2398361661461140887753533 899385623047927832907575)
      ·
        refine ⟨1349078434571891749361363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899385623047927832907575 1349078434571891749361363)
        ·
          refine ⟨2023617651857837624042045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349078434571891749361363 2023617651857837624042045)
          ·
            refine ⟨758856619446689109015767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2023617651857837624042045 758856619446689109015767)
            ·
              refine ⟨1138284929170033663523651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758856619446689109015767 1138284929170033663523651)
              ·
                refine ⟨1707427393755050495285477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138284929170033663523651 1707427393755050495285477)
                ·
                  refine ⟨320142636329071967866027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707427393755050495285477 320142636329071967866027)
                  ·
                    rfl

theorem cell20_701410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_701410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701410 prefixEnd_701410 := by exact prefixLift 701410
  have htrace : WordTrace (prefixWord ++ tailWord_701410) baseStart_701410 baseEnd_701410 := by
    simpa [prefixWord, tailWord_701410, baseEnd_701410] using wordTrace_append hprefix tailTrace_701410
  have hstable : (prefixWord ++ tailWord_701410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701410).length < 2 ^ (prefixWord ++ tailWord_701410).sum := by decide
  have hdescent : baseEnd_701410 < baseStart_701410 := by decide
  rcases family_descends (prefixWord ++ tailWord_701410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701449 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_701449 : Nat := 118140960795 + 701449 * 2 ^ 59
def prefixEnd_701449 : Nat := 4983230072969 + 3 ^ 40 * 701449 * 2
def baseEnd_701449 : Nat := 320160436991761165565867

theorem tailTrace_701449 : CollatzResearch.WordTrace tailWord_701449 prefixEnd_701449 320160436991761165565867 := by
  unfold tailWord_701449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25583946835777545796707401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17055964557185030531138267 25583946835777545796707401)
  ·
    refine ⟨19187960126833159347530551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25583946835777545796707401 19187960126833159347530551)
    ·
      refine ⟨28781940190249739021295827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19187960126833159347530551 28781940190249739021295827)
      ·
        refine ⟨43172910285374608531943741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28781940190249739021295827 43172910285374608531943741)
        ·
          refine ⟨16189841357015478199478903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43172910285374608531943741 16189841357015478199478903)
          ·
            refine ⟨24284762035523217299218355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16189841357015478199478903 24284762035523217299218355)
            ·
              refine ⟨36427143053284825948827533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24284762035523217299218355 36427143053284825948827533)
              ·
                refine ⟨13660178644981809730810325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36427143053284825948827533 13660178644981809730810325)
                ·
                  refine ⟨320160436991761165565867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13660178644981809730810325 320160436991761165565867)
                  ·
                    rfl

theorem cell20_701449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_701449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701449 prefixEnd_701449 := by exact prefixLift 701449
  have htrace : WordTrace (prefixWord ++ tailWord_701449) baseStart_701449 baseEnd_701449 := by
    simpa [prefixWord, tailWord_701449, baseEnd_701449] using wordTrace_append hprefix tailTrace_701449
  have hstable : (prefixWord ++ tailWord_701449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701449).length < 2 ^ (prefixWord ++ tailWord_701449).sum := by decide
  have hdescent : baseEnd_701449 < baseStart_701449 := by decide
  rcases family_descends (prefixWord ++ tailWord_701449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701458 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_701458 : Nat := 118140960795 + 701458 * 2 ^ 59
def prefixEnd_701458 : Nat := 4983230072969 + 3 ^ 40 * 701458 * 2
def baseEnd_701458 : Nat := 320164544836997134265831

theorem tailTrace_701458 : CollatzResearch.WordTrace tailWord_701458 prefixEnd_701458 320164544836997134265831 := by
  unfold tailWord_701458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396068773186235083446257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17056183395163293555856685 6396068773186235083446257)
  ·
    refine ⟨4797051579889676312584693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6396068773186235083446257 4797051579889676312584693)
    ·
      refine ⟨449723585614657154304815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4797051579889676312584693 449723585614657154304815)
      ·
        refine ⟨674585378421985731457223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449723585614657154304815 674585378421985731457223)
        ·
          refine ⟨1011878067632978597185835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674585378421985731457223 1011878067632978597185835)
          ·
            refine ⟨1517817101449467895778753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011878067632978597185835 1517817101449467895778753)
            ·
              refine ⟨1138362826087100921834065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517817101449467895778753 1138362826087100921834065)
              ·
                refine ⟨853772119565325691375549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138362826087100921834065 853772119565325691375549)
                ·
                  refine ⟨320164544836997134265831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853772119565325691375549 320164544836997134265831)
                  ·
                    rfl

theorem cell20_701458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_701458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701458 prefixEnd_701458 := by exact prefixLift 701458
  have htrace : WordTrace (prefixWord ++ tailWord_701458) baseStart_701458 baseEnd_701458 := by
    simpa [prefixWord, tailWord_701458, baseEnd_701458] using wordTrace_append hprefix tailTrace_701458
  have hstable : (prefixWord ++ tailWord_701458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701458).length < 2 ^ (prefixWord ++ tailWord_701458).sum := by decide
  have hdescent : baseEnd_701458 < baseStart_701458 := by decide
  rcases family_descends (prefixWord ++ tailWord_701458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701476 : List Nat := [2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_701476 : Nat := 118140960795 + 701476 * 2 ^ 59
def prefixEnd_701476 : Nat := 4983230072969 + 3 ^ 40 * 701476 * 2
def baseEnd_701476 : Nat := 106724253509156357221919

theorem tailTrace_701476 : CollatzResearch.WordTrace tailWord_701476 prefixEnd_701476 106724253509156357221919 := by
  unfold tailWord_701476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792465803339864703970141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17056621071119819605293521 12792465803339864703970141)
  ·
    refine ⟨4797174676252449263988803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12792465803339864703970141 4797174676252449263988803)
    ·
      refine ⟨7195762014378673895983205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797174676252449263988803 7195762014378673895983205)
      ·
        refine ⟨1349205377696001355496851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7195762014378673895983205 1349205377696001355496851)
        ·
          refine ⟨2023808066544002033245277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349205377696001355496851 2023808066544002033245277)
          ·
            refine ⟨758928024954000762466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2023808066544002033245277 758928024954000762466979)
            ·
              refine ⟨1138392037431001143700469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758928024954000762466979 1138392037431001143700469)
              ·
                refine ⟨106724253509156357221919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1138392037431001143700469 106724253509156357221919)
                ·
                  rfl

theorem cell20_701476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_701476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701476 prefixEnd_701476 := by exact prefixLift 701476
  have htrace : WordTrace (prefixWord ++ tailWord_701476) baseStart_701476 baseEnd_701476 := by
    simpa [prefixWord, tailWord_701476, baseEnd_701476] using wordTrace_append hprefix tailTrace_701476
  have hstable : (prefixWord ++ tailWord_701476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701476).length < 2 ^ (prefixWord ++ tailWord_701476).sum := by decide
  have hdescent : baseEnd_701476 < baseStart_701476 := by decide
  rcases family_descends (prefixWord ++ tailWord_701476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701518 : List Nat := [4, 1, 1, 1, 1, 3, 9]
def baseStart_701518 : Nat := 118140960795 + 701518 * 2 ^ 59
def prefixEnd_701518 : Nat := 4983230072969 + 3 ^ 40 * 701518 * 2
def baseEnd_701518 : Nat := 35576881163544843585065

theorem tailTrace_701518 : CollatzResearch.WordTrace tailWord_701518 prefixEnd_701518 35576881163544843585065 := by
  unfold tailWord_701518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198307934065946322621151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17057642315018380387312805 3198307934065946322621151)
  ·
    refine ⟨4797461901098919483931727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3198307934065946322621151 4797461901098919483931727)
    ·
      refine ⟨7196192851648379225897591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797461901098919483931727 7196192851648379225897591)
      ·
        refine ⟨10794289277472568838846387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196192851648379225897591 10794289277472568838846387)
        ·
          refine ⟨16191433916208853258269581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10794289277472568838846387 16191433916208853258269581)
          ·
            refine ⟨6071787718578319971851093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16191433916208853258269581 6071787718578319971851093)
            ·
              refine ⟨35576881163544843585065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6071787718578319971851093 35576881163544843585065)
              ·
                rfl

theorem cell20_701518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_701518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701518 prefixEnd_701518 := by exact prefixLift 701518
  have htrace : WordTrace (prefixWord ++ tailWord_701518) baseStart_701518 baseEnd_701518 := by
    simpa [prefixWord, tailWord_701518, baseEnd_701518] using wordTrace_append hprefix tailTrace_701518
  have hstable : (prefixWord ++ tailWord_701518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701518).length < 2 ^ (prefixWord ++ tailWord_701518).sum := by decide
  have hdescent : baseEnd_701518 < baseStart_701518 := by decide
  rcases family_descends (prefixWord ++ tailWord_701518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701528 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_701528 : Nat := 118140960795 + 701528 * 2 ^ 59
def prefixEnd_701528 : Nat := 4983230072969 + 3 ^ 40 * 701528 * 2
def baseEnd_701528 : Nat := 320196494744388001932211

theorem tailTrace_701528 : CollatzResearch.WordTrace tailWord_701528 prefixEnd_701528 320196494744388001932211 := by
  unfold tailWord_701528
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793414101245671144416619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17057885468327561525888825 12793414101245671144416619)
  ·
    refine ⟨19190121151868506716624929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12793414101245671144416619 19190121151868506716624929)
    ·
      refine ⟨14392590863901380037468697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19190121151868506716624929 14392590863901380037468697)
      ·
        refine ⟨10794443147926035028101523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14392590863901380037468697 10794443147926035028101523)
        ·
          refine ⟨16191664721889052542152285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10794443147926035028101523 16191664721889052542152285)
          ·
            refine ⟨6071874270708394703307107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16191664721889052542152285 6071874270708394703307107)
            ·
              refine ⟨9107811406062592054960661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071874270708394703307107 9107811406062592054960661)
              ·
                refine ⟨426928659659184002576281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9107811406062592054960661 426928659659184002576281)
                ·
                  refine ⟨320196494744388001932211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426928659659184002576281 320196494744388001932211)
                  ·
                    rfl

theorem cell20_701528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_701528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701528 prefixEnd_701528 := by exact prefixLift 701528
  have htrace : WordTrace (prefixWord ++ tailWord_701528) baseStart_701528 baseEnd_701528 := by
    simpa [prefixWord, tailWord_701528, baseEnd_701528] using wordTrace_append hprefix tailTrace_701528
  have hstable : (prefixWord ++ tailWord_701528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701528).length < 2 ^ (prefixWord ++ tailWord_701528).sum := by decide
  have hdescent : baseEnd_701528 < baseStart_701528 := by decide
  rcases family_descends (prefixWord ++ tailWord_701528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701534 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_701534 : Nat := 118140960795 + 701534 * 2 ^ 59
def prefixEnd_701534 : Nat := 4983230072969 + 3 ^ 40 * 701534 * 2
def baseEnd_701534 : Nat := 320199233307878647732187

theorem tailTrace_701534 : CollatzResearch.WordTrace tailWord_701534 prefixEnd_701534 320199233307878647732187 := by
  unfold tailWord_701534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198380880058700664193957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17058031360313070209034437 3198380880058700664193957)
  ·
    refine ⟨599696415011006374536367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3198380880058700664193957 599696415011006374536367)
    ·
      refine ⟨899544622516509561804551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599696415011006374536367 899544622516509561804551)
      ·
        refine ⟨1349316933774764342706827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899544622516509561804551 1349316933774764342706827)
        ·
          refine ⟨2023975400662146514060241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349316933774764342706827 2023975400662146514060241)
          ·
            refine ⟨1517981550496609885545181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023975400662146514060241 1517981550496609885545181)
            ·
              refine ⟨569243081436228707079443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1517981550496609885545181 569243081436228707079443)
              ·
                refine ⟨853864622154343060619165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569243081436228707079443 853864622154343060619165)
                ·
                  refine ⟨320199233307878647732187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853864622154343060619165 320199233307878647732187)
                  ·
                    rfl

theorem cell20_701534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_701534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701534 prefixEnd_701534 := by exact prefixLift 701534
  have htrace : WordTrace (prefixWord ++ tailWord_701534) baseStart_701534 baseEnd_701534 := by
    simpa [prefixWord, tailWord_701534, baseEnd_701534] using wordTrace_append hprefix tailTrace_701534
  have hstable : (prefixWord ++ tailWord_701534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701534).length < 2 ^ (prefixWord ++ tailWord_701534).sum := by decide
  have hdescent : baseEnd_701534 < baseStart_701534 := by decide
  rcases family_descends (prefixWord ++ tailWord_701534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701573 : List Nat := [1, 3, 1, 1, 6, 2, 6]
def baseStart_701573 : Nat := 118140960795 + 701573 * 2 ^ 59
def prefixEnd_701573 : Nat := 4983230072969 + 3 ^ 40 * 701573 * 2
def baseEnd_701573 : Nat := 35579670441174205048003

theorem tailTrace_701573 : CollatzResearch.WordTrace tailWord_701573 prefixEnd_701573 35579670441174205048003 := by
  unfold tailWord_701573
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588469487328314974221373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17058979658218876649480915 25588469487328314974221373)
  ·
    refine ⟨9595676057748118115333015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25588469487328314974221373 9595676057748118115333015)
    ·
      refine ⟨14393514086622177172999523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9595676057748118115333015 14393514086622177172999523)
      ·
        refine ⟨21590271129933265759499285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14393514086622177172999523 21590271129933265759499285)
        ·
          refine ⟨1012043959215621832476529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21590271129933265759499285 1012043959215621832476529)
          ·
            refine ⟨759032969411716374357397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012043959215621832476529 759032969411716374357397)
            ·
              refine ⟨35579670441174205048003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 759032969411716374357397 35579670441174205048003)
              ·
                rfl

theorem cell20_701573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_701573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701573 prefixEnd_701573 := by exact prefixLift 701573
  have htrace : WordTrace (prefixWord ++ tailWord_701573) baseStart_701573 baseEnd_701573 := by
    simpa [prefixWord, tailWord_701573, baseEnd_701573] using wordTrace_append hprefix tailTrace_701573
  have hstable : (prefixWord ++ tailWord_701573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701573).length < 2 ^ (prefixWord ++ tailWord_701573).sum := by decide
  have hdescent : baseEnd_701573 < baseStart_701573 := by decide
  rcases family_descends (prefixWord ++ tailWord_701573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701587 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_701587 : Nat := 118140960795 + 701587 * 2 ^ 59
def prefixEnd_701587 : Nat := 4983230072969 + 3 ^ 40 * 701587 * 2
def baseEnd_701587 : Nat := 320223423952046018965303

theorem tailTrace_701587 : CollatzResearch.WordTrace tailWord_701587 prefixEnd_701587 320223423952046018965303 := by
  unfold tailWord_701587
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588980109277595365231015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17059320072851730243487343 25588980109277595365231015)
  ·
    refine ⟨38383470163916393047846523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25588980109277595365231015 38383470163916393047846523)
    ·
      refine ⟨57575205245874589571769785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38383470163916393047846523 57575205245874589571769785)
      ·
        refine ⟨43181403934405942178827339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57575205245874589571769785 43181403934405942178827339)
        ·
          refine ⟨64772105901608913268241009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43181403934405942178827339 64772105901608913268241009)
          ·
            refine ⟨48579079426206684951180757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64772105901608913268241009 48579079426206684951180757)
            ·
              refine ⟨1138572174051719178543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48579079426206684951180757 1138572174051719178543299)
              ·
                refine ⟨1707858261077578767814949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138572174051719178543299 1707858261077578767814949)
                ·
                  refine ⟨320223423952046018965303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707858261077578767814949 320223423952046018965303)
                  ·
                    rfl

theorem cell20_701587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_701587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701587 prefixEnd_701587 := by exact prefixLift 701587
  have htrace : WordTrace (prefixWord ++ tailWord_701587) baseStart_701587 baseEnd_701587 := by
    simpa [prefixWord, tailWord_701587, baseEnd_701587] using wordTrace_append hprefix tailTrace_701587
  have hstable : (prefixWord ++ tailWord_701587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701587).length < 2 ^ (prefixWord ++ tailWord_701587).sum := by decide
  have hdescent : baseEnd_701587 < baseStart_701587 := by decide
  rcases family_descends (prefixWord ++ tailWord_701587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701632 : List Nat := [2, 1, 1, 2, 6, 8]
def baseStart_701632 : Nat := 118140960795 + 701632 * 2 ^ 59
def prefixEnd_701632 : Nat := 4983230072969 + 3 ^ 40 * 701632 * 2
def baseEnd_701632 : Nat := 11860887525119476387597

theorem tailTrace_701632 : CollatzResearch.WordTrace tailWord_701632 prefixEnd_701632 11860887525119476387597 := by
  unfold tailWord_701632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795310697057284025309575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17060414262743045367079433 12795310697057284025309575)
  ·
    refine ⟨19192966045585926037964363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12795310697057284025309575 19192966045585926037964363)
    ·
      refine ⟨28789449068378889056946545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19192966045585926037964363 28789449068378889056946545)
      ·
        refine ⟨21592086801284166792709909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28789449068378889056946545 21592086801284166792709909)
        ·
          refine ⟨1012129068810195318408277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21592086801284166792709909 1012129068810195318408277)
          ·
            refine ⟨11860887525119476387597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1012129068810195318408277 11860887525119476387597)
            ·
              rfl

theorem cell20_701632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 8].length) (baseStart_701632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701632 prefixEnd_701632 := by exact prefixLift 701632
  have htrace : WordTrace (prefixWord ++ tailWord_701632) baseStart_701632 baseEnd_701632 := by
    simpa [prefixWord, tailWord_701632, baseEnd_701632] using wordTrace_append hprefix tailTrace_701632
  have hstable : (prefixWord ++ tailWord_701632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701632).length < 2 ^ (prefixWord ++ tailWord_701632).sum := by decide
  have hdescent : baseEnd_701632 < baseStart_701632 := by decide
  rcases family_descends (prefixWord ++ tailWord_701632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701639 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_701639 : Nat := 118140960795 + 701639 * 2 ^ 59
def prefixEnd_701639 : Nat := 4983230072969 + 3 ^ 40 * 701639 * 2
def baseEnd_701639 : Nat := 320247158168964949231757

theorem tailTrace_701639 : CollatzResearch.WordTrace tailWord_701639 prefixEnd_701639 320247158168964949231757 := by
  unfold tailWord_701639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590876705089208246123971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17060584470059472164082647 25590876705089208246123971)
  ·
    refine ⟨38386315057633812369185957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25590876705089208246123971 38386315057633812369185957)
    ·
      refine ⟨7197434073306339819222367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38386315057633812369185957 7197434073306339819222367)
      ·
        refine ⟨10796151109959509728833551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197434073306339819222367 10796151109959509728833551)
        ·
          refine ⟨16194226664939264593250327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10796151109959509728833551 16194226664939264593250327)
          ·
            refine ⟨24291339997408896889875491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16194226664939264593250327 24291339997408896889875491)
            ·
              refine ⟨36437009996113345334813237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24291339997408896889875491 36437009996113345334813237)
              ·
                refine ⟨3415969687135626125138741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36437009996113345334813237 3415969687135626125138741)
                ·
                  refine ⟨320247158168964949231757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3415969687135626125138741 320247158168964949231757)
                  ·
                    rfl

theorem cell20_701639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_701639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701639 prefixEnd_701639 := by exact prefixLift 701639
  have htrace : WordTrace (prefixWord ++ tailWord_701639) baseStart_701639 baseEnd_701639 := by
    simpa [prefixWord, tailWord_701639, baseEnd_701639] using wordTrace_append hprefix tailTrace_701639
  have hstable : (prefixWord ++ tailWord_701639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701639).length < 2 ^ (prefixWord ++ tailWord_701639).sum := by decide
  have hdescent : baseEnd_701639 < baseStart_701639 := by decide
  rcases family_descends (prefixWord ++ tailWord_701639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701701 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_701701 : Nat := 118140960795 + 701701 * 2 ^ 59
def prefixEnd_701701 : Nat := 4983230072969 + 3 ^ 40 * 701701 * 2
def baseEnd_701701 : Nat := 320275456658368289164837

theorem tailTrace_701701 : CollatzResearch.WordTrace tailWord_701701 prefixEnd_701701 320275456658368289164837 := by
  unfold tailWord_701701
  simp only [CollatzResearch.WordTrace]
  refine ⟨25593138030864592834880957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17062092020576395223253971 25593138030864592834880957)
  ·
    refine ⟨9597426761574222313080359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25593138030864592834880957 9597426761574222313080359)
    ·
      refine ⟨14396140142361333469620539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597426761574222313080359 14396140142361333469620539)
      ·
        refine ⟨21594210213542000204430809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396140142361333469620539 21594210213542000204430809)
        ·
          refine ⟨16195657660156500153323107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21594210213542000204430809 16195657660156500153323107)
          ·
            refine ⟨24293486490234750229984661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16195657660156500153323107 24293486490234750229984661)
            ·
              refine ⟨1138757179229753917030531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24293486490234750229984661 1138757179229753917030531)
              ·
                refine ⟨1708135768844630875545797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138757179229753917030531 1708135768844630875545797)
                ·
                  refine ⟨320275456658368289164837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708135768844630875545797 320275456658368289164837)
                  ·
                    rfl

theorem cell20_701701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_701701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701701 prefixEnd_701701 := by exact prefixLift 701701
  have htrace : WordTrace (prefixWord ++ tailWord_701701) baseStart_701701 baseEnd_701701 := by
    simpa [prefixWord, tailWord_701701, baseEnd_701701] using wordTrace_append hprefix tailTrace_701701
  have hstable : (prefixWord ++ tailWord_701701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701701).length < 2 ^ (prefixWord ++ tailWord_701701).sum := by decide
  have hdescent : baseEnd_701701 < baseStart_701701 := by decide
  rcases family_descends (prefixWord ++ tailWord_701701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701725 : List Nat := [1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_701725 : Nat := 118140960795 + 701725 * 2 ^ 59
def prefixEnd_701725 : Nat := 4983230072969 + 3 ^ 40 * 701725 * 2
def baseEnd_701725 : Nat := 106762136970776957454913

theorem tailTrace_701725 : CollatzResearch.WordTrace tailWord_701725 prefixEnd_701725 106762136970776957454913 := by
  unfold tailWord_701725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25594013382777644933754629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17062675588518429955836419 25594013382777644933754629)
  ·
    refine ⟨4798877509270808425078993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25594013382777644933754629 4798877509270808425078993)
    ·
      refine ⟨3599158131953106318809245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4798877509270808425078993 3599158131953106318809245)
      ·
        refine ⟨1349684299482414869553467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3599158131953106318809245 1349684299482414869553467)
        ·
          refine ⟨2024526449223622304330201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349684299482414869553467 2024526449223622304330201)
          ·
            refine ⟨1518394836917716728247651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024526449223622304330201 1518394836917716728247651)
            ·
              refine ⟨2277592255376575092371477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518394836917716728247651 2277592255376575092371477)
              ·
                refine ⟨106762136970776957454913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2277592255376575092371477 106762136970776957454913)
                ·
                  rfl

theorem cell20_701725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_701725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701725 prefixEnd_701725 := by exact prefixLift 701725
  have htrace : WordTrace (prefixWord ++ tailWord_701725) baseStart_701725 baseEnd_701725 := by
    simpa [prefixWord, tailWord_701725, baseEnd_701725] using wordTrace_append hprefix tailTrace_701725
  have hstable : (prefixWord ++ tailWord_701725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701725).length < 2 ^ (prefixWord ++ tailWord_701725).sum := by decide
  have hdescent : baseEnd_701725 < baseStart_701725 := by decide
  rcases family_descends (prefixWord ++ tailWord_701725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701746 : List Nat := [3, 2, 1, 1, 4, 1, 8]
def baseStart_701746 : Nat := 118140960795 + 701746 * 2 ^ 59
def prefixEnd_701746 : Nat := 4983230072969 + 3 ^ 40 * 701746 * 2
def baseEnd_701746 : Nat := 35588443987172014740517

theorem tailTrace_701746 : CollatzResearch.WordTrace tailWord_701746 prefixEnd_701746 35588443987172014740517 := by
  unfold tailWord_701746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398694828925391380067273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17063186210467710346846061 6398694828925391380067273)
  ·
    refine ⟨4799021121694043535050455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6398694828925391380067273 4799021121694043535050455)
    ·
      refine ⟨7198531682541065302575683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799021121694043535050455 7198531682541065302575683)
      ·
        refine ⟨10797797523811597953863525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7198531682541065302575683 10797797523811597953863525)
        ·
          refine ⟨2024587035714674616349411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10797797523811597953863525 2024587035714674616349411)
          ·
            refine ⟨3036880553572011924524117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024587035714674616349411 3036880553572011924524117)
            ·
              refine ⟨35588443987172014740517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3036880553572011924524117 35588443987172014740517)
              ·
                rfl

theorem cell20_701746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_701746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701746 prefixEnd_701746 := by exact prefixLift 701746
  have htrace : WordTrace (prefixWord ++ tailWord_701746) baseStart_701746 baseEnd_701746 := by
    simpa [prefixWord, tailWord_701746, baseEnd_701746] using wordTrace_append hprefix tailTrace_701746
  have hstable : (prefixWord ++ tailWord_701746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701746).length < 2 ^ (prefixWord ++ tailWord_701746).sum := by decide
  have hdescent : baseEnd_701746 < baseStart_701746 := by decide
  rcases family_descends (prefixWord ++ tailWord_701746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701756 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_701756 : Nat := 118140960795 + 701756 * 2 ^ 59
def prefixEnd_701756 : Nat := 4983230072969 + 3 ^ 40 * 701756 * 2
def baseEnd_701756 : Nat := 320300560157032542331279

theorem tailTrace_701756 : CollatzResearch.WordTrace tailWord_701756 prefixEnd_701756 320300560157032542331279 := by
  unfold tailWord_701756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12797572022832668614066561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17063429363776891485422081 12797572022832668614066561)
  ·
    refine ⟨9598179017124501460549921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12797572022832668614066561 9598179017124501460549921)
    ·
      refine ⟨7198634262843376095412441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9598179017124501460549921 7198634262843376095412441)
      ·
        refine ⟨5398975697132532071559331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7198634262843376095412441 5398975697132532071559331)
        ·
          refine ⟨8098463545698798107338997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398975697132532071559331 8098463545698798107338997)
          ·
            refine ⟨759230957409262322563031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8098463545698798107338997 759230957409262322563031)
            ·
              refine ⟨1138846436113893483844547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759230957409262322563031 1138846436113893483844547)
              ·
                refine ⟨1708269654170840225766821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138846436113893483844547 1708269654170840225766821)
                ·
                  refine ⟨320300560157032542331279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708269654170840225766821 320300560157032542331279)
                  ·
                    rfl

theorem cell20_701756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_701756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701756 prefixEnd_701756 := by exact prefixLift 701756
  have htrace : WordTrace (prefixWord ++ tailWord_701756) baseStart_701756 baseEnd_701756 := by
    simpa [prefixWord, tailWord_701756, baseEnd_701756] using wordTrace_append hprefix tailTrace_701756
  have hstable : (prefixWord ++ tailWord_701756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701756).length < 2 ^ (prefixWord ++ tailWord_701756).sum := by decide
  have hdescent : baseEnd_701756 < baseStart_701756 := by decide
  rcases family_descends (prefixWord ++ tailWord_701756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701808 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_701808 : Nat := 118140960795 + 701808 * 2 ^ 59
def prefixEnd_701808 : Nat := 4983230072969 + 3 ^ 40 * 701808 * 2
def baseEnd_701808 : Nat := 320324294373951472597733

theorem tailTrace_701808 : CollatzResearch.WordTrace tailWord_701808 prefixEnd_701808 320324294373951472597733 := by
  unfold tailWord_701808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12798520320738475054513039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17064693760984633406017385 12798520320738475054513039)
  ·
    refine ⟨19197780481107712581769559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12798520320738475054513039 19197780481107712581769559)
    ·
      refine ⟨28796670721661568872654339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19197780481107712581769559 28796670721661568872654339)
      ·
        refine ⟨43195006082492353308981509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28796670721661568872654339 43195006082492353308981509)
        ·
          refine ⟨8099063640467316245434033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43195006082492353308981509 8099063640467316245434033)
          ·
            refine ⟨6074297730350487184075525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8099063640467316245434033 6074297730350487184075525)
            ·
              refine ⟨1138930824440716347014161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6074297730350487184075525 1138930824440716347014161)
              ·
                refine ⟨854198118330537260260621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138930824440716347014161 854198118330537260260621)
                ·
                  refine ⟨320324294373951472597733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854198118330537260260621 320324294373951472597733)
                  ·
                    rfl

theorem cell20_701808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_701808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701808 prefixEnd_701808 := by exact prefixLift 701808
  have htrace : WordTrace (prefixWord ++ tailWord_701808) baseStart_701808 baseEnd_701808 := by
    simpa [prefixWord, tailWord_701808, baseEnd_701808] using wordTrace_append hprefix tailTrace_701808
  have hstable : (prefixWord ++ tailWord_701808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701808).length < 2 ^ (prefixWord ++ tailWord_701808).sum := by decide
  have hdescent : baseEnd_701808 < baseStart_701808 := by decide
  rcases family_descends (prefixWord ++ tailWord_701808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701890 : List Nat := [3, 5, 2, 1, 1, 1, 1, 6]
def baseStart_701890 : Nat := 118140960795 + 701890 * 2 ^ 59
def prefixEnd_701890 : Nat := 4983230072969 + 3 ^ 40 * 701890 * 2
def baseEnd_701890 : Nat := 106787240469441210621355

theorem tailTrace_701890 : CollatzResearch.WordTrace tailWord_701890 prefixEnd_701890 106787240469441210621355 := by
  unfold tailWord_701890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6400007856794969528377781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17066687618119918742340749 6400007856794969528377781)
  ·
    refine ⟨600000736574528393285417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6400007856794969528377781 600000736574528393285417)
    ·
      refine ⟨450000552430896294964063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 600000736574528393285417 450000552430896294964063)
      ·
        refine ⟨675000828646344442446095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450000552430896294964063 675000828646344442446095)
        ·
          refine ⟨1012501242969516663669143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675000828646344442446095 1012501242969516663669143)
          ·
            refine ⟨1518751864454274995503715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012501242969516663669143 1518751864454274995503715)
            ·
              refine ⟨2278127796681412493255573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518751864454274995503715 2278127796681412493255573)
              ·
                refine ⟨106787240469441210621355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2278127796681412493255573 106787240469441210621355)
                ·
                  rfl

theorem cell20_701890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_701890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701890 prefixEnd_701890 := by exact prefixLift 701890
  have htrace : WordTrace (prefixWord ++ tailWord_701890) baseStart_701890 baseEnd_701890 := by
    simpa [prefixWord, tailWord_701890, baseEnd_701890] using wordTrace_append hprefix tailTrace_701890
  have hstable : (prefixWord ++ tailWord_701890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701890).length < 2 ^ (prefixWord ++ tailWord_701890).sum := by decide
  have hdescent : baseEnd_701890 < baseStart_701890 := by decide
  rcases family_descends (prefixWord ++ tailWord_701890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701898 : List Nat := [3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_701898 : Nat := 118140960795 + 701898 * 2 ^ 59
def prefixEnd_701898 : Nat := 4983230072969 + 3 ^ 40 * 701898 * 2
def baseEnd_701898 : Nat := 106788457608770386532455

theorem tailTrace_701898 : CollatzResearch.WordTrace tailWord_701898 prefixEnd_701898 106788457608770386532455 := by
  unfold tailWord_701898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6400080802787723869950587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17066882140767263653201565 6400080802787723869950587)
  ·
    refine ⟨9600121204181585804925881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6400080802787723869950587 9600121204181585804925881)
    ·
      refine ⟨7200090903136189353694411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9600121204181585804925881 7200090903136189353694411)
      ·
        refine ⟨10800136354704284030541617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200090903136189353694411 10800136354704284030541617)
        ·
          refine ⟨8100102266028213022906213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10800136354704284030541617 8100102266028213022906213)
          ·
            refine ⟨1518769174880289941794915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8100102266028213022906213 1518769174880289941794915)
            ·
              refine ⟨2278153762320434912692373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518769174880289941794915 2278153762320434912692373)
              ·
                refine ⟨106788457608770386532455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2278153762320434912692373 106788457608770386532455)
                ·
                  rfl

theorem cell20_701898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_701898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701898 prefixEnd_701898 := by exact prefixLift 701898
  have htrace : WordTrace (prefixWord ++ tailWord_701898) baseStart_701898 baseEnd_701898 := by
    simpa [prefixWord, tailWord_701898, baseEnd_701898] using wordTrace_append hprefix tailTrace_701898
  have hstable : (prefixWord ++ tailWord_701898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701898).length < 2 ^ (prefixWord ++ tailWord_701898).sum := by decide
  have hdescent : baseEnd_701898 < baseStart_701898 := by decide
  rcases family_descends (prefixWord ++ tailWord_701898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701912 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_701912 : Nat := 118140960795 + 701912 * 2 ^ 59
def prefixEnd_701912 : Nat := 4983230072969 + 3 ^ 40 * 701912 * 2
def baseEnd_701912 : Nat := 320371762807789333130641

theorem tailTrace_701912 : CollatzResearch.WordTrace tailWord_701912 prefixEnd_701912 320371762807789333130641 := by
  unfold tailWord_701912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12800416916550087935405995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17067222555400117247207993 12800416916550087935405995)
  ·
    refine ⟨19200625374825131903108993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12800416916550087935405995 19200625374825131903108993)
    ·
      refine ⟨14400469031118848927331745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19200625374825131903108993 14400469031118848927331745)
      ·
        refine ⟨10800351773339136695498809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14400469031118848927331745 10800351773339136695498809)
        ·
          refine ⟨8100263830004352521624107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10800351773339136695498809 8100263830004352521624107)
          ·
            refine ⟨12150395745006528782436161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8100263830004352521624107 12150395745006528782436161)
            ·
              refine ⟨9112796808754896586827121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12150395745006528782436161 9112796808754896586827121)
              ·
                refine ⟨6834597606566172440120341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9112796808754896586827121 6834597606566172440120341)
                ·
                  refine ⟨320371762807789333130641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6834597606566172440120341 320371762807789333130641)
                  ·
                    rfl

theorem cell20_701912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_701912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701912 prefixEnd_701912 := by exact prefixLift 701912
  have htrace : WordTrace (prefixWord ++ tailWord_701912) baseStart_701912 baseEnd_701912 := by
    simpa [prefixWord, tailWord_701912, baseEnd_701912] using wordTrace_append hprefix tailTrace_701912
  have hstable : (prefixWord ++ tailWord_701912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701912).length < 2 ^ (prefixWord ++ tailWord_701912).sum := by decide
  have hdescent : baseEnd_701912 < baseStart_701912 := by decide
  rcases family_descends (prefixWord ++ tailWord_701912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701936 : List Nat := [2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_701936 : Nat := 118140960795 + 701936 * 2 ^ 59
def prefixEnd_701936 : Nat := 4983230072969 + 3 ^ 40 * 701936 * 2
def baseEnd_701936 : Nat := 106794239020583972110181

theorem tailTrace_701936 : CollatzResearch.WordTrace tailWord_701936 prefixEnd_701936 106794239020583972110181 := by
  unfold tailWord_701936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12800854592506613984842831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17067806123342151979790441 12800854592506613984842831)
  ·
    refine ⟨19201281888759920977264247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12800854592506613984842831 19201281888759920977264247)
    ·
      refine ⟨28801922833139881465896371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19201281888759920977264247 28801922833139881465896371)
      ·
        refine ⟨43202884249709822198844557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28801922833139881465896371 43202884249709822198844557)
        ·
          refine ⟨16201081593641183324566709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43202884249709822198844557 16201081593641183324566709)
          ·
            refine ⟨1518851399403860936678129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16201081593641183324566709 1518851399403860936678129)
            ·
              refine ⟨1139138549552895702508597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518851399403860936678129 1139138549552895702508597)
              ·
                refine ⟨106794239020583972110181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1139138549552895702508597 106794239020583972110181)
                ·
                  rfl

theorem cell20_701936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_701936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_701936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_701936 prefixEnd_701936 := by exact prefixLift 701936
  have htrace : WordTrace (prefixWord ++ tailWord_701936) baseStart_701936 baseEnd_701936 := by
    simpa [prefixWord, tailWord_701936, baseEnd_701936] using wordTrace_append hprefix tailTrace_701936
  have hstable : (prefixWord ++ tailWord_701936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701936).length < 2 ^ (prefixWord ++ tailWord_701936).sum := by decide
  have hdescent : baseEnd_701936 < baseStart_701936 := by decide
  rcases family_descends (prefixWord ++ tailWord_701936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702005 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_702005 : Nat := 118140960795 + 702005 * 2 ^ 59
def prefixEnd_702005 : Nat := 4983230072969 + 3 ^ 40 * 702005 * 2
def baseEnd_702005 : Nat := 320414210541894343030261

theorem tailTrace_702005 : CollatzResearch.WordTrace tailWord_702005 prefixEnd_702005 320414210541894343030261 := by
  unfold tailWord_702005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604225821763252753947469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17069483881175501835964979 25604225821763252753947469)
  ·
    refine ⟨9601584683161219782730301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25604225821763252753947469 9601584683161219782730301)
    ·
      refine ⟨3600594256185457418523863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9601584683161219782730301 3600594256185457418523863)
      ·
        refine ⟨5400891384278186127785795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3600594256185457418523863 5400891384278186127785795)
        ·
          refine ⟨8101337076417279191678693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5400891384278186127785795 8101337076417279191678693)
          ·
            refine ⟨1519000701828239848439755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8101337076417279191678693 1519000701828239848439755)
            ·
              refine ⟨2278501052742359772659633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519000701828239848439755 2278501052742359772659633)
              ·
                refine ⟨1708875789556769829494725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278501052742359772659633 1708875789556769829494725)
                ·
                  refine ⟨320414210541894343030261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708875789556769829494725 320414210541894343030261)
                  ·
                    rfl

theorem cell20_702005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_702005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702005 prefixEnd_702005 := by exact prefixLift 702005
  have htrace : WordTrace (prefixWord ++ tailWord_702005) baseStart_702005 baseEnd_702005 := by
    simpa [prefixWord, tailWord_702005, baseEnd_702005] using wordTrace_append hprefix tailTrace_702005
  have hstable : (prefixWord ++ tailWord_702005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702005).length < 2 ^ (prefixWord ++ tailWord_702005).sum := by decide
  have hdescent : baseEnd_702005 < baseStart_702005 := by decide
  rcases family_descends (prefixWord ++ tailWord_702005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702026 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_702026 : Nat := 118140960795 + 702026 * 2 ^ 59
def prefixEnd_702026 : Nat := 4983230072969 + 3 ^ 40 * 702026 * 2
def baseEnd_702026 : Nat := 320423795514111603330175

theorem tailTrace_702026 : CollatzResearch.WordTrace tailWord_702026 prefixEnd_702026 320423795514111603330175 := by
  unfold tailWord_702026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401247938671793335115483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17069994503124782226974621 6401247938671793335115483)
  ·
    refine ⟨9601871908007690002673225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401247938671793335115483 9601871908007690002673225)
    ·
      refine ⟨7201403931005767502004919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9601871908007690002673225 7201403931005767502004919)
      ·
        refine ⟨10802105896508651253007379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201403931005767502004919 10802105896508651253007379)
        ·
          refine ⟨16203158844762976879511069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10802105896508651253007379 16203158844762976879511069)
          ·
            refine ⟨6076184566786116329816651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16203158844762976879511069 6076184566786116329816651)
            ·
              refine ⟨9114276850179174494724977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076184566786116329816651 9114276850179174494724977)
              ·
                refine ⟨6835707637634380871043733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9114276850179174494724977 6835707637634380871043733)
                ·
                  refine ⟨320423795514111603330175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6835707637634380871043733 320423795514111603330175)
                  ·
                    rfl

theorem cell20_702026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_702026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702026 prefixEnd_702026 := by exact prefixLift 702026
  have htrace : WordTrace (prefixWord ++ tailWord_702026) baseStart_702026 baseEnd_702026 := by
    simpa [prefixWord, tailWord_702026, baseEnd_702026] using wordTrace_append hprefix tailTrace_702026
  have hstable : (prefixWord ++ tailWord_702026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702026).length < 2 ^ (prefixWord ++ tailWord_702026).sum := by decide
  have hdescent : baseEnd_702026 < baseStart_702026 := by decide
  rcases family_descends (prefixWord ++ tailWord_702026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702029 : List Nat := [1, 6, 1, 1, 3, 1, 7]
def baseStart_702029 : Nat := 118140960795 + 702029 * 2 ^ 59
def prefixEnd_702029 : Nat := 4983230072969 + 3 ^ 40 * 702029 * 2
def baseEnd_702029 : Nat := 35602796088428547358907

theorem tailTrace_702029 : CollatzResearch.WordTrace tailWord_702029 prefixEnd_702029 35602796088428547358907 := by
  unfold tailWord_702029
  simp only [CollatzResearch.WordTrace]
  refine ⟨25605101173676304852821141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17070067449117536568547427 25605101173676304852821141)
  ·
    refine ⟨1200239117516076789975991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25605101173676304852821141 1200239117516076789975991)
    ·
      refine ⟨1800358676274115184963987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200239117516076789975991 1800358676274115184963987)
      ·
        refine ⟨2700538014411172777445981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800358676274115184963987 2700538014411172777445981)
        ·
          refine ⟨1012701755404189791542243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2700538014411172777445981 1012701755404189791542243)
          ·
            refine ⟨1519052633106284687313365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012701755404189791542243 1519052633106284687313365)
            ·
              refine ⟨35602796088428547358907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1519052633106284687313365 35602796088428547358907)
              ·
                rfl

theorem cell20_702029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_702029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702029 prefixEnd_702029 := by exact prefixLift 702029
  have htrace : WordTrace (prefixWord ++ tailWord_702029) baseStart_702029 baseEnd_702029 := by
    simpa [prefixWord, tailWord_702029, baseEnd_702029] using wordTrace_append hprefix tailTrace_702029
  have hstable : (prefixWord ++ tailWord_702029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702029).length < 2 ^ (prefixWord ++ tailWord_702029).sum := by decide
  have hdescent : baseEnd_702029 < baseStart_702029 := by decide
  rcases family_descends (prefixWord ++ tailWord_702029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702033 : List Nat := [1, 2, 2, 1, 3, 2, 9]
def baseStart_702033 : Nat := 118140960795 + 702033 * 2 ^ 59
def prefixEnd_702033 : Nat := 4983230072969 + 3 ^ 40 * 702033 * 2
def baseEnd_702033 : Nat := 35602998944983410010757

theorem tailTrace_702033 : CollatzResearch.WordTrace tailWord_702033 prefixEnd_702033 35602998944983410010757 := by
  unfold tailWord_702033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25605247065661813535966753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17070164710441209023977835 25605247065661813535966753)
  ·
    refine ⟨19203935299246360151975065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25605247065661813535966753 19203935299246360151975065)
    ·
      refine ⟨14402951474434770113981299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19203935299246360151975065 14402951474434770113981299)
      ·
        refine ⟨21604427211652155170971949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14402951474434770113981299 21604427211652155170971949)
        ·
          refine ⟨8101660204369558189114481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21604427211652155170971949 8101660204369558189114481)
          ·
            refine ⟨6076245153277168641835861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8101660204369558189114481 6076245153277168641835861)
            ·
              refine ⟨35602998944983410010757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6076245153277168641835861 35602998944983410010757)
              ·
                rfl

theorem cell20_702033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_702033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702033 prefixEnd_702033 := by exact prefixLift 702033
  have htrace : WordTrace (prefixWord ++ tailWord_702033) baseStart_702033 baseEnd_702033 := by
    simpa [prefixWord, tailWord_702033, baseEnd_702033] using wordTrace_append hprefix tailTrace_702033
  have hstable : (prefixWord ++ tailWord_702033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702033).length < 2 ^ (prefixWord ++ tailWord_702033).sum := by decide
  have hdescent : baseEnd_702033 < baseStart_702033 := by decide
  rcases family_descends (prefixWord ++ tailWord_702033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702053 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 3]
def baseStart_702053 : Nat := 118140960795 + 702053 * 2 ^ 59
def prefixEnd_702053 : Nat := 4983230072969 + 3 ^ 40 * 702053 * 2
def baseEnd_702053 : Nat := 320436119049819509430065

theorem tailTrace_702053 : CollatzResearch.WordTrace tailWord_702053 prefixEnd_702053 320436119049819509430065 := by
  unfold tailWord_702053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25605976525589356951694813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17070651017059571301129875 25605976525589356951694813)
  ·
    refine ⟨9602241197096008856885555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25605976525589356951694813 9602241197096008856885555)
    ·
      refine ⟨14403361795644013285328333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602241197096008856885555 14403361795644013285328333)
      ·
        refine ⟨5401260673366504981998125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14403361795644013285328333 5401260673366504981998125)
        ·
          refine ⟨2025472752512439368249297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5401260673366504981998125 2025472752512439368249297)
          ·
            refine ⟨1519104564384329526186973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025472752512439368249297 1519104564384329526186973)
            ·
              refine ⟨569664211644123572320115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1519104564384329526186973 569664211644123572320115)
              ·
                refine ⟨854496317466185358480173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569664211644123572320115 854496317466185358480173)
                ·
                  refine ⟨320436119049819509430065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854496317466185358480173 320436119049819509430065)
                  ·
                    rfl

theorem cell20_702053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_702053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702053 prefixEnd_702053 := by exact prefixLift 702053
  have htrace : WordTrace (prefixWord ++ tailWord_702053) baseStart_702053 baseEnd_702053 := by
    simpa [prefixWord, tailWord_702053, baseEnd_702053] using wordTrace_append hprefix tailTrace_702053
  have hstable : (prefixWord ++ tailWord_702053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702053).length < 2 ^ (prefixWord ++ tailWord_702053).sum := by decide
  have hdescent : baseEnd_702053 < baseStart_702053 := by decide
  rcases family_descends (prefixWord ++ tailWord_702053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702057 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_702057 : Nat := 118140960795 + 702057 * 2 ^ 59
def prefixEnd_702057 : Nat := 4983230072969 + 3 ^ 40 * 702057 * 2
def baseEnd_702057 : Nat := 320437944758813273296715

theorem tailTrace_702057 : CollatzResearch.WordTrace tailWord_702057 prefixEnd_702057 320437944758813273296715 := by
  unfold tailWord_702057
  simp only [CollatzResearch.WordTrace]
  refine ⟨25606122417574865634840425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17070748278383243756560283 25606122417574865634840425)
  ·
    refine ⟨19204591813181149226130319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25606122417574865634840425 19204591813181149226130319)
    ·
      refine ⟨28806887719771723839195479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19204591813181149226130319 28806887719771723839195479)
      ·
        refine ⟨43210331579657585758793219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28806887719771723839195479 43210331579657585758793219)
        ·
          refine ⟨64815497369486378638189829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43210331579657585758793219 64815497369486378638189829)
          ·
            refine ⟨12152905756778695994660593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64815497369486378638189829 12152905756778695994660593)
            ·
              refine ⟨9114679317584021995995445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12152905756778695994660593 9114679317584021995995445)
              ·
                refine ⟨854501186023502062124573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9114679317584021995995445 854501186023502062124573)
                ·
                  refine ⟨320437944758813273296715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854501186023502062124573 320437944758813273296715)
                  ·
                    rfl

theorem cell20_702057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_702057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702057 prefixEnd_702057 := by exact prefixLift 702057
  have htrace : WordTrace (prefixWord ++ tailWord_702057) baseStart_702057 baseEnd_702057 := by
    simpa [prefixWord, tailWord_702057, baseEnd_702057] using wordTrace_append hprefix tailTrace_702057
  have hstable : (prefixWord ++ tailWord_702057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702057).length < 2 ^ (prefixWord ++ tailWord_702057).sum := by decide
  have hdescent : baseEnd_702057 < baseStart_702057 := by decide
  rcases family_descends (prefixWord ++ tailWord_702057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702077 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 2]
def baseStart_702077 : Nat := 118140960795 + 702077 * 2 ^ 59
def prefixEnd_702077 : Nat := 4983230072969 + 3 ^ 40 * 702077 * 2
def baseEnd_702077 : Nat := 320447073303782092629967

theorem tailTrace_702077 : CollatzResearch.WordTrace tailWord_702077 prefixEnd_702077 320447073303782092629967 := by
  unfold tailWord_702077
  simp only [CollatzResearch.WordTrace]
  refine ⟨25606851877502409050568485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17071234585001606033712323 25606851877502409050568485)
  ·
    refine ⟨4801284727031701696981591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25606851877502409050568485 4801284727031701696981591)
    ·
      refine ⟨7201927090547552545472387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801284727031701696981591 7201927090547552545472387)
      ·
        refine ⟨10802890635821328818208581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201927090547552545472387 10802890635821328818208581)
        ·
          refine ⟨2025541994216499153414109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10802890635821328818208581 2025541994216499153414109)
          ·
            refine ⟨759578247831187182530291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2025541994216499153414109 759578247831187182530291)
            ·
              refine ⟨1139367371746780773795437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759578247831187182530291 1139367371746780773795437)
              ·
                refine ⟨427262764405042790173289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139367371746780773795437 427262764405042790173289)
                ·
                  refine ⟨320447073303782092629967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427262764405042790173289 320447073303782092629967)
                  ·
                    rfl

theorem cell20_702077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_702077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702077 prefixEnd_702077 := by exact prefixLift 702077
  have htrace : WordTrace (prefixWord ++ tailWord_702077) baseStart_702077 baseEnd_702077 := by
    simpa [prefixWord, tailWord_702077, baseEnd_702077] using wordTrace_append hprefix tailTrace_702077
  have hstable : (prefixWord ++ tailWord_702077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702077).length < 2 ^ (prefixWord ++ tailWord_702077).sum := by decide
  have hdescent : baseEnd_702077 < baseStart_702077 := by decide
  rcases family_descends (prefixWord ++ tailWord_702077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702108 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_702108 : Nat := 118140960795 + 702108 * 2 ^ 59
def prefixEnd_702108 : Nat := 4983230072969 + 3 ^ 40 * 702108 * 2
def baseEnd_702108 : Nat := 320461222548483762596507

theorem tailTrace_702108 : CollatzResearch.WordTrace tailWord_702108 prefixEnd_702108 320461222548483762596507 := by
  unfold tailWord_702108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803991270195050672473489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17071988360260067563297985 12803991270195050672473489)
  ·
    refine ⟨9602993452646288004355117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12803991270195050672473489 9602993452646288004355117)
    ·
      refine ⟨3601122544742358001633169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9602993452646288004355117 3601122544742358001633169)
      ·
        refine ⟨2700841908556768501224877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601122544742358001633169 2700841908556768501224877)
        ·
          refine ⟨1012815715708788187959329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2700841908556768501224877 1012815715708788187959329)
          ·
            refine ⟨759611786781591140969497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012815715708788187959329 759611786781591140969497)
            ·
              refine ⟨569708840086193355727123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759611786781591140969497 569708840086193355727123)
              ·
                refine ⟨854563260129290033590685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569708840086193355727123 854563260129290033590685)
                ·
                  refine ⟨320461222548483762596507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854563260129290033590685 320461222548483762596507)
                  ·
                    rfl

theorem cell20_702108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_702108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702108 prefixEnd_702108 := by exact prefixLift 702108
  have htrace : WordTrace (prefixWord ++ tailWord_702108) baseStart_702108 baseEnd_702108 := by
    simpa [prefixWord, tailWord_702108, baseEnd_702108] using wordTrace_append hprefix tailTrace_702108
  have hstable : (prefixWord ++ tailWord_702108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702108).length < 2 ^ (prefixWord ++ tailWord_702108).sum := by decide
  have hdescent : baseEnd_702108 < baseStart_702108 := by decide
  rcases family_descends (prefixWord ++ tailWord_702108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702112 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_702112 : Nat := 118140960795 + 702112 * 2 ^ 59
def prefixEnd_702112 : Nat := 4983230072969 + 3 ^ 40 * 702112 * 2
def baseEnd_702112 : Nat := 320463048257477526463157

theorem tailTrace_702112 : CollatzResearch.WordTrace tailWord_702112 prefixEnd_702112 320463048257477526463157 := by
  unfold tailWord_702112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12804064216187805014046295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17072085621583740018728393 12804064216187805014046295)
  ·
    refine ⟨19206096324281707521069443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12804064216187805014046295 19206096324281707521069443)
    ·
      refine ⟨28809144486422561281604165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19206096324281707521069443 28809144486422561281604165)
      ·
        refine ⟨5401714591204230240300781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28809144486422561281604165 5401714591204230240300781)
        ·
          refine ⟨2025642971701586340112793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5401714591204230240300781 2025642971701586340112793)
          ·
            refine ⟨1519232228776189755084595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025642971701586340112793 1519232228776189755084595)
            ·
              refine ⟨2278848343164284632626893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519232228776189755084595 2278848343164284632626893)
              ·
                refine ⟨854568128686606737235085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278848343164284632626893 854568128686606737235085)
                ·
                  refine ⟨320463048257477526463157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854568128686606737235085 320463048257477526463157)
                  ·
                    rfl

theorem cell20_702112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_702112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702112 prefixEnd_702112 := by exact prefixLift 702112
  have htrace : WordTrace (prefixWord ++ tailWord_702112) baseStart_702112 baseEnd_702112 := by
    simpa [prefixWord, tailWord_702112, baseEnd_702112] using wordTrace_append hprefix tailTrace_702112
  have hstable : (prefixWord ++ tailWord_702112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702112).length < 2 ^ (prefixWord ++ tailWord_702112).sum := by decide
  have hdescent : baseEnd_702112 < baseStart_702112 := by decide
  rcases family_descends (prefixWord ++ tailWord_702112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702195 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 2]
def baseStart_702195 : Nat := 118140960795 + 702195 * 2 ^ 59
def prefixEnd_702195 : Nat := 4983230072969 + 3 ^ 40 * 702195 * 2
def baseEnd_702195 : Nat := 320500931719098126696151

theorem tailTrace_702195 : CollatzResearch.WordTrace tailWord_702195 prefixEnd_702195 320500931719098126696151 := by
  unfold tailWord_702195
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611155691074915203364039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17074103794049943468909359 25611155691074915203364039)
  ·
    refine ⟨38416733536612372805046059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25611155691074915203364039 38416733536612372805046059)
    ·
      refine ⟨57625100304918559207569089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38416733536612372805046059 57625100304918559207569089)
      ·
        refine ⟨43218825228688919405676817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57625100304918559207569089 43218825228688919405676817)
        ·
          refine ⟨32414118921516689554257613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43218825228688919405676817 32414118921516689554257613)
          ·
            refine ⟨12155294595568758582846605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32414118921516689554257613 12155294595568758582846605)
            ·
              refine ⟨4558235473338284468567477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12155294595568758582846605 4558235473338284468567477)
              ·
                refine ⟨427334575625464168928201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4558235473338284468567477 427334575625464168928201)
                ·
                  refine ⟨320500931719098126696151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427334575625464168928201 320500931719098126696151)
                  ·
                    rfl

theorem cell20_702195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 2].length) (baseStart_702195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702195 prefixEnd_702195 := by exact prefixLift 702195
  have htrace : WordTrace (prefixWord ++ tailWord_702195) baseStart_702195 baseEnd_702195 := by
    simpa [prefixWord, tailWord_702195, baseEnd_702195] using wordTrace_append hprefix tailTrace_702195
  have hstable : (prefixWord ++ tailWord_702195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702195).length < 2 ^ (prefixWord ++ tailWord_702195).sum := by decide
  have hdescent : baseEnd_702195 < baseStart_702195 := by decide
  rcases family_descends (prefixWord ++ tailWord_702195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702212 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_702212 : Nat := 118140960795 + 702212 * 2 ^ 59
def prefixEnd_702212 : Nat := 4983230072969 + 3 ^ 40 * 702212 * 2
def baseEnd_702212 : Nat := 320508690982321623129415

theorem tailTrace_702212 : CollatzResearch.WordTrace tailWord_702212 prefixEnd_702212 320508690982321623129415 := by
  unfold tailWord_702212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805887866006663553366445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17074517154675551404488593 12805887866006663553366445)
  ·
    refine ⟨4802207949752498832512417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12805887866006663553366445 4802207949752498832512417)
    ·
      refine ⟨3601655962314374124384313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4802207949752498832512417 3601655962314374124384313)
      ·
        refine ⟨2701241971735780593288235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601655962314374124384313 2701241971735780593288235)
        ·
          refine ⟨4051862957603670889932353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701241971735780593288235 4051862957603670889932353)
          ·
            refine ⟨3038897218202753167449265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4051862957603670889932353 3038897218202753167449265)
            ·
              refine ⟨2279172913652064875586949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038897218202753167449265 2279172913652064875586949)
              ·
                refine ⟨427344921309762164172553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2279172913652064875586949 427344921309762164172553)
                ·
                  refine ⟨320508690982321623129415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427344921309762164172553 320508690982321623129415)
                  ·
                    rfl

theorem cell20_702212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_702212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702212 prefixEnd_702212 := by exact prefixLift 702212
  have htrace : WordTrace (prefixWord ++ tailWord_702212) baseStart_702212 baseEnd_702212 := by
    simpa [prefixWord, tailWord_702212, baseEnd_702212] using wordTrace_append hprefix tailTrace_702212
  have hstable : (prefixWord ++ tailWord_702212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702212).length < 2 ^ (prefixWord ++ tailWord_702212).sum := by decide
  have hdescent : baseEnd_702212 < baseStart_702212 := by decide
  rcases family_descends (prefixWord ++ tailWord_702212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702309 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 2]
def baseStart_702309 : Nat := 118140960795 + 702309 * 2 ^ 59
def prefixEnd_702309 : Nat := 4983230072969 + 3 ^ 40 * 702309 * 2
def baseEnd_702309 : Nat := 320552964425420396895685

theorem tailTrace_702309 : CollatzResearch.WordTrace tailWord_702309 prefixEnd_702309 320552964425420396895685 := by
  unfold tailWord_702309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615313612661912673013981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17076875741774608448675987 25615313612661912673013981)
  ·
    refine ⟨9605742604748217252380243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25615313612661912673013981 9605742604748217252380243)
    ·
      refine ⟨14408613907122325878570365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9605742604748217252380243 14408613907122325878570365)
      ·
        refine ⟨5403230215170872204463887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14408613907122325878570365 5403230215170872204463887)
        ·
          refine ⟨8104845322756308306695831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403230215170872204463887 8104845322756308306695831)
          ·
            refine ⟨12157267984134462460043747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104845322756308306695831 12157267984134462460043747)
            ·
              refine ⟨18235901976201693690065621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12157267984134462460043747 18235901976201693690065621)
              ·
                refine ⟨427403952567227195860913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18235901976201693690065621 427403952567227195860913)
                ·
                  refine ⟨320552964425420396895685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427403952567227195860913 320552964425420396895685)
                  ·
                    rfl

theorem cell20_702309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_702309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702309 prefixEnd_702309 := by exact prefixLift 702309
  have htrace : WordTrace (prefixWord ++ tailWord_702309) baseStart_702309 baseEnd_702309 := by
    simpa [prefixWord, tailWord_702309, baseEnd_702309] using wordTrace_append hprefix tailTrace_702309
  have hstable : (prefixWord ++ tailWord_702309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702309).length < 2 ^ (prefixWord ++ tailWord_702309).sum := by decide
  have hdescent : baseEnd_702309 < baseStart_702309 := by decide
  rcases family_descends (prefixWord ++ tailWord_702309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702350 : List Nat := [4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_702350 : Nat := 118140960795 + 702350 * 2 ^ 59
def prefixEnd_702350 : Nat := 4983230072969 + 3 ^ 40 * 702350 * 2
def baseEnd_702350 : Nat := 106857225980868825509617

theorem tailTrace_702350 : CollatzResearch.WordTrace tailWord_702350 prefixEnd_702350 106857225980868825509617 := by
  unfold tailWord_702350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202101125689172084407063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17077872670342251116837669 3202101125689172084407063)
  ·
    refine ⟨4803151688533758126610595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3202101125689172084407063 4803151688533758126610595)
    ·
      refine ⟨7204727532800637189915893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4803151688533758126610595 7204727532800637189915893)
      ·
        refine ⟨675443206200059736554615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7204727532800637189915893 675443206200059736554615)
        ·
          refine ⟨1013164809300089604831923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675443206200059736554615 1013164809300089604831923)
          ·
            refine ⟨1519747213950134407247885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013164809300089604831923 1519747213950134407247885)
            ·
              refine ⟨569905205231300402717957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1519747213950134407247885 569905205231300402717957)
              ·
                refine ⟨106857225980868825509617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569905205231300402717957 106857225980868825509617)
                ·
                  rfl

theorem cell20_702350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_702350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702350 prefixEnd_702350 := by exact prefixLift 702350
  have htrace : WordTrace (prefixWord ++ tailWord_702350) baseStart_702350 baseEnd_702350 := by
    simpa [prefixWord, tailWord_702350, baseEnd_702350] using wordTrace_append hprefix tailTrace_702350
  have hstable : (prefixWord ++ tailWord_702350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702350).length < 2 ^ (prefixWord ++ tailWord_702350).sum := by decide
  have hdescent : baseEnd_702350 < baseStart_702350 := by decide
  rcases family_descends (prefixWord ++ tailWord_702350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702364 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_702364 : Nat := 118140960795 + 702364 * 2 ^ 59
def prefixEnd_702364 : Nat := 4983230072969 + 3 ^ 40 * 702364 * 2
def baseEnd_702364 : Nat := 320578067924084650062127

theorem tailTrace_702364 : CollatzResearch.WordTrace tailWord_702364 prefixEnd_702364 320578067924084650062127 := by
  unfold tailWord_702364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12808659813731328533133073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17078213084975104710844097 12808659813731328533133073)
  ·
    refine ⟨9606494860298496399849805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12808659813731328533133073 9606494860298496399849805)
    ·
      refine ⟨3602435572611936149943677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9606494860298496399849805 3602435572611936149943677)
      ·
        refine ⟨1350913339729476056228879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3602435572611936149943677 1350913339729476056228879)
        ·
          refine ⟨2026370009594214084343319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350913339729476056228879 2026370009594214084343319)
          ·
            refine ⟨3039555014391321126514979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026370009594214084343319 3039555014391321126514979)
            ·
              refine ⟨4559332521586981689772469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039555014391321126514979 4559332521586981689772469)
              ·
                refine ⟨427437423898779533416169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4559332521586981689772469 427437423898779533416169)
                ·
                  refine ⟨320578067924084650062127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427437423898779533416169 320578067924084650062127)
                  ·
                    rfl

theorem cell20_702364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_702364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702364 prefixEnd_702364 := by exact prefixLift 702364
  have htrace : WordTrace (prefixWord ++ tailWord_702364) baseStart_702364 baseEnd_702364 := by
    simpa [prefixWord, tailWord_702364, baseEnd_702364] using wordTrace_append hprefix tailTrace_702364
  have hstable : (prefixWord ++ tailWord_702364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702364).length < 2 ^ (prefixWord ++ tailWord_702364).sum := by decide
  have hdescent : baseEnd_702364 < baseStart_702364 := by decide
  rcases family_descends (prefixWord ++ tailWord_702364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702385 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_702385 : Nat := 118140960795 + 702385 * 2 ^ 59
def prefixEnd_702385 : Nat := 4983230072969 + 3 ^ 40 * 702385 * 2
def baseEnd_702385 : Nat := 320587652896301910362041

theorem tailTrace_702385 : CollatzResearch.WordTrace tailWord_702385 prefixEnd_702385 320587652896301910362041 := by
  unfold tailWord_702385
  simp only [CollatzResearch.WordTrace]
  refine ⟨25618085560386577652780609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17078723706924385101853739 25618085560386577652780609)
  ·
    refine ⟨19213564170289933239585457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25618085560386577652780609 19213564170289933239585457)
    ·
      refine ⟨14410173127717449929689093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19213564170289933239585457 14410173127717449929689093)
      ·
        refine ⟨2701907461447021861816705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14410173127717449929689093 2701907461447021861816705)
        ·
          refine ⟨2026430596085266396362529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701907461447021861816705 2026430596085266396362529)
          ·
            refine ⟨1519822947063949797271897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026430596085266396362529 1519822947063949797271897)
            ·
              refine ⟨1139867210297962347953923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519822947063949797271897 1139867210297962347953923)
              ·
                refine ⟨1709800815446943521930885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139867210297962347953923 1709800815446943521930885)
                ·
                  refine ⟨320587652896301910362041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1709800815446943521930885 320587652896301910362041)
                  ·
                    rfl

theorem cell20_702385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_702385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702385 prefixEnd_702385 := by exact prefixLift 702385
  have htrace : WordTrace (prefixWord ++ tailWord_702385) baseStart_702385 baseEnd_702385 := by
    simpa [prefixWord, tailWord_702385, baseEnd_702385] using wordTrace_append hprefix tailTrace_702385
  have hstable : (prefixWord ++ tailWord_702385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702385).length < 2 ^ (prefixWord ++ tailWord_702385).sum := by decide
  have hdescent : baseEnd_702385 < baseStart_702385 := by decide
  rcases family_descends (prefixWord ++ tailWord_702385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702492 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_702492 : Nat := 118140960795 + 702492 * 2 ^ 59
def prefixEnd_702492 : Nat := 4983230072969 + 3 ^ 40 * 702492 * 2
def baseEnd_702492 : Nat := 320636490611885093794937

theorem tailTrace_702492 : CollatzResearch.WordTrace tailWord_702492 prefixEnd_702492 320636490611885093794937 := by
  unfold tailWord_702492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810994085499467463462865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17081325447332623284617153 12810994085499467463462865)
  ·
    refine ⟨9608245564124600597597149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12810994085499467463462865 9608245564124600597597149)
    ·
      refine ⟨3603092086546725224098931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9608245564124600597597149 3603092086546725224098931)
      ·
        refine ⟨5404638129820087836148397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603092086546725224098931 5404638129820087836148397)
        ·
          refine ⟨2026739298682532938555649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5404638129820087836148397 2026739298682532938555649)
          ·
            refine ⟨1520054474011899703916737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026739298682532938555649 1520054474011899703916737)
            ·
              refine ⟨1140040855508924777937553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520054474011899703916737 1140040855508924777937553)
              ·
                refine ⟨855030641631693583453165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140040855508924777937553 855030641631693583453165)
                ·
                  refine ⟨320636490611885093794937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855030641631693583453165 320636490611885093794937)
                  ·
                    rfl

theorem cell20_702492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_702492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702492 prefixEnd_702492 := by exact prefixLift 702492
  have htrace : WordTrace (prefixWord ++ tailWord_702492) baseStart_702492 baseEnd_702492 := by
    simpa [prefixWord, tailWord_702492, baseEnd_702492] using wordTrace_append hprefix tailTrace_702492
  have hstable : (prefixWord ++ tailWord_702492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702492).length < 2 ^ (prefixWord ++ tailWord_702492).sum := by decide
  have hdescent : baseEnd_702492 < baseStart_702492 := by decide
  rcases family_descends (prefixWord ++ tailWord_702492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702499 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 2]
def baseStart_702499 : Nat := 118140960795 + 702499 * 2 ^ 59
def prefixEnd_702499 : Nat := 4983230072969 + 3 ^ 40 * 702499 * 2
def baseEnd_702499 : Nat := 320639685602624180561575

theorem tailTrace_702499 : CollatzResearch.WordTrace tailWord_702499 prefixEnd_702499 320639685602624180561575 := by
  unfold tailWord_702499
  simp only [CollatzResearch.WordTrace]
  refine ⟨25622243481973575122430551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17081495654649050081620367 25622243481973575122430551)
  ·
    refine ⟨38433365222960362683645827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25622243481973575122430551 38433365222960362683645827)
    ·
      refine ⟨57650047834440544025468741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38433365222960362683645827 57650047834440544025468741)
      ·
        refine ⟨10809383968957602004775389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57650047834440544025468741 10809383968957602004775389)
        ·
          refine ⟨4053518988359100751790771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10809383968957602004775389 4053518988359100751790771)
          ·
            refine ⟨6080278482538651127686157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053518988359100751790771 6080278482538651127686157)
            ·
              refine ⟨2280104430951994172882309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6080278482538651127686157 2280104430951994172882309)
              ·
                refine ⟨427519580803498907415433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2280104430951994172882309 427519580803498907415433)
                ·
                  refine ⟨320639685602624180561575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427519580803498907415433 320639685602624180561575)
                  ·
                    rfl

theorem cell20_702499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2].length) (baseStart_702499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702499 prefixEnd_702499 := by exact prefixLift 702499
  have htrace : WordTrace (prefixWord ++ tailWord_702499) baseStart_702499 baseEnd_702499 := by
    simpa [prefixWord, tailWord_702499, baseEnd_702499] using wordTrace_append hprefix tailTrace_702499
  have hstable : (prefixWord ++ tailWord_702499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702499).length < 2 ^ (prefixWord ++ tailWord_702499).sum := by decide
  have hdescent : baseEnd_702499 < baseStart_702499 := by decide
  rcases family_descends (prefixWord ++ tailWord_702499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702506 : List Nat := [3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_702506 : Nat := 118140960795 + 702506 * 2 ^ 59
def prefixEnd_702506 : Nat := 4983230072969 + 3 ^ 40 * 702506 * 2
def baseEnd_702506 : Nat := 106880960197787755776071

theorem tailTrace_702506 : CollatzResearch.WordTrace tailWord_702506 prefixEnd_702506 106880960197787755776071 := by
  unfold tailWord_702506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405624698237053829483843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17081665861965476878623581 6405624698237053829483843)
  ·
    refine ⟨9608437047355580744225765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6405624698237053829483843 9608437047355580744225765)
    ·
      refine ⟨1801581946379171389542331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9608437047355580744225765 1801581946379171389542331)
      ·
        refine ⟨2702372919568757084313497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801581946379171389542331 2702372919568757084313497)
        ·
          refine ⟨2026779689676567813235123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702372919568757084313497 2026779689676567813235123)
          ·
            refine ⟨3040169534514851719852685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026779689676567813235123 3040169534514851719852685)
            ·
              refine ⟨1140063575443069394944757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3040169534514851719852685 1140063575443069394944757)
              ·
                refine ⟨106880960197787755776071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1140063575443069394944757 106880960197787755776071)
                ·
                  rfl

theorem cell20_702506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_702506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702506 prefixEnd_702506 := by exact prefixLift 702506
  have htrace : WordTrace (prefixWord ++ tailWord_702506) baseStart_702506 baseEnd_702506 := by
    simpa [prefixWord, tailWord_702506, baseEnd_702506] using wordTrace_append hprefix tailTrace_702506
  have hstable : (prefixWord ++ tailWord_702506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702506).length < 2 ^ (prefixWord ++ tailWord_702506).sum := by decide
  have hdescent : baseEnd_702506 < baseStart_702506 := by decide
  rcases family_descends (prefixWord ++ tailWord_702506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702513 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_702513 : Nat := 118140960795 + 702513 * 2 ^ 59
def prefixEnd_702513 : Nat := 4983230072969 + 3 ^ 40 * 702513 * 2
def baseEnd_702513 : Nat := 320646075584102354094851

theorem tailTrace_702513 : CollatzResearch.WordTrace tailWord_702513 prefixEnd_702513 320646075584102354094851 := by
  unfold tailWord_702513
  simp only [CollatzResearch.WordTrace]
  refine ⟨25622754103922855513440193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17081836069281903675626795 25622754103922855513440193)
  ·
    refine ⟨19217065577942141635080145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25622754103922855513440193 19217065577942141635080145)
    ·
      refine ⟨14412799183456606226310109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19217065577942141635080145 14412799183456606226310109)
      ·
        refine ⟨5404799693796227334866291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14412799183456606226310109 5404799693796227334866291)
        ·
          refine ⟨8107199540694341002299437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404799693796227334866291 8107199540694341002299437)
          ·
            refine ⟨3040199827760377875862289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8107199540694341002299437 3040199827760377875862289)
            ·
              refine ⟨2280149870820283406896717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040199827760377875862289 2280149870820283406896717)
              ·
                refine ⟨855056201557606277586269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2280149870820283406896717 855056201557606277586269)
                ·
                  refine ⟨320646075584102354094851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855056201557606277586269 320646075584102354094851)
                  ·
                    rfl

theorem cell20_702513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_702513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702513 prefixEnd_702513 := by exact prefixLift 702513
  have htrace : WordTrace (prefixWord ++ tailWord_702513) baseStart_702513 baseEnd_702513 := by
    simpa [prefixWord, tailWord_702513, baseEnd_702513] using wordTrace_append hprefix tailTrace_702513
  have hstable : (prefixWord ++ tailWord_702513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702513).length < 2 ^ (prefixWord ++ tailWord_702513).sum := by decide
  have hdescent : baseEnd_702513 < baseStart_702513 := by decide
  rcases family_descends (prefixWord ++ tailWord_702513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702516 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_702516 : Nat := 118140960795 + 702516 * 2 ^ 59
def prefixEnd_702516 : Nat := 4983230072969 + 3 ^ 40 * 702516 * 2
def baseEnd_702516 : Nat := 320647444865847676994839

theorem tailTrace_702516 : CollatzResearch.WordTrace tailWord_702516 prefixEnd_702516 320647444865847676994839 := by
  unfold tailWord_702516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12811431761455993512899701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17081909015274658017199601 12811431761455993512899701)
  ·
    refine ⟨1201071727636499391834347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12811431761455993512899701 1201071727636499391834347)
    ·
      refine ⟨1801607591454749087751521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201071727636499391834347 1801607591454749087751521)
      ·
        refine ⟨1351205693591061815813641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1801607591454749087751521 1351205693591061815813641)
        ·
          refine ⟨1013404270193296361860231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1351205693591061815813641 1013404270193296361860231)
          ·
            refine ⟨1520106405289944542790347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013404270193296361860231 1520106405289944542790347)
            ·
              refine ⟨2280159607934916814185521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520106405289944542790347 2280159607934916814185521)
              ·
                refine ⟨1710119705951187610639141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280159607934916814185521 1710119705951187610639141)
                ·
                  refine ⟨320647444865847676994839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710119705951187610639141 320647444865847676994839)
                  ·
                    rfl

theorem cell20_702516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_702516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702516 prefixEnd_702516 := by exact prefixLift 702516
  have htrace : WordTrace (prefixWord ++ tailWord_702516) baseStart_702516 baseEnd_702516 := by
    simpa [prefixWord, tailWord_702516, baseEnd_702516] using wordTrace_append hprefix tailTrace_702516
  have hstable : (prefixWord ++ tailWord_702516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702516).length < 2 ^ (prefixWord ++ tailWord_702516).sum := by decide
  have hdescent : baseEnd_702516 < baseStart_702516 := by decide
  rcases family_descends (prefixWord ++ tailWord_702516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702537 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 2]
def baseStart_702537 : Nat := 118140960795 + 702537 * 2 ^ 59
def prefixEnd_702537 : Nat := 4983230072969 + 3 ^ 40 * 702537 * 2
def baseEnd_702537 : Nat := 320657029838064937294753

theorem tailTrace_702537 : CollatzResearch.WordTrace tailWord_702537 prefixEnd_702537 320657029838064937294753 := by
  unfold tailWord_702537
  simp only [CollatzResearch.WordTrace]
  refine ⟨25623629455835907612313865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17082419637223938408209243 25623629455835907612313865)
  ·
    refine ⟨19217722091876930709235399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25623629455835907612313865 19217722091876930709235399)
    ·
      refine ⟨28826583137815396063853099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19217722091876930709235399 28826583137815396063853099)
      ·
        refine ⟨43239874706723094095779649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28826583137815396063853099 43239874706723094095779649)
        ·
          refine ⟨32429906030042320571834737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43239874706723094095779649 32429906030042320571834737)
          ·
            refine ⟨24322429522531740428876053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32429906030042320571834737 24322429522531740428876053)
            ·
              refine ⟨1140113883868675332603565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24322429522531740428876053 1140113883868675332603565)
              ·
                refine ⟨427542706450753249726337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140113883868675332603565 427542706450753249726337)
                ·
                  refine ⟨320657029838064937294753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427542706450753249726337 320657029838064937294753)
                  ·
                    rfl

theorem cell20_702537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_702537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702537 prefixEnd_702537 := by exact prefixLift 702537
  have htrace : WordTrace (prefixWord ++ tailWord_702537) baseStart_702537 baseEnd_702537 := by
    simpa [prefixWord, tailWord_702537, baseEnd_702537] using wordTrace_append hprefix tailTrace_702537
  have hstable : (prefixWord ++ tailWord_702537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702537).length < 2 ^ (prefixWord ++ tailWord_702537).sum := by decide
  have hdescent : baseEnd_702537 < baseStart_702537 := by decide
  rcases family_descends (prefixWord ++ tailWord_702537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702551 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_702551 : Nat := 118140960795 + 702551 * 2 ^ 59
def prefixEnd_702551 : Nat := 4983230072969 + 3 ^ 40 * 702551 * 2
def baseEnd_702551 : Nat := 320663419819543110828029

theorem tailTrace_702551 : CollatzResearch.WordTrace tailWord_702551 prefixEnd_702551 320663419819543110828029 := by
  unfold tailWord_702551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25624140077785188003323507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17082760051856792002215671 25624140077785188003323507)
  ·
    refine ⟨38436210116677782004985261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25624140077785188003323507 38436210116677782004985261)
    ·
      refine ⟨14413578793754168251869473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38436210116677782004985261 14413578793754168251869473)
      ·
        refine ⟨10810184095315626188902105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14413578793754168251869473 10810184095315626188902105)
        ·
          refine ⟨8107638071486719641676579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10810184095315626188902105 8107638071486719641676579)
          ·
            refine ⟨12161457107230079462514869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107638071486719641676579 12161457107230079462514869)
            ·
              refine ⟨1140136603802819949610769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12161457107230079462514869 1140136603802819949610769)
              ·
                refine ⟨855102452852114962208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140136603802819949610769 855102452852114962208077)
                ·
                  refine ⟨320663419819543110828029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855102452852114962208077 320663419819543110828029)
                  ·
                    rfl

theorem cell20_702551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_702551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702551 prefixEnd_702551 := by exact prefixLift 702551
  have htrace : WordTrace (prefixWord ++ tailWord_702551) baseStart_702551 baseEnd_702551 := by
    simpa [prefixWord, tailWord_702551, baseEnd_702551] using wordTrace_append hprefix tailTrace_702551
  have hstable : (prefixWord ++ tailWord_702551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702551).length < 2 ^ (prefixWord ++ tailWord_702551).sum := by decide
  have hdescent : baseEnd_702551 < baseStart_702551 := by decide
  rcases family_descends (prefixWord ++ tailWord_702551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702582 : List Nat := [5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_702582 : Nat := 118140960795 + 702582 * 2 ^ 59
def prefixEnd_702582 : Nat := 4983230072969 + 3 ^ 40 * 702582 * 2
def baseEnd_702582 : Nat := 106892523021414926931523

theorem tailTrace_702582 : CollatzResearch.WordTrace tailWord_702582 prefixEnd_702582 106892523021414926931523 := by
  unfold tailWord_702582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601579421292055018606375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17083513827115253531801333 1601579421292055018606375)
  ·
    refine ⟨2402369131938082527909563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1601579421292055018606375 2402369131938082527909563)
    ·
      refine ⟨3603553697907123791864345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402369131938082527909563 3603553697907123791864345)
      ·
        refine ⟨2702665273430342843898259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3603553697907123791864345 2702665273430342843898259)
        ·
          refine ⟨4053997910145514265847389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702665273430342843898259 4053997910145514265847389)
          ·
            refine ⟨1520249216304567849692771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4053997910145514265847389 1520249216304567849692771)
            ·
              refine ⟨2280373824456851774539157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520249216304567849692771 2280373824456851774539157)
              ·
                refine ⟨106892523021414926931523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2280373824456851774539157 106892523021414926931523)
                ·
                  rfl

theorem cell20_702582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_702582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702582 prefixEnd_702582 := by exact prefixLift 702582
  have htrace : WordTrace (prefixWord ++ tailWord_702582) baseStart_702582 baseEnd_702582 := by
    simpa [prefixWord, tailWord_702582, baseEnd_702582] using wordTrace_append hprefix tailTrace_702582
  have hstable : (prefixWord ++ tailWord_702582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702582).length < 2 ^ (prefixWord ++ tailWord_702582).sum := by decide
  have hdescent : baseEnd_702582 < baseStart_702582 := by decide
  rcases family_descends (prefixWord ++ tailWord_702582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702623 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 3]
def baseStart_702623 : Nat := 118140960795 + 702623 * 2 ^ 59
def prefixEnd_702623 : Nat := 4983230072969 + 3 ^ 40 * 702623 * 2
def baseEnd_702623 : Nat := 320696282581430860427735

theorem tailTrace_702623 : CollatzResearch.WordTrace tailWord_702623 prefixEnd_702623 320696282581430860427735 := by
  unfold tailWord_702623
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626766133524344299944523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17084510755682896199963015 25626766133524344299944523)
  ·
    refine ⟨38440149200286516449916785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25626766133524344299944523 38440149200286516449916785)
    ·
      refine ⟨28830111900214887337437589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38440149200286516449916785 28830111900214887337437589)
      ·
        refine ⟨1351411495322572843942387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28830111900214887337437589 1351411495322572843942387)
        ·
          refine ⟨2027117242983859265913581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351411495322572843942387 2027117242983859265913581)
          ·
            refine ⟨760168966118947224717593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2027117242983859265913581 760168966118947224717593)
            ·
              refine ⟨570126724589210418538195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760168966118947224717593 570126724589210418538195)
              ·
                refine ⟨855190086883815627807293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570126724589210418538195 855190086883815627807293)
                ·
                  refine ⟨320696282581430860427735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855190086883815627807293 320696282581430860427735)
                  ·
                    rfl

theorem cell20_702623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_702623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702623 prefixEnd_702623 := by exact prefixLift 702623
  have htrace : WordTrace (prefixWord ++ tailWord_702623) baseStart_702623 baseEnd_702623 := by
    simpa [prefixWord, tailWord_702623, baseEnd_702623] using wordTrace_append hprefix tailTrace_702623
  have hstable : (prefixWord ++ tailWord_702623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702623).length < 2 ^ (prefixWord ++ tailWord_702623).sum := by decide
  have hdescent : baseEnd_702623 < baseStart_702623 := by decide
  rcases family_descends (prefixWord ++ tailWord_702623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702696 : List Nat := [2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_702696 : Nat := 118140960795 + 702696 * 2 ^ 59
def prefixEnd_702696 : Nat := 4983230072969 + 3 ^ 40 * 702696 * 2
def baseEnd_702696 : Nat := 106909867256855683664701

theorem tailTrace_702696 : CollatzResearch.WordTrace tailWord_702696 prefixEnd_702696 106909867256855683664701 := by
  unfold tailWord_702696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814714331129938883675971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17086285774839918511567961 12814714331129938883675971)
  ·
    refine ⟨19222071496694908325513957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12814714331129938883675971 19222071496694908325513957)
    ·
      refine ⟨3604138405630295311033867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19222071496694908325513957 3604138405630295311033867)
      ·
        refine ⟨5406207608445442966550801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604138405630295311033867 5406207608445442966550801)
        ·
          refine ⟨4054655706334082224913101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5406207608445442966550801 4054655706334082224913101)
          ·
            refine ⟨1520495889875280834342413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4054655706334082224913101 1520495889875280834342413)
            ·
              refine ⟨570185958703230312878405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1520495889875280834342413 570185958703230312878405)
              ·
                refine ⟨106909867256855683664701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570185958703230312878405 106909867256855683664701)
                ·
                  rfl

theorem cell20_702696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_702696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702696 prefixEnd_702696 := by exact prefixLift 702696
  have htrace : WordTrace (prefixWord ++ tailWord_702696) baseStart_702696 baseEnd_702696 := by
    simpa [prefixWord, tailWord_702696, baseEnd_702696] using wordTrace_append hprefix tailTrace_702696
  have hstable : (prefixWord ++ tailWord_702696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702696).length < 2 ^ (prefixWord ++ tailWord_702696).sum := by decide
  have hdescent : baseEnd_702696 < baseStart_702696 := by decide
  rcases family_descends (prefixWord ++ tailWord_702696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702706 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_702706 : Nat := 118140960795 + 702706 * 2 ^ 59
def prefixEnd_702706 : Nat := 4983230072969 + 3 ^ 40 * 702706 * 2
def baseEnd_702706 : Nat := 320734166043051460660729

theorem tailTrace_702706 : CollatzResearch.WordTrace tailWord_702706 prefixEnd_702706 320734166043051460660729 := by
  unfold tailWord_702706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407448348055912368803993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17086528928149099650143981 6407448348055912368803993)
  ·
    refine ⟨4805586261041934276602995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6407448348055912368803993 4805586261041934276602995)
    ·
      refine ⟨7208379391562901414904493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4805586261041934276602995 7208379391562901414904493)
      ·
        refine ⟨2703142271836088030589185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7208379391562901414904493 2703142271836088030589185)
        ·
          refine ⟨2027356703877066022941889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2703142271836088030589185 2027356703877066022941889)
          ·
            refine ⟨1520517527907799517206417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027356703877066022941889 1520517527907799517206417)
            ·
              refine ⟨1140388145930849637904813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520517527907799517206417 1140388145930849637904813)
              ·
                refine ⟨427645554724068614214305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140388145930849637904813 427645554724068614214305)
                ·
                  refine ⟨320734166043051460660729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427645554724068614214305 320734166043051460660729)
                  ·
                    rfl

theorem cell20_702706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_702706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702706 prefixEnd_702706 := by exact prefixLift 702706
  have htrace : WordTrace (prefixWord ++ tailWord_702706) baseStart_702706 baseEnd_702706 := by
    simpa [prefixWord, tailWord_702706, baseEnd_702706] using wordTrace_append hprefix tailTrace_702706
  have hstable : (prefixWord ++ tailWord_702706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702706).length < 2 ^ (prefixWord ++ tailWord_702706).sum := by decide
  have hdescent : baseEnd_702706 < baseStart_702706 := by decide
  rcases family_descends (prefixWord ++ tailWord_702706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702772 : List Nat := [2, 5, 1, 1, 1, 4, 6]
def baseStart_702772 : Nat := 118140960795 + 702772 * 2 ^ 59
def prefixEnd_702772 : Nat := 4983230072969 + 3 ^ 40 * 702772 * 2
def baseEnd_702772 : Nat := 35640476693494284940051

theorem tailTrace_702772 : CollatzResearch.WordTrace tailWord_702772 prefixEnd_702772 35640476693494284940051 := by
  unfold tailWord_702772
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816100304992271373559285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17088133739989695164745713 12816100304992271373559285)
  ·
    refine ⟨1201509403593025441271183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12816100304992271373559285 1201509403593025441271183)
    ·
      refine ⟨1802264105389538161906775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201509403593025441271183 1802264105389538161906775)
      ·
        refine ⟨2703396158084307242860163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802264105389538161906775 2703396158084307242860163)
        ·
          refine ⟨4055094237126460864290245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703396158084307242860163 4055094237126460864290245)
          ·
            refine ⟨760330169461211412054421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4055094237126460864290245 760330169461211412054421)
            ·
              refine ⟨35640476693494284940051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 760330169461211412054421 35640476693494284940051)
              ·
                rfl

theorem cell20_702772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_702772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702772 prefixEnd_702772 := by exact prefixLift 702772
  have htrace : WordTrace (prefixWord ++ tailWord_702772) baseStart_702772 baseEnd_702772 := by
    simpa [prefixWord, tailWord_702772, baseEnd_702772] using wordTrace_append hprefix tailTrace_702772
  have hstable : (prefixWord ++ tailWord_702772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702772).length < 2 ^ (prefixWord ++ tailWord_702772).sum := by decide
  have hdescent : baseEnd_702772 < baseStart_702772 := by decide
  rcases family_descends (prefixWord ++ tailWord_702772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702776 : List Nat := [2, 1, 2, 1, 3, 1, 10]
def baseStart_702776 : Nat := 118140960795 + 702776 * 2 ^ 59
def prefixEnd_702776 : Nat := 4983230072969 + 3 ^ 40 * 702776 * 2
def baseEnd_702776 : Nat := 35640679550049147591901

theorem tailTrace_702776 : CollatzResearch.WordTrace tailWord_702776 prefixEnd_702776 35640679550049147591901 := by
  unfold tailWord_702776
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816173250985025715132091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17088231001313367620176121 12816173250985025715132091)
  ·
    refine ⟨19224259876477538572698137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12816173250985025715132091 19224259876477538572698137)
    ·
      refine ⟨14418194907358153929523603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19224259876477538572698137 14418194907358153929523603)
      ·
        refine ⟨21627292361037230894285405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14418194907358153929523603 21627292361037230894285405)
        ·
          refine ⟨8110234635388961585357027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21627292361037230894285405 8110234635388961585357027)
          ·
            refine ⟨12165351953083442378035541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110234635388961585357027 12165351953083442378035541)
            ·
              refine ⟨35640679550049147591901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12165351953083442378035541 35640679550049147591901)
              ·
                rfl

theorem cell20_702776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_702776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702776 prefixEnd_702776 := by exact prefixLift 702776
  have htrace : WordTrace (prefixWord ++ tailWord_702776) baseStart_702776 baseEnd_702776 := by
    simpa [prefixWord, tailWord_702776, baseEnd_702776] using wordTrace_append hprefix tailTrace_702776
  have hstable : (prefixWord ++ tailWord_702776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702776).length < 2 ^ (prefixWord ++ tailWord_702776).sum := by decide
  have hdescent : baseEnd_702776 < baseStart_702776 := by decide
  rcases family_descends (prefixWord ++ tailWord_702776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702807 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_702807 : Nat := 118140960795 + 702807 * 2 ^ 59
def prefixEnd_702807 : Nat := 4983230072969 + 3 ^ 40 * 702807 * 2
def baseEnd_702807 : Nat := 320780265195143998293649

theorem tailTrace_702807 : CollatzResearch.WordTrace tailWord_702807 prefixEnd_702807 320780265195143998293649 := by
  unfold tailWord_702807
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633477164857743724642675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17088984776571829149761783 25633477164857743724642675)
  ·
    refine ⟨38450215747286615586964013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25633477164857743724642675 38450215747286615586964013)
    ·
      refine ⟨14418830905232480845111505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38450215747286615586964013 14418830905232480845111505)
      ·
        refine ⟨10814123178924360633833629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14418830905232480845111505 10814123178924360633833629)
        ·
          refine ⟨4055296192096635237687611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10814123178924360633833629 4055296192096635237687611)
          ·
            refine ⟨6082944288144952856531417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055296192096635237687611 6082944288144952856531417)
            ·
              refine ⟨4562208216108714642398563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082944288144952856531417 4562208216108714642398563)
              ·
                refine ⟨6843312324163071963597845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562208216108714642398563 6843312324163071963597845)
                ·
                  refine ⟨320780265195143998293649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6843312324163071963597845 320780265195143998293649)
                  ·
                    rfl

theorem cell20_702807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_702807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702807 prefixEnd_702807 := by exact prefixLift 702807
  have htrace : WordTrace (prefixWord ++ tailWord_702807) baseStart_702807 baseEnd_702807 := by
    simpa [prefixWord, tailWord_702807, baseEnd_702807] using wordTrace_append hprefix tailTrace_702807
  have hstable : (prefixWord ++ tailWord_702807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702807).length < 2 ^ (prefixWord ++ tailWord_702807).sum := by decide
  have hdescent : baseEnd_702807 < baseStart_702807 := by decide
  rcases family_descends (prefixWord ++ tailWord_702807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702837 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 2]
def baseStart_702837 : Nat := 118140960795 + 702837 * 2 ^ 59
def prefixEnd_702837 : Nat := 4983230072969 + 3 ^ 40 * 702837 * 2
def baseEnd_702837 : Nat := 320793958012597227293527

theorem tailTrace_702837 : CollatzResearch.WordTrace tailWord_702837 prefixEnd_702837 320793958012597227293527 := by
  unfold tailWord_702837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25634571354749058848234765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17089714236499372565489843 25634571354749058848234765)
  ·
    refine ⟨9612964258030897068088037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25634571354749058848234765 9612964258030897068088037)
    ·
      refine ⟨1802430798380793200266507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9612964258030897068088037 1802430798380793200266507)
      ·
        refine ⟨2703646197571189800399761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802430798380793200266507 2703646197571189800399761)
        ·
          refine ⟨2027734648178392350299821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2703646197571189800399761 2027734648178392350299821)
          ·
            refine ⟨760400493066897131362433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2027734648178392350299821 760400493066897131362433)
            ·
              refine ⟨570300369800172848521825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760400493066897131362433 570300369800172848521825)
              ·
                refine ⟨427725277350129636391369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570300369800172848521825 427725277350129636391369)
                ·
                  refine ⟨320793958012597227293527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427725277350129636391369 320793958012597227293527)
                  ·
                    rfl

theorem cell20_702837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_702837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702837 prefixEnd_702837 := by exact prefixLift 702837
  have htrace : WordTrace (prefixWord ++ tailWord_702837) baseStart_702837 baseEnd_702837 := by
    simpa [prefixWord, tailWord_702837, baseEnd_702837] using wordTrace_append hprefix tailTrace_702837
  have hstable : (prefixWord ++ tailWord_702837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702837).length < 2 ^ (prefixWord ++ tailWord_702837).sum := by decide
  have hdescent : baseEnd_702837 < baseStart_702837 := by decide
  rcases family_descends (prefixWord ++ tailWord_702837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702862 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_702862 : Nat := 118140960795 + 702862 * 2 ^ 59
def prefixEnd_702862 : Nat := 4983230072969 + 3 ^ 40 * 702862 * 2
def baseEnd_702862 : Nat := 320805368693808251460091

theorem tailTrace_702862 : CollatzResearch.WordTrace tailWord_702862 prefixEnd_702862 320805368693808251460091 := by
  unfold tailWord_702862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204435397457311014736855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17090322119772325411929893 3204435397457311014736855)
  ·
    refine ⟨4806653096185966522105283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3204435397457311014736855 4806653096185966522105283)
    ·
      refine ⟨7209979644278949783157925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4806653096185966522105283 7209979644278949783157925)
      ·
        refine ⟨1351871183302303084342111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7209979644278949783157925 1351871183302303084342111)
        ·
          refine ⟨2027806774953454626513167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351871183302303084342111 2027806774953454626513167)
          ·
            refine ⟨3041710162430181939769751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027806774953454626513167 3041710162430181939769751)
            ·
              refine ⟨4562565243645272909654627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041710162430181939769751 4562565243645272909654627)
              ·
                refine ⟨6843847865467909364481941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562565243645272909654627 6843847865467909364481941)
                ·
                  refine ⟨320805368693808251460091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6843847865467909364481941 320805368693808251460091)
                  ·
                    rfl

theorem cell20_702862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_702862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702862 prefixEnd_702862 := by exact prefixLift 702862
  have htrace : WordTrace (prefixWord ++ tailWord_702862) baseStart_702862 baseEnd_702862 := by
    simpa [prefixWord, tailWord_702862, baseEnd_702862] using wordTrace_append hprefix tailTrace_702862
  have hstable : (prefixWord ++ tailWord_702862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702862).length < 2 ^ (prefixWord ++ tailWord_702862).sum := by decide
  have hdescent : baseEnd_702862 < baseStart_702862 := by decide
  rcases family_descends (prefixWord ++ tailWord_702862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702879 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 2]
def baseStart_702879 : Nat := 118140960795 + 702879 * 2 ^ 59
def prefixEnd_702879 : Nat := 4983230072969 + 3 ^ 40 * 702879 * 2
def baseEnd_702879 : Nat := 320813127957031747893355

theorem tailTrace_702879 : CollatzResearch.WordTrace tailWord_702879 prefixEnd_702879 320813127957031747893355 := by
  unfold tailWord_702879
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636103220596900021263691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17090735480397933347509127 25636103220596900021263691)
  ·
    refine ⟨38454154830895350031895537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25636103220596900021263691 38454154830895350031895537)
    ·
      refine ⟨28840616123171512523921653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38454154830895350031895537 28840616123171512523921653)
      ·
        refine ⟨2703807761547329299117655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28840616123171512523921653 2703807761547329299117655)
        ·
          refine ⟨4055711642320993948676483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703807761547329299117655 4055711642320993948676483)
          ·
            refine ⟨6083567463481490923014725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055711642320993948676483 6083567463481490923014725)
            ·
              refine ⟨1140668899402779548065261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6083567463481490923014725 1140668899402779548065261)
              ·
                refine ⟨427750837276042330524473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140668899402779548065261 427750837276042330524473)
                ·
                  refine ⟨320813127957031747893355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427750837276042330524473 320813127957031747893355)
                  ·
                    rfl

theorem cell20_702879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2].length) (baseStart_702879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702879 prefixEnd_702879 := by exact prefixLift 702879
  have htrace : WordTrace (prefixWord ++ tailWord_702879) baseStart_702879 baseEnd_702879 := by
    simpa [prefixWord, tailWord_702879, baseEnd_702879] using wordTrace_append hprefix tailTrace_702879
  have hstable : (prefixWord ++ tailWord_702879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702879).length < 2 ^ (prefixWord ++ tailWord_702879).sum := by decide
  have hdescent : baseEnd_702879 < baseStart_702879 := by decide
  rcases family_descends (prefixWord ++ tailWord_702879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702921 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_702921 : Nat := 118140960795 + 702921 * 2 ^ 59
def prefixEnd_702921 : Nat := 4983230072969 + 3 ^ 40 * 702921 * 2
def baseEnd_702921 : Nat := 320832297901466268493183

theorem tailTrace_702921 : CollatzResearch.WordTrace tailWord_702921 prefixEnd_702921 320832297901466268493183 := by
  unfold tailWord_702921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25637635086444741194292617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17091756724296494129528411 25637635086444741194292617)
  ·
    refine ⟨19228226314833555895719463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25637635086444741194292617 19228226314833555895719463)
    ·
      refine ⟨28842339472250333843579195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19228226314833555895719463 28842339472250333843579195)
      ·
        refine ⟨43263509208375500765368793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28842339472250333843579195 43263509208375500765368793)
        ·
          refine ⟨32447631906281625574026595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43263509208375500765368793 32447631906281625574026595)
          ·
            refine ⟨48671447859422438361039893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32447631906281625574026595 48671447859422438361039893)
            ·
              refine ⟨2281474118410426798173745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48671447859422438361039893 2281474118410426798173745)
              ·
                refine ⟨1711105588807820098630309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281474118410426798173745 1711105588807820098630309)
                ·
                  refine ⟨320832297901466268493183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711105588807820098630309 320832297901466268493183)
                  ·
                    rfl

theorem cell20_702921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_702921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702921 prefixEnd_702921 := by exact prefixLift 702921
  have htrace : WordTrace (prefixWord ++ tailWord_702921) baseStart_702921 baseEnd_702921 := by
    simpa [prefixWord, tailWord_702921, baseEnd_702921] using wordTrace_append hprefix tailTrace_702921
  have hstable : (prefixWord ++ tailWord_702921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702921).length < 2 ^ (prefixWord ++ tailWord_702921).sum := by decide
  have hdescent : baseEnd_702921 < baseStart_702921 := by decide
  rcases family_descends (prefixWord ++ tailWord_702921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702930 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_702930 : Nat := 118140960795 + 702930 * 2 ^ 59
def prefixEnd_702930 : Nat := 4983230072969 + 3 ^ 40 * 702930 * 2
def baseEnd_702930 : Nat := 320836405746702237193147

theorem tailTrace_702930 : CollatzResearch.WordTrace tailWord_702930 prefixEnd_702930 320836405746702237193147 := by
  unfold tailWord_702930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409490835853033932842561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17091975562274757154246829 6409490835853033932842561)
  ·
    refine ⟨4807118126889775449631921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6409490835853033932842561 4807118126889775449631921)
    ·
      refine ⟨3605338595167331587223941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4807118126889775449631921 3605338595167331587223941)
      ·
        refine ⟨676000986593874672604489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3605338595167331587223941 676000986593874672604489)
        ·
          refine ⟨507000739945406004453367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676000986593874672604489 507000739945406004453367)
          ·
            refine ⟨760501109918109006680051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507000739945406004453367 760501109918109006680051)
            ·
              refine ⟨1140751664877163510020077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760501109918109006680051 1140751664877163510020077)
              ·
                refine ⟨427781874328936316257529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140751664877163510020077 427781874328936316257529)
                ·
                  refine ⟨320836405746702237193147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427781874328936316257529 320836405746702237193147)
                  ·
                    rfl

theorem cell20_702930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_702930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702930 prefixEnd_702930 := by exact prefixLift 702930
  have htrace : WordTrace (prefixWord ++ tailWord_702930) baseStart_702930 baseEnd_702930 := by
    simpa [prefixWord, tailWord_702930, baseEnd_702930] using wordTrace_append hprefix tailTrace_702930
  have hstable : (prefixWord ++ tailWord_702930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702930).length < 2 ^ (prefixWord ++ tailWord_702930).sum := by decide
  have hdescent : baseEnd_702930 < baseStart_702930 := by decide
  rcases family_descends (prefixWord ++ tailWord_702930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702952 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_702952 : Nat := 118140960795 + 702952 * 2 ^ 59
def prefixEnd_702952 : Nat := 4983230072969 + 3 ^ 40 * 702952 * 2
def baseEnd_702952 : Nat := 320846447146167938459723

theorem tailTrace_702952 : CollatzResearch.WordTrace tailWord_702952 prefixEnd_702952 320846447146167938459723 := by
  unfold tailWord_702952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12819382874666216744335555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17092510499554955659114073 12819382874666216744335555)
  ·
    refine ⟨19229074311999325116503333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12819382874666216744335555 19229074311999325116503333)
    ·
      refine ⟨3605451433499873459344375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19229074311999325116503333 3605451433499873459344375)
      ·
        refine ⟨5408177150249810189016563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605451433499873459344375 5408177150249810189016563)
        ·
          refine ⟨8112265725374715283524845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408177150249810189016563 8112265725374715283524845)
          ·
            refine ⟨3042099647015518231321817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8112265725374715283524845 3042099647015518231321817)
            ·
              refine ⟨2281574735261638673491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042099647015518231321817 2281574735261638673491363)
              ·
                refine ⟨3422362102892458010237045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281574735261638673491363 3422362102892458010237045)
                ·
                  refine ⟨320846447146167938459723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3422362102892458010237045 320846447146167938459723)
                  ·
                    rfl

theorem cell20_702952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_702952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702952 prefixEnd_702952 := by exact prefixLift 702952
  have htrace : WordTrace (prefixWord ++ tailWord_702952) baseStart_702952 baseEnd_702952 := by
    simpa [prefixWord, tailWord_702952, baseEnd_702952] using wordTrace_append hprefix tailTrace_702952
  have hstable : (prefixWord ++ tailWord_702952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702952).length < 2 ^ (prefixWord ++ tailWord_702952).sum := by decide
  have hdescent : baseEnd_702952 < baseStart_702952 := by decide
  rcases family_descends (prefixWord ++ tailWord_702952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702955 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 2]
def baseStart_702955 : Nat := 118140960795 + 702955 * 2 ^ 59
def prefixEnd_702955 : Nat := 4983230072969 + 3 ^ 40 * 702955 * 2
def baseEnd_702955 : Nat := 320847816427913261359711

theorem tailTrace_702955 : CollatzResearch.WordTrace tailWord_702955 prefixEnd_702955 320847816427913261359711 := by
  unfold tailWord_702955
  simp only [CollatzResearch.WordTrace]
  refine ⟨25638875168321565001030319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17092583445547710000686879 25638875168321565001030319)
  ·
    refine ⟨38458312752482347501545479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25638875168321565001030319 38458312752482347501545479)
    ·
      refine ⟨57687469128723521252318219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38458312752482347501545479 57687469128723521252318219)
      ·
        refine ⟨86531203693085281878477329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57687469128723521252318219 86531203693085281878477329)
        ·
          refine ⟨64898402769813961408857997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86531203693085281878477329 64898402769813961408857997)
          ·
            refine ⟨24336901038680235528321749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64898402769813961408857997 24336901038680235528321749)
            ·
              refine ⟨570396118094068020195041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24336901038680235528321749 570396118094068020195041)
              ·
                refine ⟨427797088570551015146281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570396118094068020195041 427797088570551015146281)
                ·
                  refine ⟨320847816427913261359711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427797088570551015146281 320847816427913261359711)
                  ·
                    rfl

theorem cell20_702955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2].length) (baseStart_702955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702955 prefixEnd_702955 := by exact prefixLift 702955
  have htrace : WordTrace (prefixWord ++ tailWord_702955) baseStart_702955 baseEnd_702955 := by
    simpa [prefixWord, tailWord_702955, baseEnd_702955] using wordTrace_append hprefix tailTrace_702955
  have hstable : (prefixWord ++ tailWord_702955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702955).length < 2 ^ (prefixWord ++ tailWord_702955).sum := by decide
  have hdescent : baseEnd_702955 < baseStart_702955 := by decide
  rcases family_descends (prefixWord ++ tailWord_702955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702962 : List Nat := [3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_702962 : Nat := 118140960795 + 702962 * 2 ^ 59
def prefixEnd_702962 : Nat := 4983230072969 + 3 ^ 40 * 702962 * 2
def baseEnd_702962 : Nat := 106950337139550782708783

theorem tailTrace_702962 : CollatzResearch.WordTrace tailWord_702962 prefixEnd_702962 106950337139550782708783 := by
  unfold tailWord_702962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409782619824051299133785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17092753652864136797690093 6409782619824051299133785)
  ·
    refine ⟨4807336964868038474350339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6409782619824051299133785 4807336964868038474350339)
    ·
      refine ⟨7211005447302057711525509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4807336964868038474350339 7211005447302057711525509)
      ·
        refine ⟨1352063521369135820911033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7211005447302057711525509 1352063521369135820911033)
        ·
          refine ⟨1014047641026851865683275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352063521369135820911033 1014047641026851865683275)
          ·
            refine ⟨1521071461540277798524913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014047641026851865683275 1521071461540277798524913)
            ·
              refine ⟨1140803596155208348893685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521071461540277798524913 1140803596155208348893685)
              ·
                refine ⟨106950337139550782708783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1140803596155208348893685 106950337139550782708783)
                ·
                  rfl

theorem cell20_702962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_702962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702962 prefixEnd_702962 := by exact prefixLift 702962
  have htrace : WordTrace (prefixWord ++ tailWord_702962) baseStart_702962 baseEnd_702962 := by
    simpa [prefixWord, tailWord_702962, baseEnd_702962] using wordTrace_append hprefix tailTrace_702962
  have hstable : (prefixWord ++ tailWord_702962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702962).length < 2 ^ (prefixWord ++ tailWord_702962).sum := by decide
  have hdescent : baseEnd_702962 < baseStart_702962 := by decide
  rcases family_descends (prefixWord ++ tailWord_702962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702969 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 3]
def baseStart_702969 : Nat := 118140960795 + 702969 * 2 ^ 59
def prefixEnd_702969 : Nat := 4983230072969 + 3 ^ 40 * 702969 * 2
def baseEnd_702969 : Nat := 320854206409391434892987

theorem tailTrace_702969 : CollatzResearch.WordTrace tailWord_702969 prefixEnd_702969 320854206409391434892987 := by
  unfold tailWord_702969
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639385790270845392039961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17092923860180563594693307 25639385790270845392039961)
  ·
    refine ⟨19229539342703134044029971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25639385790270845392039961 19229539342703134044029971)
    ·
      refine ⟨28844309014054701066044957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19229539342703134044029971 28844309014054701066044957)
      ·
        refine ⟨10816615880270512899766859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28844309014054701066044957 10816615880270512899766859)
        ·
          refine ⟨16224923820405769349650289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10816615880270512899766859 16224923820405769349650289)
          ·
            refine ⟨12168692865304327012237717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16224923820405769349650289 12168692865304327012237717)
            ·
              refine ⟨570407478061140328698643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12168692865304327012237717 570407478061140328698643)
              ·
                refine ⟨855611217091710493047965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570407478061140328698643 855611217091710493047965)
                ·
                  refine ⟨320854206409391434892987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855611217091710493047965 320854206409391434892987)
                  ·
                    rfl

theorem cell20_702969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_702969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_702969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_702969 prefixEnd_702969 := by exact prefixLift 702969
  have htrace : WordTrace (prefixWord ++ tailWord_702969) baseStart_702969 baseEnd_702969 := by
    simpa [prefixWord, tailWord_702969, baseEnd_702969] using wordTrace_append hprefix tailTrace_702969
  have hstable : (prefixWord ++ tailWord_702969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702969).length < 2 ^ (prefixWord ++ tailWord_702969).sum := by decide
  have hdescent : baseEnd_702969 < baseStart_702969 := by decide
  rcases family_descends (prefixWord ++ tailWord_702969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703004 : List Nat := [2, 2, 3, 1, 2, 10]
def baseStart_703004 : Nat := 118140960795 + 703004 * 2 ^ 59
def prefixEnd_703004 : Nat := 4983230072969 + 3 ^ 40 * 703004 * 2
def baseEnd_703004 : Nat := 11884080791225439582451

theorem tailTrace_703004 : CollatzResearch.WordTrace tailWord_703004 prefixEnd_703004 11884080791225439582451 := by
  unfold tailWord_703004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820331172572023184782033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17093774896762697579709377 12820331172572023184782033)
  ·
    refine ⟨9615248379429017388586525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12820331172572023184782033 9615248379429017388586525)
    ·
      refine ⟨3605718142285881520719947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9615248379429017388586525 3605718142285881520719947)
      ·
        refine ⟨5408577213428822281079921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605718142285881520719947 5408577213428822281079921)
        ·
          refine ⟨4056432910071616710809941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5408577213428822281079921 4056432910071616710809941)
          ·
            refine ⟨11884080791225439582451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4056432910071616710809941 11884080791225439582451)
            ·
              rfl

theorem cell20_703004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 10].length) (baseStart_703004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703004 prefixEnd_703004 := by exact prefixLift 703004
  have htrace : WordTrace (prefixWord ++ tailWord_703004) baseStart_703004 baseEnd_703004 := by
    simpa [prefixWord, tailWord_703004, baseEnd_703004] using wordTrace_append hprefix tailTrace_703004
  have hstable : (prefixWord ++ tailWord_703004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703004).length < 2 ^ (prefixWord ++ tailWord_703004).sum := by decide
  have hdescent : baseEnd_703004 < baseStart_703004 := by decide
  rcases family_descends (prefixWord ++ tailWord_703004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703044 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_703044 : Nat := 118140960795 + 703044 * 2 ^ 59
def prefixEnd_703044 : Nat := 4983230072969 + 3 ^ 40 * 703044 * 2
def baseEnd_703044 : Nat := 320888438453024507392681

theorem tailTrace_703044 : CollatzResearch.WordTrace tailWord_703044 prefixEnd_703044 320888438453024507392681 := by
  unfold tailWord_703044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821060632499566600510093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17094747509999422134013457 12821060632499566600510093)
  ·
    refine ⟨4807897737187337475191285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12821060632499566600510093 4807897737187337475191285)
    ·
      refine ⟨450740412861312888299183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4807897737187337475191285 450740412861312888299183)
      ·
        refine ⟨676110619291969332448775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450740412861312888299183 676110619291969332448775)
        ·
          refine ⟨1014165928937953998673163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676110619291969332448775 1014165928937953998673163)
          ·
            refine ⟨1521248893406930998009745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014165928937953998673163 1521248893406930998009745)
            ·
              refine ⟨1140936670055198248507309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521248893406930998009745 1140936670055198248507309)
              ·
                refine ⟨427851251270699343190241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140936670055198248507309 427851251270699343190241)
                ·
                  refine ⟨320888438453024507392681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427851251270699343190241 320888438453024507392681)
                  ·
                    rfl

theorem cell20_703044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_703044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703044 prefixEnd_703044 := by exact prefixLift 703044
  have htrace : WordTrace (prefixWord ++ tailWord_703044) baseStart_703044 baseEnd_703044 := by
    simpa [prefixWord, tailWord_703044, baseEnd_703044] using wordTrace_append hprefix tailTrace_703044
  have hstable : (prefixWord ++ tailWord_703044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703044).length < 2 ^ (prefixWord ++ tailWord_703044).sum := by decide
  have hdescent : baseEnd_703044 < baseStart_703044 := by decide
  rcases family_descends (prefixWord ++ tailWord_703044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703073 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_703073 : Nat := 118140960795 + 703073 * 2 ^ 59
def prefixEnd_703073 : Nat := 4983230072969 + 3 ^ 40 * 703073 * 2
def baseEnd_703073 : Nat := 320901674843229295425895

theorem tailTrace_703073 : CollatzResearch.WordTrace tailWord_703073 prefixEnd_703073 320901674843229295425895 := by
  unfold tailWord_703073
  simp only [CollatzResearch.WordTrace]
  refine ⟨25643178981894071153825873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17095452654596047435883915 25643178981894071153825873)
  ·
    refine ⟨19232384236420553365369405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25643178981894071153825873 19232384236420553365369405)
    ·
      refine ⟨7212144088657707512013527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19232384236420553365369405 7212144088657707512013527)
      ·
        refine ⟨10818216132986561268020291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212144088657707512013527 10818216132986561268020291)
        ·
          refine ⟨16227324199479841902030437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818216132986561268020291 16227324199479841902030437)
          ·
            refine ⟨3042623287402470356630707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16227324199479841902030437 3042623287402470356630707)
            ·
              refine ⟨4563934931103705534946061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042623287402470356630707 4563934931103705534946061)
              ·
                refine ⟨1711475599163889575604773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4563934931103705534946061 1711475599163889575604773)
                ·
                  refine ⟨320901674843229295425895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711475599163889575604773 320901674843229295425895)
                  ·
                    rfl

theorem cell20_703073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_703073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703073 prefixEnd_703073 := by exact prefixLift 703073
  have htrace : WordTrace (prefixWord ++ tailWord_703073) baseStart_703073 baseEnd_703073 := by
    simpa [prefixWord, tailWord_703073, baseEnd_703073] using wordTrace_append hprefix tailTrace_703073
  have hstable : (prefixWord ++ tailWord_703073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703073).length < 2 ^ (prefixWord ++ tailWord_703073).sum := by decide
  have hdescent : baseEnd_703073 < baseStart_703073 := by decide
  rcases family_descends (prefixWord ++ tailWord_703073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703093 : List Nat := [1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_703093 : Nat := 118140960795 + 703093 * 2 ^ 59
def prefixEnd_703093 : Nat := 4983230072969 + 3 ^ 40 * 703093 * 2
def baseEnd_703093 : Nat := 106970267796066038253049

theorem tailTrace_703093 : CollatzResearch.WordTrace tailWord_703093 prefixEnd_703093 106970267796066038253049 := by
  unfold tailWord_703093
  simp only [CollatzResearch.WordTrace]
  refine ⟨25643908441821614569553933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17095938961214409713035955 25643908441821614569553933)
  ·
    refine ⟨9616465665683105463582725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25643908441821614569553933 9616465665683105463582725)
    ·
      refine ⟨1803087312315582274421761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9616465665683105463582725 1803087312315582274421761)
      ·
        refine ⟨1352315484236686705816321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1803087312315582274421761 1352315484236686705816321)
        ·
          refine ⟨1014236613177515029362241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352315484236686705816321 1014236613177515029362241)
          ·
            refine ⟨760677459883136272021681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014236613177515029362241 760677459883136272021681)
            ·
              refine ⟨570508094912352204016261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760677459883136272021681 570508094912352204016261)
              ·
                refine ⟨106970267796066038253049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570508094912352204016261 106970267796066038253049)
                ·
                  rfl

theorem cell20_703093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_703093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703093 prefixEnd_703093 := by exact prefixLift 703093
  have htrace : WordTrace (prefixWord ++ tailWord_703093) baseStart_703093 baseEnd_703093 := by
    simpa [prefixWord, tailWord_703093, baseEnd_703093] using wordTrace_append hprefix tailTrace_703093
  have hstable : (prefixWord ++ tailWord_703093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703093).length < 2 ^ (prefixWord ++ tailWord_703093).sum := by decide
  have hdescent : baseEnd_703093 < baseStart_703093 := by decide
  rcases family_descends (prefixWord ++ tailWord_703093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703097 : List Nat := [1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_703097 : Nat := 118140960795 + 703097 * 2 ^ 59
def prefixEnd_703097 : Nat := 4983230072969 + 3 ^ 40 * 703097 * 2
def baseEnd_703097 : Nat := 106970876365730626208599

theorem tailTrace_703097 : CollatzResearch.WordTrace tailWord_703097 prefixEnd_703097 106970876365730626208599 := by
  unfold tailWord_703097
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644054333807123252699545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17096036222538082168466363 25644054333807123252699545)
  ·
    refine ⟨19233040750355342439524659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25644054333807123252699545 19233040750355342439524659)
    ·
      refine ⟨28849561125533013659286989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19233040750355342439524659 28849561125533013659286989)
      ·
        refine ⟨10818585422074880122232621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28849561125533013659286989 10818585422074880122232621)
        ·
          refine ⟨4056969533278080045837233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10818585422074880122232621 4056969533278080045837233)
          ·
            refine ⟨3042727149958560034377925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056969533278080045837233 3042727149958560034377925)
            ·
              refine ⟨570511340617230006445861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3042727149958560034377925 570511340617230006445861)
              ·
                refine ⟨106970876365730626208599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570511340617230006445861 106970876365730626208599)
                ·
                  rfl

theorem cell20_703097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_703097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703097 prefixEnd_703097 := by exact prefixLift 703097
  have htrace : WordTrace (prefixWord ++ tailWord_703097) baseStart_703097 baseEnd_703097 := by
    simpa [prefixWord, tailWord_703097, baseEnd_703097] using wordTrace_append hprefix tailTrace_703097
  have hstable : (prefixWord ++ tailWord_703097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703097).length < 2 ^ (prefixWord ++ tailWord_703097).sum := by decide
  have hdescent : baseEnd_703097 < baseStart_703097 := by decide
  rcases family_descends (prefixWord ++ tailWord_703097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703114 : List Nat := [3, 1, 2, 3, 4, 1, 6]
def baseStart_703114 : Nat := 118140960795 + 703114 * 2 ^ 59
def prefixEnd_703114 : Nat := 4983230072969 + 3 ^ 40 * 703114 * 2
def baseEnd_703114 : Nat := 35657820928935041673229

theorem tailTrace_703114 : CollatzResearch.WordTrace tailWord_703114 prefixEnd_703114 35657820928935041673229 := by
  unfold tailWord_703114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411168593686383789017099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17096449583163690104045597 6411168593686383789017099)
  ·
    refine ⟨9616752890529575683525649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411168593686383789017099 9616752890529575683525649)
    ·
      refine ⟨7212564667897181762644237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9616752890529575683525649 7212564667897181762644237)
      ·
        refine ⟨2704711750461443160991589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7212564667897181762644237 2704711750461443160991589)
        ·
          refine ⟨507133453211520592685923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2704711750461443160991589 507133453211520592685923)
          ·
            refine ⟨760700179817280889028885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507133453211520592685923 760700179817280889028885)
            ·
              refine ⟨35657820928935041673229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 760700179817280889028885 35657820928935041673229)
              ·
                rfl

theorem cell20_703114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 6].length) (baseStart_703114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703114 prefixEnd_703114 := by exact prefixLift 703114
  have htrace : WordTrace (prefixWord ++ tailWord_703114) baseStart_703114 baseEnd_703114 := by
    simpa [prefixWord, tailWord_703114, baseEnd_703114] using wordTrace_append hprefix tailTrace_703114
  have hstable : (prefixWord ++ tailWord_703114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703114).length < 2 ^ (prefixWord ++ tailWord_703114).sum := by decide
  have hdescent : baseEnd_703114 < baseStart_703114 := by decide
  rcases family_descends (prefixWord ++ tailWord_703114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703242 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_703242 : Nat := 118140960795 + 703242 * 2 ^ 59
def prefixEnd_703242 : Nat := 4983230072969 + 3 ^ 40 * 703242 * 2
def baseEnd_703242 : Nat := 320978811048215818791871

theorem tailTrace_703242 : CollatzResearch.WordTrace tailWord_703242 prefixEnd_703242 320978811048215818791871 := by
  unfold tailWord_703242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412335729570453254181995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17099561945521208677818653 6412335729570453254181995)
  ·
    refine ⟨9618503594355679881272993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412335729570453254181995 9618503594355679881272993)
    ·
      refine ⟨7213877695766759910954745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9618503594355679881272993 7213877695766759910954745)
      ·
        refine ⟨5410408271825069933216059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7213877695766759910954745 5410408271825069933216059)
        ·
          refine ⟨8115612407737604899824089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410408271825069933216059 8115612407737604899824089)
          ·
            refine ⟨6086709305803203674868067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115612407737604899824089 6086709305803203674868067)
            ·
              refine ⟨9130063958704805512302101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6086709305803203674868067 9130063958704805512302101)
              ·
                refine ⟨427971748064287758389161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9130063958704805512302101 427971748064287758389161)
                ·
                  refine ⟨320978811048215818791871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427971748064287758389161 320978811048215818791871)
                  ·
                    rfl

theorem cell20_703242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_703242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703242 prefixEnd_703242 := by exact prefixLift 703242
  have htrace : WordTrace (prefixWord ++ tailWord_703242) baseStart_703242 baseEnd_703242 := by
    simpa [prefixWord, tailWord_703242, baseEnd_703242] using wordTrace_append hprefix tailTrace_703242
  have hstable : (prefixWord ++ tailWord_703242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703242).length < 2 ^ (prefixWord ++ tailWord_703242).sum := by decide
  have hdescent : baseEnd_703242 < baseStart_703242 := by decide
  rcases family_descends (prefixWord ++ tailWord_703242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703263 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_703263 : Nat := 118140960795 + 703263 * 2 ^ 59
def prefixEnd_703263 : Nat := 4983230072969 + 3 ^ 40 * 703263 * 2
def baseEnd_703263 : Nat := 320988396020433079091785

theorem tailTrace_703263 : CollatzResearch.WordTrace tailWord_703263 prefixEnd_703263 320988396020433079091785 := by
  unfold tailWord_703263
  simp only [CollatzResearch.WordTrace]
  refine ⟨25650108851205733603242443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17100072567470489068828295 25650108851205733603242443)
  ·
    refine ⟨38475163276808600404863665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25650108851205733603242443 38475163276808600404863665)
    ·
      refine ⟨28856372457606450303647749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38475163276808600404863665 28856372457606450303647749)
      ·
        refine ⟨5410569835801209431933953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28856372457606450303647749 5410569835801209431933953)
        ·
          refine ⟨4057927376850907073950465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5410569835801209431933953 4057927376850907073950465)
          ·
            refine ⟨3043445532638180305462849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057927376850907073950465 3043445532638180305462849)
            ·
              refine ⟨2282584149478635229097137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043445532638180305462849 2282584149478635229097137)
              ·
                refine ⟨1711938112108976421822853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282584149478635229097137 1711938112108976421822853)
                ·
                  refine ⟨320988396020433079091785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711938112108976421822853 320988396020433079091785)
                  ·
                    rfl

theorem cell20_703263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_703263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703263 prefixEnd_703263 := by exact prefixLift 703263
  have htrace : WordTrace (prefixWord ++ tailWord_703263) baseStart_703263 baseEnd_703263 := by
    simpa [prefixWord, tailWord_703263, baseEnd_703263] using wordTrace_append hprefix tailTrace_703263
  have hstable : (prefixWord ++ tailWord_703263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703263).length < 2 ^ (prefixWord ++ tailWord_703263).sum := by decide
  have hdescent : baseEnd_703263 < baseStart_703263 := by decide
  rcases family_descends (prefixWord ++ tailWord_703263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703266 : List Nat := [3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_703266 : Nat := 118140960795 + 703266 * 2 ^ 59
def prefixEnd_703266 : Nat := 4983230072969 + 3 ^ 40 * 703266 * 2
def baseEnd_703266 : Nat := 106996588434059467330591

theorem tailTrace_703266 : CollatzResearch.WordTrace tailWord_703266 prefixEnd_703266 106996588434059467330591 := by
  unfold tailWord_703266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412554567548716278900413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17100145513463243410401101 6412554567548716278900413)
  ·
    refine ⟨2404707962830768604587655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6412554567548716278900413 2404707962830768604587655)
    ·
      refine ⟨3607061944246152906881483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404707962830768604587655 3607061944246152906881483)
      ·
        refine ⟨5410592916369229360322225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607061944246152906881483 5410592916369229360322225)
        ·
          refine ⟨4057944687276922020241669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5410592916369229360322225 4057944687276922020241669)
          ·
            refine ⟨760864628864422878795313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4057944687276922020241669 760864628864422878795313)
            ·
              refine ⟨570648471648317159096485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760864628864422878795313 570648471648317159096485)
              ·
                refine ⟨106996588434059467330591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570648471648317159096485 106996588434059467330591)
                ·
                  rfl

theorem cell20_703266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_703266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703266 prefixEnd_703266 := by exact prefixLift 703266
  have htrace : WordTrace (prefixWord ++ tailWord_703266) baseStart_703266 baseEnd_703266 := by
    simpa [prefixWord, tailWord_703266, baseEnd_703266] using wordTrace_append hprefix tailTrace_703266
  have hstable : (prefixWord ++ tailWord_703266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703266).length < 2 ^ (prefixWord ++ tailWord_703266).sum := by decide
  have hdescent : baseEnd_703266 < baseStart_703266 := by decide
  rcases family_descends (prefixWord ++ tailWord_703266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703308 : List Nat := [2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_703308 : Nat := 118140960795 + 703308 * 2 ^ 59
def prefixEnd_703308 : Nat := 4983230072969 + 3 ^ 40 * 703308 * 2
def baseEnd_703308 : Nat := 107002978415537640863867

theorem tailTrace_703308 : CollatzResearch.WordTrace tailWord_703308 prefixEnd_703308 107002978415537640863867 := by
  unfold tailWord_703308
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825875068021353144315289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17101166757361804192420385 12825875068021353144315289)
  ·
    refine ⟨9619406301016014858236467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12825875068021353144315289 9619406301016014858236467)
    ·
      refine ⟨14429109451524022287354701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9619406301016014858236467 14429109451524022287354701)
      ·
        refine ⟨5410916044321508357758013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14429109451524022287354701 5410916044321508357758013)
        ·
          refine ⟨2029093516620565634159255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5410916044321508357758013 2029093516620565634159255)
          ·
            refine ⟨3043640274930848451238883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029093516620565634159255 3043640274930848451238883)
            ·
              refine ⟨4565460412396272676858325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043640274930848451238883 4565460412396272676858325)
              ·
                refine ⟨107002978415537640863867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4565460412396272676858325 107002978415537640863867)
                ·
                  rfl

theorem cell20_703308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_703308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703308 prefixEnd_703308 := by exact prefixLift 703308
  have htrace : WordTrace (prefixWord ++ tailWord_703308) baseStart_703308 baseEnd_703308 := by
    simpa [prefixWord, tailWord_703308, baseEnd_703308] using wordTrace_append hprefix tailTrace_703308
  have hstable : (prefixWord ++ tailWord_703308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703308).length < 2 ^ (prefixWord ++ tailWord_703308).sum := by decide
  have hdescent : baseEnd_703308 < baseStart_703308 := by decide
  rcases family_descends (prefixWord ++ tailWord_703308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703349 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_703349 : Nat := 118140960795 + 703349 * 2 ^ 59
def prefixEnd_703349 : Nat := 4983230072969 + 3 ^ 40 * 703349 * 2
def baseEnd_703349 : Nat := 321027648763799002224767

theorem tailTrace_703349 : CollatzResearch.WordTrace tailWord_703349 prefixEnd_703349 321027648763799002224767 := by
  unfold tailWord_703349
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653245528894170290873101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17102163685929446860582067 25653245528894170290873101)
  ·
    refine ⟨9619967073335313859077413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25653245528894170290873101 9619967073335313859077413)
    ·
      refine ⟨1803743826250371348577015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9619967073335313859077413 1803743826250371348577015)
      ·
        refine ⟨2705615739375557022865523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803743826250371348577015 2705615739375557022865523)
        ·
          refine ⟨4058423609063335534298285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705615739375557022865523 4058423609063335534298285)
          ·
            refine ⟨1521908853398750825361857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4058423609063335534298285 1521908853398750825361857)
            ·
              refine ⟨1141431640049063119021393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521908853398750825361857 1141431640049063119021393)
              ·
                refine ⟨856073730036797339266045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141431640049063119021393 856073730036797339266045)
                ·
                  refine ⟨321027648763799002224767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856073730036797339266045 321027648763799002224767)
                  ·
                    rfl

theorem cell20_703349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_703349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703349 prefixEnd_703349 := by exact prefixLift 703349
  have htrace : WordTrace (prefixWord ++ tailWord_703349) baseStart_703349 baseEnd_703349 := by
    simpa [prefixWord, tailWord_703349, baseEnd_703349] using wordTrace_append hprefix tailTrace_703349
  have hstable : (prefixWord ++ tailWord_703349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703349).length < 2 ^ (prefixWord ++ tailWord_703349).sum := by decide
  have hdescent : baseEnd_703349 < baseStart_703349 := by decide
  rcases family_descends (prefixWord ++ tailWord_703349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703422 : List Nat := [4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_703422 : Nat := 118140960795 + 703422 * 2 ^ 59
def prefixEnd_703422 : Nat := 4983230072969 + 3 ^ 40 * 703422 * 2
def baseEnd_703422 : Nat := 107020322650978397597045

theorem tailTrace_703422 : CollatzResearch.WordTrace tailWord_703422 prefixEnd_703422 107020322650978397597045 := by
  unfold tailWord_703422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206988507203712969785065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17103938705086469172187013 3206988507203712969785065)
  ·
    refine ⟨2405241380402784727338799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3206988507203712969785065 2405241380402784727338799)
    ·
      refine ⟨3607862070604177091008199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405241380402784727338799 3607862070604177091008199)
      ·
        refine ⟨5411793105906265636512299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607862070604177091008199 5411793105906265636512299)
        ·
          refine ⟨8117689658859398454768449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411793105906265636512299 8117689658859398454768449)
          ·
            refine ⟨6088267244144548841076337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8117689658859398454768449 6088267244144548841076337)
            ·
              refine ⟨4566200433108411630807253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088267244144548841076337 4566200433108411630807253)
              ·
                refine ⟨107020322650978397597045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4566200433108411630807253 107020322650978397597045)
                ·
                  rfl

theorem cell20_703422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_703422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703422 prefixEnd_703422 := by exact prefixLift 703422
  have htrace : WordTrace (prefixWord ++ tailWord_703422) baseStart_703422 baseEnd_703422 := by
    simpa [prefixWord, tailWord_703422, baseEnd_703422] using wordTrace_append hprefix tailTrace_703422
  have hstable : (prefixWord ++ tailWord_703422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703422).length < 2 ^ (prefixWord ++ tailWord_703422).sum := by decide
  have hdescent : baseEnd_703422 < baseStart_703422 := by decide
  rcases family_descends (prefixWord ++ tailWord_703422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703439 : List Nat := [1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_703439 : Nat := 118140960795 + 703439 * 2 ^ 59
def prefixEnd_703439 : Nat := 4983230072969 + 3 ^ 40 * 703439 * 2
def baseEnd_703439 : Nat := 107022909072052896408133

theorem tailTrace_703439 : CollatzResearch.WordTrace tailWord_703439 prefixEnd_703439 107022909072052896408133 := by
  unfold tailWord_703439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25656528098568115661649371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17104352065712077107766247 25656528098568115661649371)
  ·
    refine ⟨38484792147852173492474057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25656528098568115661649371 38484792147852173492474057)
    ·
      refine ⟨28863594110889130119355543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38484792147852173492474057 28863594110889130119355543)
      ·
        refine ⟨43295391166333695179033315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28863594110889130119355543 43295391166333695179033315)
        ·
          refine ⟨64943086749500542768549973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43295391166333695179033315 64943086749500542768549973)
          ·
            refine ⟨761051797845709485568945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 64943086749500542768549973 761051797845709485568945)
            ·
              refine ⟨570788848384282114176709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761051797845709485568945 570788848384282114176709)
              ·
                refine ⟨107022909072052896408133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570788848384282114176709 107022909072052896408133)
                ·
                  rfl

theorem cell20_703439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_703439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703439 prefixEnd_703439 := by exact prefixLift 703439
  have htrace : WordTrace (prefixWord ++ tailWord_703439) baseStart_703439 baseEnd_703439 := by
    simpa [prefixWord, tailWord_703439, baseEnd_703439] using wordTrace_append hprefix tailTrace_703439
  have hstable : (prefixWord ++ tailWord_703439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703439).length < 2 ^ (prefixWord ++ tailWord_703439).sum := by decide
  have hdescent : baseEnd_703439 < baseStart_703439 := by decide
  rcases family_descends (prefixWord ++ tailWord_703439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703449 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 2]
def baseStart_703449 : Nat := 118140960795 + 703449 * 2 ^ 59
def prefixEnd_703449 : Nat := 4983230072969 + 3 ^ 40 * 703449 * 2
def baseEnd_703449 : Nat := 321073291488643098891025

theorem tailTrace_703449 : CollatzResearch.WordTrace tailWord_703449 prefixEnd_703449 321073291488643098891025 := by
  unfold tailWord_703449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25656892828531887369513401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17104595219021258246342267 25656892828531887369513401)
  ·
    refine ⟨19242669621398915527135051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25656892828531887369513401 19242669621398915527135051)
    ·
      refine ⟨28864004432098373290702577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19242669621398915527135051 28864004432098373290702577)
      ·
        refine ⟨21648003324073779968026933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28864004432098373290702577 21648003324073779968026933)
        ·
          refine ⟨2029500311631916872002525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21648003324073779968026933 2029500311631916872002525)
          ·
            refine ⟨761062616861968827000947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2029500311631916872002525 761062616861968827000947)
            ·
              refine ⟨1141593925292953240501421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761062616861968827000947 1141593925292953240501421)
              ·
                refine ⟨428097721984857465188033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141593925292953240501421 428097721984857465188033)
                ·
                  refine ⟨321073291488643098891025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428097721984857465188033 321073291488643098891025)
                  ·
                    rfl

theorem cell20_703449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_703449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703449 prefixEnd_703449 := by exact prefixLift 703449
  have htrace : WordTrace (prefixWord ++ tailWord_703449) baseStart_703449 baseEnd_703449 := by
    simpa [prefixWord, tailWord_703449, baseEnd_703449] using wordTrace_append hprefix tailTrace_703449
  have hstable : (prefixWord ++ tailWord_703449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703449).length < 2 ^ (prefixWord ++ tailWord_703449).sum := by decide
  have hdescent : baseEnd_703449 < baseStart_703449 := by decide
  rcases family_descends (prefixWord ++ tailWord_703449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703476 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_703476 : Nat := 118140960795 + 703476 * 2 ^ 59
def prefixEnd_703476 : Nat := 4983230072969 + 3 ^ 40 * 703476 * 2
def baseEnd_703476 : Nat := 321085615024351004990915

theorem tailTrace_703476 : CollatzResearch.WordTrace tailWord_703476 prefixEnd_703476 321085615024351004990915 := by
  unfold tailWord_703476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828938799717035490373141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17105251732956047320497521 12828938799717035490373141)
  ·
    refine ⟨601356506236736038611241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12828938799717035490373141 601356506236736038611241)
    ·
      refine ⟨451017379677552028958431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 601356506236736038611241 451017379677552028958431)
      ·
        refine ⟨676526069516328043437647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451017379677552028958431 676526069516328043437647)
        ·
          refine ⟨1014789104274492065156471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676526069516328043437647 1014789104274492065156471)
          ·
            refine ⟨1522183656411738097734707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014789104274492065156471 1522183656411738097734707)
            ·
              refine ⟨2283275484617607146602061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522183656411738097734707 2283275484617607146602061)
              ·
                refine ⟨856228306731602679975773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2283275484617607146602061 856228306731602679975773)
                ·
                  refine ⟨321085615024351004990915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856228306731602679975773 321085615024351004990915)
                  ·
                    rfl

theorem cell20_703476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_703476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703476 prefixEnd_703476 := by exact prefixLift 703476
  have htrace : WordTrace (prefixWord ++ tailWord_703476) baseStart_703476 baseEnd_703476 := by
    simpa [prefixWord, tailWord_703476, baseEnd_703476] using wordTrace_append hprefix tailTrace_703476
  have hstable : (prefixWord ++ tailWord_703476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703476).length < 2 ^ (prefixWord ++ tailWord_703476).sum := by decide
  have hdescent : baseEnd_703476 < baseStart_703476 := by decide
  rcases family_descends (prefixWord ++ tailWord_703476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703484 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_703484 : Nat := 118140960795 + 703484 * 2 ^ 59
def prefixEnd_703484 : Nat := 4983230072969 + 3 ^ 40 * 703484 * 2
def baseEnd_703484 : Nat := 321089266442338532724215

theorem tailTrace_703484 : CollatzResearch.WordTrace tailWord_703484 prefixEnd_703484 321089266442338532724215 := by
  unfold tailWord_703484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829084691702544173518753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17105446255603392231358337 12829084691702544173518753)
  ·
    refine ⟨9621813518776908130139065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12829084691702544173518753 9621813518776908130139065)
    ·
      refine ⟨7216360139082681097604299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9621813518776908130139065 7216360139082681097604299)
      ·
        refine ⟨10824540208624021646406449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7216360139082681097604299 10824540208624021646406449)
        ·
          refine ⟨8118405156468016234804837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824540208624021646406449 8118405156468016234804837)
          ·
            refine ⟨1522200966837753044025907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8118405156468016234804837 1522200966837753044025907)
            ·
              refine ⟨2283301450256629566038861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522200966837753044025907 2283301450256629566038861)
              ·
                refine ⟨856238043846236087264573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2283301450256629566038861 856238043846236087264573)
                ·
                  refine ⟨321089266442338532724215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856238043846236087264573 321089266442338532724215)
                  ·
                    rfl

theorem cell20_703484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_703484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703484 prefixEnd_703484 := by exact prefixLift 703484
  have htrace : WordTrace (prefixWord ++ tailWord_703484) baseStart_703484 baseEnd_703484 := by
    simpa [prefixWord, tailWord_703484, baseEnd_703484] using wordTrace_append hprefix tailTrace_703484
  have hstable : (prefixWord ++ tailWord_703484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703484).length < 2 ^ (prefixWord ++ tailWord_703484).sum := by decide
  have hdescent : baseEnd_703484 < baseStart_703484 := by decide
  rcases family_descends (prefixWord ++ tailWord_703484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703498 : List Nat := [3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_703498 : Nat := 118140960795 + 703498 * 2 ^ 59
def prefixEnd_703498 : Nat := 4983230072969 + 3 ^ 40 * 703498 * 2
def baseEnd_703498 : Nat := 107031885474605568752497

theorem tailTrace_703498 : CollatzResearch.WordTrace tailWord_703498 prefixEnd_703498 107031885474605568752497 := by
  unfold tailWord_703498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414670001338592184511787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17105786670236245825364765 6414670001338592184511787)
  ·
    refine ⟨9622005002007888276767681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414670001338592184511787 9622005002007888276767681)
    ·
      refine ⟨7216503751505916207575761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9622005002007888276767681 7216503751505916207575761)
      ·
        refine ⟨5412377813629437155681821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7216503751505916207575761 5412377813629437155681821)
        ·
          refine ⟨2029641680111038933380683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5412377813629437155681821 2029641680111038933380683)
          ·
            refine ⟨3044462520166558400071025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029641680111038933380683 3044462520166558400071025)
            ·
              refine ⟨2283346890124918800053269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044462520166558400071025 2283346890124918800053269)
              ·
                refine ⟨107031885474605568752497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2283346890124918800053269 107031885474605568752497)
                ·
                  rfl

theorem cell20_703498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_703498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703498 prefixEnd_703498 := by exact prefixLift 703498
  have htrace : WordTrace (prefixWord ++ tailWord_703498) baseStart_703498 baseEnd_703498 := by
    simpa [prefixWord, tailWord_703498, baseEnd_703498] using wordTrace_append hprefix tailTrace_703498
  have hstable : (prefixWord ++ tailWord_703498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703498).length < 2 ^ (prefixWord ++ tailWord_703498).sum := by decide
  have hdescent : baseEnd_703498 < baseStart_703498 := by decide
  rcases family_descends (prefixWord ++ tailWord_703498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703519 : List Nat := [1, 1, 2, 4, 1, 11]
def baseStart_703519 : Nat := 118140960795 + 703519 * 2 ^ 59
def prefixEnd_703519 : Nat := 4983230072969 + 3 ^ 40 * 703519 * 2
def baseEnd_703519 : Nat := 11892786718371628391015

theorem tailTrace_703519 : CollatzResearch.WordTrace tailWord_703519 prefixEnd_703519 11892786718371628391015 := by
  unfold tailWord_703519
  simp only [CollatzResearch.WordTrace]
  refine ⟨25659445938278289324561611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17106297292185526216374407 25659445938278289324561611)
  ·
    refine ⟨38489168907417433986842417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25659445938278289324561611 38489168907417433986842417)
    ·
      refine ⟨28866876680563075490131813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38489168907417433986842417 28866876680563075490131813)
      ·
        refine ⟨5412539377605576654399715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28866876680563075490131813 5412539377605576654399715)
        ·
          refine ⟨8118809066408364981599573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412539377605576654399715 8118809066408364981599573)
          ·
            refine ⟨11892786718371628391015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8118809066408364981599573 11892786718371628391015)
            ·
              rfl

theorem cell20_703519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 11].length) (baseStart_703519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703519 prefixEnd_703519 := by exact prefixLift 703519
  have htrace : WordTrace (prefixWord ++ tailWord_703519) baseStart_703519 baseEnd_703519 := by
    simpa [prefixWord, tailWord_703519, baseEnd_703519] using wordTrace_append hprefix tailTrace_703519
  have hstable : (prefixWord ++ tailWord_703519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703519).length < 2 ^ (prefixWord ++ tailWord_703519).sum := by decide
  have hdescent : baseEnd_703519 < baseStart_703519 := by decide
  rcases family_descends (prefixWord ++ tailWord_703519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703522 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_703522 : Nat := 118140960795 + 703522 * 2 ^ 59
def prefixEnd_703522 : Nat := 4983230072969 + 3 ^ 40 * 703522 * 2
def baseEnd_703522 : Nat := 321106610677779289457393

theorem tailTrace_703522 : CollatzResearch.WordTrace tailWord_703522 prefixEnd_703522 321106610677779289457393 := by
  unfold tailWord_703522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414888839316855209230205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17106370238178280557947213 6414888839316855209230205)
  ·
    refine ⟨2405583314743820703461327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6414888839316855209230205 2405583314743820703461327)
    ·
      refine ⟨3608374972115731055191991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405583314743820703461327 3608374972115731055191991)
      ·
        refine ⟨5412562458173596582787987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608374972115731055191991 5412562458173596582787987)
        ·
          refine ⟨8118843687260394874181981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412562458173596582787987 8118843687260394874181981)
          ·
            refine ⟨3044566382722648077818243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8118843687260394874181981 3044566382722648077818243)
            ·
              refine ⟨4566849574083972116727365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044566382722648077818243 4566849574083972116727365)
              ·
                refine ⟨856284295140744771886381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4566849574083972116727365 856284295140744771886381)
                ·
                  refine ⟨321106610677779289457393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856284295140744771886381 321106610677779289457393)
                  ·
                    rfl

theorem cell20_703522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_703522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703522 prefixEnd_703522 := by exact prefixLift 703522
  have htrace : WordTrace (prefixWord ++ tailWord_703522) baseStart_703522 baseEnd_703522 := by
    simpa [prefixWord, tailWord_703522, baseEnd_703522] using wordTrace_append hprefix tailTrace_703522
  have hstable : (prefixWord ++ tailWord_703522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703522).length < 2 ^ (prefixWord ++ tailWord_703522).sum := by decide
  have hdescent : baseEnd_703522 < baseStart_703522 := by decide
  rcases family_descends (prefixWord ++ tailWord_703522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703557 : List Nat := [1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_703557 : Nat := 118140960795 + 703557 * 2 ^ 59
def prefixEnd_703557 : Nat := 4983230072969 + 3 ^ 40 * 703557 * 2
def baseEnd_703557 : Nat := 107040861877158241096861

theorem tailTrace_703557 : CollatzResearch.WordTrace tailWord_703557 prefixEnd_703557 107040861877158241096861 := by
  unfold tailWord_703557
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660831912140621814444925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17107221274760414542963283 25660831912140621814444925)
  ·
    refine ⟨9622811967052733180416847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25660831912140621814444925 9622811967052733180416847)
    ·
      refine ⟨14434217950579099770625271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9622811967052733180416847 14434217950579099770625271)
      ·
        refine ⟨21651326925868649655937907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14434217950579099770625271 21651326925868649655937907)
        ·
          refine ⟨32476990388802974483906861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21651326925868649655937907 32476990388802974483906861)
          ·
            refine ⟨12178871395801115431465073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32476990388802974483906861 12178871395801115431465073)
            ·
              refine ⟨9134153546850836573598805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12178871395801115431465073 9134153546850836573598805)
              ·
                refine ⟨107040861877158241096861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9134153546850836573598805 107040861877158241096861)
                ·
                  rfl

theorem cell20_703557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_703557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703557 prefixEnd_703557 := by exact prefixLift 703557
  have htrace : WordTrace (prefixWord ++ tailWord_703557) baseStart_703557 baseEnd_703557 := by
    simpa [prefixWord, tailWord_703557, baseEnd_703557] using wordTrace_append hprefix tailTrace_703557
  have hstable : (prefixWord ++ tailWord_703557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703557).length < 2 ^ (prefixWord ++ tailWord_703557).sum := by decide
  have hdescent : baseEnd_703557 < baseStart_703557 := by decide
  rcases family_descends (prefixWord ++ tailWord_703557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703614 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_703614 : Nat := 118140960795 + 703614 * 2 ^ 59
def prefixEnd_703614 : Nat := 4983230072969 + 3 ^ 40 * 703614 * 2
def baseEnd_703614 : Nat := 321148601984635858390351

theorem tailTrace_703614 : CollatzResearch.WordTrace tailWord_703614 prefixEnd_703614 321148601984635858390351 := by
  unfold tailWord_703614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207863859116765068658737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17108607248622747032846597 3207863859116765068658737)
  ·
    refine ⟨2405897894337573801494053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3207863859116765068658737 2405897894337573801494053)
    ·
      refine ⟨451105855188295087780135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2405897894337573801494053 451105855188295087780135)
      ·
        refine ⟨676658782782442631670203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451105855188295087780135 676658782782442631670203)
        ·
          refine ⟨1014988174173663947505305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676658782782442631670203 1014988174173663947505305)
          ·
            refine ⟨761241130630247960628979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014988174173663947505305 761241130630247960628979)
            ·
              refine ⟨1141861695945371940943469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761241130630247960628979 1141861695945371940943469)
              ·
                refine ⟨428198135979514477853801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141861695945371940943469 428198135979514477853801)
                ·
                  refine ⟨321148601984635858390351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428198135979514477853801 321148601984635858390351)
                  ·
                    rfl

theorem cell20_703614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_703614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703614 prefixEnd_703614 := by exact prefixLift 703614
  have htrace : WordTrace (prefixWord ++ tailWord_703614) baseStart_703614 baseEnd_703614 := by
    simpa [prefixWord, tailWord_703614, baseEnd_703614] using wordTrace_append hprefix tailTrace_703614
  have hstable : (prefixWord ++ tailWord_703614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703614).length < 2 ^ (prefixWord ++ tailWord_703614).sum := by decide
  have hdescent : baseEnd_703614 < baseStart_703614 := by decide
  rcases family_descends (prefixWord ++ tailWord_703614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703639 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 2]
def baseStart_703639 : Nat := 118140960795 + 703639 * 2 ^ 59
def prefixEnd_703639 : Nat := 4983230072969 + 3 ^ 40 * 703639 * 2
def baseEnd_703639 : Nat := 321160012665846882556915

theorem tailTrace_703639 : CollatzResearch.WordTrace tailWord_703639 prefixEnd_703639 321160012665846882556915 := by
  unfold tailWord_703639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663822697843549818929971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17109215131895699879286647 25663822697843549818929971)
  ·
    refine ⟨38495734046765324728394957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25663822697843549818929971 38495734046765324728394957)
    ·
      refine ⟨14435900267536996773148109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38495734046765324728394957 14435900267536996773148109)
      ·
        refine ⟨5413462600326373789930541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14435900267536996773148109 5413462600326373789930541)
        ·
          refine ⟨2030048475122390171223953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5413462600326373789930541 2030048475122390171223953)
          ·
            refine ⟨1522536356341792628417965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030048475122390171223953 1522536356341792628417965)
            ·
              refine ⟨570951133628172235656737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1522536356341792628417965 570951133628172235656737)
              ·
                refine ⟨428213350221129176742553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570951133628172235656737 428213350221129176742553)
                ·
                  refine ⟨321160012665846882556915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428213350221129176742553 321160012665846882556915)
                  ·
                    rfl

theorem cell20_703639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2].length) (baseStart_703639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703639 prefixEnd_703639 := by exact prefixLift 703639
  have htrace : WordTrace (prefixWord ++ tailWord_703639) baseStart_703639 baseEnd_703639 := by
    simpa [prefixWord, tailWord_703639, baseEnd_703639] using wordTrace_append hprefix tailTrace_703639
  have hstable : (prefixWord ++ tailWord_703639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703639).length < 2 ^ (prefixWord ++ tailWord_703639).sum := by decide
  have hdescent : baseEnd_703639 < baseStart_703639 := by decide
  rcases family_descends (prefixWord ++ tailWord_703639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703653 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 3]
def baseStart_703653 : Nat := 118140960795 + 703653 * 2 ^ 59
def prefixEnd_703653 : Nat := 4983230072969 + 3 ^ 40 * 703653 * 2
def baseEnd_703653 : Nat := 321166402647325056090191

theorem tailTrace_703653 : CollatzResearch.WordTrace tailWord_703653 prefixEnd_703653 321166402647325056090191 := by
  unfold tailWord_703653
  simp only [CollatzResearch.WordTrace]
  refine ⟨25664333319792830209939613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17109555546528553473293075 25664333319792830209939613)
  ·
    refine ⟨9624124994922311328727355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25664333319792830209939613 9624124994922311328727355)
    ·
      refine ⟨14436187492383466993091033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9624124994922311328727355 14436187492383466993091033)
      ·
        refine ⟨10827140619287600244818275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14436187492383466993091033 10827140619287600244818275)
        ·
          refine ⟨16240710928931400367227413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10827140619287600244818275 16240710928931400367227413)
          ·
            refine ⟨761283324793659392213785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16240710928931400367227413 761283324793659392213785)
            ·
              refine ⟨570962493595244544160339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761283324793659392213785 570962493595244544160339)
              ·
                refine ⟨856443740392866816240509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570962493595244544160339 856443740392866816240509)
                ·
                  refine ⟨321166402647325056090191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856443740392866816240509 321166402647325056090191)
                  ·
                    rfl

theorem cell20_703653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_703653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703653 prefixEnd_703653 := by exact prefixLift 703653
  have htrace : WordTrace (prefixWord ++ tailWord_703653) baseStart_703653 baseEnd_703653 := by
    simpa [prefixWord, tailWord_703653, baseEnd_703653] using wordTrace_append hprefix tailTrace_703653
  have hstable : (prefixWord ++ tailWord_703653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703653).length < 2 ^ (prefixWord ++ tailWord_703653).sum := by decide
  have hdescent : baseEnd_703653 < baseStart_703653 := by decide
  rcases family_descends (prefixWord ++ tailWord_703653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703671 : List Nat := [1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_703671 : Nat := 118140960795 + 703671 * 2 ^ 59
def prefixEnd_703671 : Nat := 4983230072969 + 3 ^ 40 * 703671 * 2
def baseEnd_703671 : Nat := 107058206112598997830039

theorem tailTrace_703671 : CollatzResearch.WordTrace tailWord_703671 prefixEnd_703671 107058206112598997830039 := by
  unfold tailWord_703671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25664989833727619284094867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17109993222485079522729911 25664989833727619284094867)
  ·
    refine ⟨38497484750591428926142301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25664989833727619284094867 38497484750591428926142301)
    ·
      refine ⟨14436556781471785847303363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38497484750591428926142301 14436556781471785847303363)
      ·
        refine ⟨21654835172207678770955045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14436556781471785847303363 21654835172207678770955045)
        ·
          refine ⟨4060281594788939769554071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21654835172207678770955045 4060281594788939769554071)
          ·
            refine ⟨6090422392183409654331107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060281594788939769554071 6090422392183409654331107)
            ·
              refine ⟨9135633588275114481496661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090422392183409654331107 9135633588275114481496661)
              ·
                refine ⟨107058206112598997830039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9135633588275114481496661 107058206112598997830039)
                ·
                  rfl

theorem cell20_703671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_703671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703671 prefixEnd_703671 := by exact prefixLift 703671
  have htrace : WordTrace (prefixWord ++ tailWord_703671) baseStart_703671 baseEnd_703671 := by
    simpa [prefixWord, tailWord_703671, baseEnd_703671] using wordTrace_append hprefix tailTrace_703671
  have hstable : (prefixWord ++ tailWord_703671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703671).length < 2 ^ (prefixWord ++ tailWord_703671).sum := by decide
  have hdescent : baseEnd_703671 < baseStart_703671 := by decide
  rcases family_descends (prefixWord ++ tailWord_703671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703694 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_703694 : Nat := 118140960795 + 703694 * 2 ^ 59
def prefixEnd_703694 : Nat := 4983230072969 + 3 ^ 40 * 703694 * 2
def baseEnd_703694 : Nat := 321185116164511135723357

theorem tailTrace_703694 : CollatzResearch.WordTrace tailWord_703694 prefixEnd_703694 321185116164511135723357 := by
  unfold tailWord_703694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208228589080536776522767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17110552475096196141454757 3208228589080536776522767)
  ·
    refine ⟨4812342883620805164784151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3208228589080536776522767 4812342883620805164784151)
    ·
      refine ⟨7218514325431207747176227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4812342883620805164784151 7218514325431207747176227)
      ·
        refine ⟨10827771488146811620764341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218514325431207747176227 10827771488146811620764341)
        ·
          refine ⟨1015103577013763589446657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10827771488146811620764341 1015103577013763589446657)
          ·
            refine ⟨761327682760322692084993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015103577013763589446657 761327682760322692084993)
            ·
              refine ⟨570995762070242019063745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761327682760322692084993 570995762070242019063745)
              ·
                refine ⟨428246821552681514297809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570995762070242019063745 428246821552681514297809)
                ·
                  refine ⟨321185116164511135723357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428246821552681514297809 321185116164511135723357)
                  ·
                    rfl

theorem cell20_703694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_703694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703694 prefixEnd_703694 := by exact prefixLift 703694
  have htrace : WordTrace (prefixWord ++ tailWord_703694) baseStart_703694 baseEnd_703694 := by
    simpa [prefixWord, tailWord_703694, baseEnd_703694] using wordTrace_append hprefix tailTrace_703694
  have hstable : (prefixWord ++ tailWord_703694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703694).length < 2 ^ (prefixWord ++ tailWord_703694).sum := by decide
  have hdescent : baseEnd_703694 < baseStart_703694 := by decide
  rcases family_descends (prefixWord ++ tailWord_703694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703698 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_703698 : Nat := 118140960795 + 703698 * 2 ^ 59
def prefixEnd_703698 : Nat := 4983230072969 + 3 ^ 40 * 703698 * 2
def baseEnd_703698 : Nat := 321186941873504899590007

theorem tailTrace_703698 : CollatzResearch.WordTrace tailWord_703698 prefixEnd_703698 321186941873504899590007 := by
  unfold tailWord_703698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416493651157450723831937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17110649736419868596885165 6416493651157450723831937)
  ·
    refine ⟨4812370238368088042873953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6416493651157450723831937 4812370238368088042873953)
    ·
      refine ⟨3609277678776066032155465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4812370238368088042873953 3609277678776066032155465)
      ·
        refine ⟨2706958259082049524116599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609277678776066032155465 2706958259082049524116599)
        ·
          refine ⟨4060437388623074286174899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706958259082049524116599 4060437388623074286174899)
          ·
            refine ⟨6090656082934611429262349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060437388623074286174899 6090656082934611429262349)
            ·
              refine ⟨2283996031100479285973381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6090656082934611429262349 2283996031100479285973381)
              ·
                refine ⟨428249255831339866120009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2283996031100479285973381 428249255831339866120009)
                ·
                  refine ⟨321186941873504899590007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428249255831339866120009 321186941873504899590007)
                  ·
                    rfl

theorem cell20_703698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_703698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703698 prefixEnd_703698 := by exact prefixLift 703698
  have htrace : WordTrace (prefixWord ++ tailWord_703698) baseStart_703698 baseEnd_703698 := by
    simpa [prefixWord, tailWord_703698, baseEnd_703698] using wordTrace_append hprefix tailTrace_703698
  have hstable : (prefixWord ++ tailWord_703698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703698).length < 2 ^ (prefixWord ++ tailWord_703698).sum := by decide
  have hdescent : baseEnd_703698 < baseStart_703698 := by decide
  rcases family_descends (prefixWord ++ tailWord_703698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703746 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_703746 : Nat := 118140960795 + 703746 * 2 ^ 59
def prefixEnd_703746 : Nat := 4983230072969 + 3 ^ 40 * 703746 * 2
def baseEnd_703746 : Nat := 321208850381430065989811

theorem tailTrace_703746 : CollatzResearch.WordTrace tailWord_703746 prefixEnd_703746 321208850381430065989811 := by
  unfold tailWord_703746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416931327113976773268773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17111816872303938062050061 6416931327113976773268773)
  ·
    refine ⟨1203174623833870644987895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6416931327113976773268773 1203174623833870644987895)
    ·
      refine ⟨1804761935750805967481843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203174623833870644987895 1804761935750805967481843)
      ·
        refine ⟨2707142903626208951222765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804761935750805967481843 2707142903626208951222765)
        ·
          refine ⟨1015178588859828356708537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2707142903626208951222765 1015178588859828356708537)
          ·
            refine ⟨761383941644871267531403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015178588859828356708537 761383941644871267531403)
            ·
              refine ⟨1142075912467306901297105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761383941644871267531403 1142075912467306901297105)
              ·
                refine ⟨856556934350480175972829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142075912467306901297105 856556934350480175972829)
                ·
                  refine ⟨321208850381430065989811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856556934350480175972829 321208850381430065989811)
                  ·
                    rfl

theorem cell20_703746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_703746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703746 prefixEnd_703746 := by exact prefixLift 703746
  have htrace : WordTrace (prefixWord ++ tailWord_703746) baseStart_703746 baseEnd_703746 := by
    simpa [prefixWord, tailWord_703746, baseEnd_703746] using wordTrace_append hprefix tailTrace_703746
  have hstable : (prefixWord ++ tailWord_703746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703746).length < 2 ^ (prefixWord ++ tailWord_703746).sum := by decide
  have hdescent : baseEnd_703746 < baseStart_703746 := by decide
  rcases family_descends (prefixWord ++ tailWord_703746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703747 : List Nat := [1, 1, 1, 3, 2, 5, 7]
def baseStart_703747 : Nat := 118140960795 + 703747 * 2 ^ 59
def prefixEnd_703747 : Nat := 4983230072969 + 3 ^ 40 * 703747 * 2
def baseEnd_703747 : Nat := 35689922978742056328497

theorem tailTrace_703747 : CollatzResearch.WordTrace tailWord_703747 prefixEnd_703747 35689922978742056328497 := by
  unfold tailWord_703747
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667761781452284263861495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17111841187634856175907663 25667761781452284263861495)
  ·
    refine ⟨38501642672178426395792243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25667761781452284263861495 38501642672178426395792243)
    ·
      refine ⟨57752464008267639593688365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38501642672178426395792243 57752464008267639593688365)
      ·
        refine ⟨21657174003100364847633137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57752464008267639593688365 21657174003100364847633137)
        ·
          refine ⟨16242880502325273635724853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21657174003100364847633137 16242880502325273635724853)
          ·
            refine ⟨1522770047092994403349205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16242880502325273635724853 1522770047092994403349205)
            ·
              refine ⟨35689922978742056328497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1522770047092994403349205 35689922978742056328497)
              ·
                rfl

theorem cell20_703747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_703747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703747 prefixEnd_703747 := by exact prefixLift 703747
  have htrace : WordTrace (prefixWord ++ tailWord_703747) baseStart_703747 baseEnd_703747 := by
    simpa [prefixWord, tailWord_703747, baseEnd_703747] using wordTrace_append hprefix tailTrace_703747
  have hstable : (prefixWord ++ tailWord_703747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703747).length < 2 ^ (prefixWord ++ tailWord_703747).sum := by decide
  have hdescent : baseEnd_703747 < baseStart_703747 := by decide
  rcases family_descends (prefixWord ++ tailWord_703747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703781 : List Nat := [1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_703781 : Nat := 118140960795 + 703781 * 2 ^ 59
def prefixEnd_703781 : Nat := 4983230072969 + 3 ^ 40 * 703781 * 2
def baseEnd_703781 : Nat := 107074941778375166607667

theorem tailTrace_703781 : CollatzResearch.WordTrace tailWord_703781 prefixEnd_703781 107074941778375166607667 := by
  unfold tailWord_703781
  simp only [CollatzResearch.WordTrace]
  refine ⟨25669001863329108070599197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17112667908886072047066131 25669001863329108070599197)
  ·
    refine ⟨9625875698748415526474699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25669001863329108070599197 9625875698748415526474699)
    ·
      refine ⟨14438813548122623289712049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9625875698748415526474699 14438813548122623289712049)
      ·
        refine ⟨10829110161091967467284037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14438813548122623289712049 10829110161091967467284037)
        ·
          refine ⟨2030458155204743900115757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10829110161091967467284037 2030458155204743900115757)
          ·
            refine ⟨761421808201778962543409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2030458155204743900115757 761421808201778962543409)
            ·
              refine ⟨571066356151334221907557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761421808201778962543409 571066356151334221907557)
              ·
                refine ⟨107074941778375166607667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571066356151334221907557 107074941778375166607667)
                ·
                  rfl

theorem cell20_703781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_703781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703781 prefixEnd_703781 := by exact prefixLift 703781
  have htrace : WordTrace (prefixWord ++ tailWord_703781) baseStart_703781 baseEnd_703781 := by
    simpa [prefixWord, tailWord_703781, baseEnd_703781] using wordTrace_append hprefix tailTrace_703781
  have hstable : (prefixWord ++ tailWord_703781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703781).length < 2 ^ (prefixWord ++ tailWord_703781).sum := by decide
  have hdescent : baseEnd_703781 < baseStart_703781 := by decide
  rcases family_descends (prefixWord ++ tailWord_703781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703792 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_703792 : Nat := 118140960795 + 703792 * 2 ^ 59
def prefixEnd_703792 : Nat := 4983230072969 + 3 ^ 40 * 703792 * 2
def baseEnd_703792 : Nat := 321229846034858350456289

theorem tailTrace_703792 : CollatzResearch.WordTrace tailWord_703792 prefixEnd_703792 321229846034858350456289 := by
  unfold tailWord_703792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834701533144628474624815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17112935377526171299499753 12834701533144628474624815)
  ·
    refine ⟨19252052299716942711937223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12834701533144628474624815 19252052299716942711937223)
    ·
      refine ⟨28878078449575414067905835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19252052299716942711937223 28878078449575414067905835)
      ·
        refine ⟨43317117674363121101858753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28878078449575414067905835 43317117674363121101858753)
        ·
          refine ⟨32487838255772340826394065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43317117674363121101858753 32487838255772340826394065)
          ·
            refine ⟨24365878691829255619795549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32487838255772340826394065 24365878691829255619795549)
            ·
              refine ⟨9137204509435970857423331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24365878691829255619795549 9137204509435970857423331)
              ·
                refine ⟨13705806764153956286134997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137204509435970857423331 13705806764153956286134997)
                ·
                  refine ⟨321229846034858350456289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13705806764153956286134997 321229846034858350456289)
                  ·
                    rfl

theorem cell20_703792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_703792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703792 prefixEnd_703792 := by exact prefixLift 703792
  have htrace : WordTrace (prefixWord ++ tailWord_703792) baseStart_703792 baseEnd_703792 := by
    simpa [prefixWord, tailWord_703792, baseEnd_703792] using wordTrace_append hprefix tailTrace_703792
  have hstable : (prefixWord ++ tailWord_703792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703792).length < 2 ^ (prefixWord ++ tailWord_703792).sum := by decide
  have hdescent : baseEnd_703792 < baseStart_703792 := by decide
  rcases family_descends (prefixWord ++ tailWord_703792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703798 : List Nat := [5, 1, 2, 3, 1, 2, 6]
def baseStart_703798 : Nat := 118140960795 + 703798 * 2 ^ 59
def prefixEnd_703798 : Nat := 4983230072969 + 3 ^ 40 * 703798 * 2
def baseEnd_703798 : Nat := 35692509399816555139585

theorem tailTrace_703798 : CollatzResearch.WordTrace tailWord_703798 prefixEnd_703798 35692509399816555139585 := by
  unfold tailWord_703798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604351369016719998373003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17113081269511679982645365 1604351369016719998373003)
  ·
    refine ⟨2406527053525079997559505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604351369016719998373003 2406527053525079997559505)
    ·
      refine ⟨1804895290143809998169629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2406527053525079997559505 1804895290143809998169629)
      ·
        refine ⟨676835733803928749313611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1804895290143809998169629 676835733803928749313611)
        ·
          refine ⟨1015253600705893123970417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676835733803928749313611 1015253600705893123970417)
          ·
            refine ⟨761440200529419842977813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015253600705893123970417 761440200529419842977813)
            ·
              refine ⟨35692509399816555139585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761440200529419842977813 35692509399816555139585)
              ·
                rfl

theorem cell20_703798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_703798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703798 prefixEnd_703798 := by exact prefixLift 703798
  have htrace : WordTrace (prefixWord ++ tailWord_703798) baseStart_703798 baseEnd_703798 := by
    simpa [prefixWord, tailWord_703798, baseEnd_703798] using wordTrace_append hprefix tailTrace_703798
  have hstable : (prefixWord ++ tailWord_703798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703798).length < 2 ^ (prefixWord ++ tailWord_703798).sum := by decide
  have hdescent : baseEnd_703798 < baseStart_703798 := by decide
  rcases family_descends (prefixWord ++ tailWord_703798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703812 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_703812 : Nat := 118140960795 + 703812 * 2 ^ 59
def prefixEnd_703812 : Nat := 4983230072969 + 3 ^ 40 * 703812 * 2
def baseEnd_703812 : Nat := 321238974579827169789541

theorem tailTrace_703812 : CollatzResearch.WordTrace tailWord_703812 prefixEnd_703812 321238974579827169789541 := by
  unfold tailWord_703812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835066263108400182488845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17113421684144533576651793 12835066263108400182488845)
  ·
    refine ⟨4813149848665650068433317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12835066263108400182488845 4813149848665650068433317)
    ·
      refine ⟨902465596624809387831247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4813149848665650068433317 902465596624809387831247)
      ·
        refine ⟨1353698394937214081746871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902465596624809387831247 1353698394937214081746871)
        ·
          refine ⟨2030547592405821122620307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353698394937214081746871 2030547592405821122620307)
          ·
            refine ⟨3045821388608731683930461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030547592405821122620307 3045821388608731683930461)
            ·
              refine ⟨1142183020728274381473923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045821388608731683930461 1142183020728274381473923)
              ·
                refine ⟨1713274531092411572210885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142183020728274381473923 1713274531092411572210885)
                ·
                  refine ⟨321238974579827169789541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713274531092411572210885 321238974579827169789541)
                  ·
                    rfl

theorem cell20_703812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_703812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703812 prefixEnd_703812 := by exact prefixLift 703812
  have htrace : WordTrace (prefixWord ++ tailWord_703812) baseStart_703812 baseEnd_703812 := by
    simpa [prefixWord, tailWord_703812, baseEnd_703812] using wordTrace_append hprefix tailTrace_703812
  have hstable : (prefixWord ++ tailWord_703812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703812).length < 2 ^ (prefixWord ++ tailWord_703812).sum := by decide
  have hdescent : baseEnd_703812 < baseStart_703812 := by decide
  rcases family_descends (prefixWord ++ tailWord_703812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703861 : List Nat := [1, 3, 4, 1, 11]
def baseStart_703861 : Nat := 118140960795 + 703861 * 2 ^ 59
def prefixEnd_703861 : Nat := 4983230072969 + 3 ^ 40 * 703861 * 2
def baseEnd_703861 : Nat := 3966189376728404656247

theorem tailTrace_703861 : CollatzResearch.WordTrace tailWord_703861 prefixEnd_703861 3966189376728404656247 := by
  unfold tailWord_703861
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671919703039281733511437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17114613135359521155674291 25671919703039281733511437)
  ·
    refine ⟨9626969888639730650066789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25671919703039281733511437 9626969888639730650066789)
    ·
      refine ⟨1805056854119949496887523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9626969888639730650066789 1805056854119949496887523)
      ·
        refine ⟨2707585281179924245331285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805056854119949496887523 2707585281179924245331285)
        ·
          refine ⟨3966189376728404656247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2707585281179924245331285 3966189376728404656247)
          ·
            rfl

theorem cell20_703861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 11].length) (baseStart_703861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703861 prefixEnd_703861 := by exact prefixLift 703861
  have htrace : WordTrace (prefixWord ++ tailWord_703861) baseStart_703861 baseEnd_703861 := by
    simpa [prefixWord, tailWord_703861, baseEnd_703861] using wordTrace_append hprefix tailTrace_703861
  have hstable : (prefixWord ++ tailWord_703861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703861).length < 2 ^ (prefixWord ++ tailWord_703861).sum := by decide
  have hdescent : baseEnd_703861 < baseStart_703861 := by decide
  rcases family_descends (prefixWord ++ tailWord_703861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703874 : List Nat := [3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_703874 : Nat := 118140960795 + 703874 * 2 ^ 59
def prefixEnd_703874 : Nat := 4983230072969 + 3 ^ 40 * 703874 * 2
def baseEnd_703874 : Nat := 107089091023076836574207

theorem tailTrace_703874 : CollatzResearch.WordTrace tailWord_703874 prefixEnd_703874 107089091023076836574207 := by
  unfold tailWord_703874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418098462998046238433669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17114929234661456635823117 6418098462998046238433669)
  ·
    refine ⟨1203393461812133669706313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6418098462998046238433669 1203393461812133669706313)
    ·
      refine ⟨902545096359100252279735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203393461812133669706313 902545096359100252279735)
      ·
        refine ⟨1353817644538650378419603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902545096359100252279735 1353817644538650378419603)
        ·
          refine ⟨2030726466807975567629405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353817644538650378419603 2030726466807975567629405)
          ·
            refine ⟨761522425052990837861027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2030726466807975567629405 761522425052990837861027)
            ·
              refine ⟨1142283637579486256791541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761522425052990837861027 1142283637579486256791541)
              ·
                refine ⟨107089091023076836574207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142283637579486256791541 107089091023076836574207)
                ·
                  rfl

theorem cell20_703874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_703874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703874 prefixEnd_703874 := by exact prefixLift 703874
  have htrace : WordTrace (prefixWord ++ tailWord_703874) baseStart_703874 baseEnd_703874 := by
    simpa [prefixWord, tailWord_703874, baseEnd_703874] using wordTrace_append hprefix tailTrace_703874
  have hstable : (prefixWord ++ tailWord_703874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703874).length < 2 ^ (prefixWord ++ tailWord_703874).sum := by decide
  have hdescent : baseEnd_703874 < baseStart_703874 := by decide
  rcases family_descends (prefixWord ++ tailWord_703874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703975 : List Nat := [1, 1, 5, 2, 1, 2, 8]
def baseStart_703975 : Nat := 118140960795 + 703975 * 2 ^ 59
def prefixEnd_703975 : Nat := 4983230072969 + 3 ^ 40 * 703975 * 2
def baseEnd_703975 : Nat := 35701485802369227483949

theorem tailTrace_703975 : CollatzResearch.WordTrace tailWord_703975 prefixEnd_703975 35701485802369227483949 := by
  unfold tailWord_703975
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676077624626279203161379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17117385083084186135440919 25676077624626279203161379)
  ·
    refine ⟨38514116436939418804742069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25676077624626279203161379 38514116436939418804742069)
    ·
      refine ⟨3610698415963070512944569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38514116436939418804742069 3610698415963070512944569)
      ·
        refine ⟨2708023811972302884708427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3610698415963070512944569 2708023811972302884708427)
        ·
          refine ⟨4062035717958454327062641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708023811972302884708427 4062035717958454327062641)
          ·
            refine ⟨3046526788468840745296981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062035717958454327062641 3046526788468840745296981)
            ·
              refine ⟨35701485802369227483949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3046526788468840745296981 35701485802369227483949)
              ·
                rfl

theorem cell20_703975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_703975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703975 prefixEnd_703975 := by exact prefixLift 703975
  have htrace : WordTrace (prefixWord ++ tailWord_703975) baseStart_703975 baseEnd_703975 := by
    simpa [prefixWord, tailWord_703975, baseEnd_703975] using wordTrace_append hprefix tailTrace_703975
  have hstable : (prefixWord ++ tailWord_703975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703975).length < 2 ^ (prefixWord ++ tailWord_703975).sum := by decide
  have hdescent : baseEnd_703975 < baseStart_703975 := by decide
  rcases family_descends (prefixWord ++ tailWord_703975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703981 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 4]
def baseStart_703981 : Nat := 118140960795 + 703981 * 2 ^ 59
def prefixEnd_703981 : Nat := 4983230072969 + 3 ^ 40 * 703981 * 2
def baseEnd_703981 : Nat := 321316110784813693155517

theorem tailTrace_703981 : CollatzResearch.WordTrace tailWord_703981 prefixEnd_703981 321316110784813693155517 := by
  unfold tailWord_703981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676296462604542227879797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17117530975069694818586531 25676296462604542227879797)
  ·
    refine ⟨2407152793369175833863731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25676296462604542227879797 2407152793369175833863731)
    ·
      refine ⟨3610729190053763750795597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407152793369175833863731 3610729190053763750795597)
      ·
        refine ⟨1354023446270161406548349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3610729190053763750795597 1354023446270161406548349)
        ·
          refine ⟨507758792351310527455631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1354023446270161406548349 507758792351310527455631)
          ·
            refine ⟨761638188526965791183447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507758792351310527455631 761638188526965791183447)
            ·
              refine ⟨1142457282790448686775171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761638188526965791183447 1142457282790448686775171)
              ·
                refine ⟨1713685924185673030162757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142457282790448686775171 1713685924185673030162757)
                ·
                  refine ⟨321316110784813693155517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713685924185673030162757 321316110784813693155517)
                  ·
                    rfl

theorem cell20_703981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_703981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703981 prefixEnd_703981 := by exact prefixLift 703981
  have htrace : WordTrace (prefixWord ++ tailWord_703981) baseStart_703981 baseEnd_703981 := by
    simpa [prefixWord, tailWord_703981, baseEnd_703981] using wordTrace_append hprefix tailTrace_703981
  have hstable : (prefixWord ++ tailWord_703981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703981).length < 2 ^ (prefixWord ++ tailWord_703981).sum := by decide
  have hdescent : baseEnd_703981 < baseStart_703981 := by decide
  rcases family_descends (prefixWord ++ tailWord_703981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703985 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_703985 : Nat := 118140960795 + 703985 * 2 ^ 59
def prefixEnd_703985 : Nat := 4983230072969 + 3 ^ 40 * 703985 * 2
def baseEnd_703985 : Nat := 321317936493807457022167

theorem tailTrace_703985 : CollatzResearch.WordTrace tailWord_703985 prefixEnd_703985 321317936493807457022167 := by
  unfold tailWord_703985
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676442354590050911025409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17117628236393367274016939 25676442354590050911025409)
  ·
    refine ⟨19257331765942538183269057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25676442354590050911025409 19257331765942538183269057)
    ·
      refine ⟨14442998824456903637451793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19257331765942538183269057 14442998824456903637451793)
      ·
        refine ⟨10832249118342677728088845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14442998824456903637451793 10832249118342677728088845)
        ·
          refine ⟨4062093419378504148033317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10832249118342677728088845 4062093419378504148033317)
          ·
            refine ⟨761642516133469527756247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4062093419378504148033317 761642516133469527756247)
            ·
              refine ⟨1142463774200204291634371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761642516133469527756247 1142463774200204291634371)
              ·
                refine ⟨1713695661300306437451557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142463774200204291634371 1713695661300306437451557)
                ·
                  refine ⟨321317936493807457022167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713695661300306437451557 321317936493807457022167)
                  ·
                    rfl

theorem cell20_703985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_703985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_703985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_703985 prefixEnd_703985 := by exact prefixLift 703985
  have htrace : WordTrace (prefixWord ++ tailWord_703985) baseStart_703985 baseEnd_703985 := by
    simpa [prefixWord, tailWord_703985, baseEnd_703985] using wordTrace_append hprefix tailTrace_703985
  have hstable : (prefixWord ++ tailWord_703985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703985).length < 2 ^ (prefixWord ++ tailWord_703985).sum := by decide
  have hdescent : baseEnd_703985 < baseStart_703985 := by decide
  rcases family_descends (prefixWord ++ tailWord_703985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704051 : List Nat := [1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_704051 : Nat := 118140960795 + 704051 * 2 ^ 59
def prefixEnd_704051 : Nat := 4983230072969 + 3 ^ 40 * 704051 * 2
def baseEnd_704051 : Nat := 107116020230734853607299

theorem tailTrace_704051 : CollatzResearch.WordTrace tailWord_704051 prefixEnd_704051 107116020230734853607299 := by
  unfold tailWord_704051
  simp only [CollatzResearch.WordTrace]
  refine ⟨25678849572350944182928007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17119233048233962788618671 25678849572350944182928007)
  ·
    refine ⟨38518274358526416274392011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25678849572350944182928007 38518274358526416274392011)
    ·
      refine ⟨57777411537789624411588017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38518274358526416274392011 57777411537789624411588017)
      ·
        refine ⟨43333058653342218308691013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57777411537789624411588017 43333058653342218308691013)
        ·
          refine ⟨8124948497501665932879565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43333058653342218308691013 8124948497501665932879565)
          ·
            refine ⟨3046855686563124724829837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8124948497501665932879565 3046855686563124724829837)
            ·
              refine ⟨1142570882461171771811189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3046855686563124724829837 1142570882461171771811189)
              ·
                refine ⟨107116020230734853607299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142570882461171771811189 107116020230734853607299)
                ·
                  rfl

theorem cell20_704051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_704051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704051 prefixEnd_704051 := by exact prefixLift 704051
  have htrace : WordTrace (prefixWord ++ tailWord_704051) baseStart_704051 baseEnd_704051 := by
    simpa [prefixWord, tailWord_704051, baseEnd_704051] using wordTrace_append hprefix tailTrace_704051
  have hstable : (prefixWord ++ tailWord_704051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704051).length < 2 ^ (prefixWord ++ tailWord_704051).sum := by decide
  have hdescent : baseEnd_704051 < baseStart_704051 := by decide
  rcases family_descends (prefixWord ++ tailWord_704051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704061 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_704061 : Nat := 118140960795 + 704061 * 2 ^ 59
def prefixEnd_704061 : Nat := 4983230072969 + 3 ^ 40 * 704061 * 2
def baseEnd_704061 : Nat := 321352624964688970488523

theorem tailTrace_704061 : CollatzResearch.WordTrace tailWord_704061 prefixEnd_704061 321352624964688970488523 := by
  unfold tailWord_704061
  simp only [CollatzResearch.WordTrace]
  refine ⟨25679214302314715890792037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17119476201543143927194691 25679214302314715890792037)
  ·
    refine ⟨4814852681684009229523507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25679214302314715890792037 4814852681684009229523507)
    ·
      refine ⟨7222279022526013844285261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814852681684009229523507 7222279022526013844285261)
      ·
        refine ⟨2708354633447255191606973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7222279022526013844285261 2708354633447255191606973)
        ·
          refine ⟨1015632987542720696852615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2708354633447255191606973 1015632987542720696852615)
          ·
            refine ⟨1523449481314081045278923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015632987542720696852615 1523449481314081045278923)
            ·
              refine ⟨2285174221971121567918385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523449481314081045278923 2285174221971121567918385)
              ·
                refine ⟨1713880666478341175938789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285174221971121567918385 1713880666478341175938789)
                ·
                  refine ⟨321352624964688970488523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713880666478341175938789 321352624964688970488523)
                  ·
                    rfl

theorem cell20_704061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_704061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704061 prefixEnd_704061 := by exact prefixLift 704061
  have htrace : WordTrace (prefixWord ++ tailWord_704061) baseStart_704061 baseEnd_704061 := by
    simpa [prefixWord, tailWord_704061, baseEnd_704061] using wordTrace_append hprefix tailTrace_704061
  have hstable : (prefixWord ++ tailWord_704061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704061).length < 2 ^ (prefixWord ++ tailWord_704061).sum := by decide
  have hdescent : baseEnd_704061 < baseStart_704061 := by decide
  rcases family_descends (prefixWord ++ tailWord_704061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704092 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_704092 : Nat := 118140960795 + 704092 * 2 ^ 59
def prefixEnd_704092 : Nat := 4983230072969 + 3 ^ 40 * 704092 * 2
def baseEnd_704092 : Nat := 321366774209390640455063

theorem tailTrace_704092 : CollatzResearch.WordTrace tailWord_704092 prefixEnd_704092 321366774209390640455063 := by
  unfold tailWord_704092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840172482601204092585265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17120229976801605456780353 12840172482601204092585265)
  ·
    refine ⟨9630129361950903069438949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12840172482601204092585265 9630129361950903069438949)
    ·
      refine ⟨1805649255365794325519803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9630129361950903069438949 1805649255365794325519803)
      ·
        refine ⟨2708473883048691488279705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805649255365794325519803 2708473883048691488279705)
        ·
          refine ⟨2031355412286518616209779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708473883048691488279705 2031355412286518616209779)
          ·
            refine ⟨3047033118429777924314669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031355412286518616209779 3047033118429777924314669)
            ·
              refine ⟨1142637419411166721618001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3047033118429777924314669 1142637419411166721618001)
              ·
                refine ⟨856978064558375041213501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142637419411166721618001 856978064558375041213501)
                ·
                  refine ⟨321366774209390640455063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856978064558375041213501 321366774209390640455063)
                  ·
                    rfl

theorem cell20_704092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_704092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704092 prefixEnd_704092 := by exact prefixLift 704092
  have htrace : WordTrace (prefixWord ++ tailWord_704092) baseStart_704092 baseEnd_704092 := by
    simpa [prefixWord, tailWord_704092, baseEnd_704092] using wordTrace_append hprefix tailTrace_704092
  have hstable : (prefixWord ++ tailWord_704092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704092).length < 2 ^ (prefixWord ++ tailWord_704092).sum := by decide
  have hdescent : baseEnd_704092 < baseStart_704092 := by decide
  rcases family_descends (prefixWord ++ tailWord_704092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704099 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 2]
def baseStart_704099 : Nat := 118140960795 + 704099 * 2 ^ 59
def prefixEnd_704099 : Nat := 4983230072969 + 3 ^ 40 * 704099 * 2
def baseEnd_704099 : Nat := 321369969200129727221701

theorem tailTrace_704099 : CollatzResearch.WordTrace tailWord_704099 prefixEnd_704099 321369969200129727221701 := by
  unfold tailWord_704099
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680600276177048380675351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17120400184118032253783567 25680600276177048380675351)
  ·
    refine ⟨38520900414265572571013027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25680600276177048380675351 38520900414265572571013027)
    ·
      refine ⟨57781350621398358856519541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38520900414265572571013027 57781350621398358856519541)
      ·
        refine ⟨5417001620756096142798707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57781350621398358856519541 5417001620756096142798707)
        ·
          refine ⟨8125502431134144214198061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417001620756096142798707 8125502431134144214198061)
          ·
            refine ⟨3047063411675304080324273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8125502431134144214198061 3047063411675304080324273)
            ·
              refine ⟨2285297558756478060243205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047063411675304080324273 2285297558756478060243205)
              ·
                refine ⟨428493292266839636295601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2285297558756478060243205 428493292266839636295601)
                ·
                  refine ⟨321369969200129727221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428493292266839636295601 321369969200129727221701)
                  ·
                    rfl

theorem cell20_704099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2].length) (baseStart_704099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704099 prefixEnd_704099 := by exact prefixLift 704099
  have htrace : WordTrace (prefixWord ++ tailWord_704099) baseStart_704099 baseEnd_704099 := by
    simpa [prefixWord, tailWord_704099, baseEnd_704099] using wordTrace_append hprefix tailTrace_704099
  have hstable : (prefixWord ++ tailWord_704099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704099).length < 2 ^ (prefixWord ++ tailWord_704099).sum := by decide
  have hdescent : baseEnd_704099 < baseStart_704099 := by decide
  rcases family_descends (prefixWord ++ tailWord_704099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704109 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 3]
def baseStart_704109 : Nat := 118140960795 + 704109 * 2 ^ 59
def prefixEnd_704109 : Nat := 4983230072969 + 3 ^ 40 * 704109 * 2
def baseEnd_704109 : Nat := 321374533472614136888327

theorem tailTrace_704109 : CollatzResearch.WordTrace tailWord_704109 prefixEnd_704109 321374533472614136888327 := by
  unfold tailWord_704109
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680965006140820088539381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17120643337427213392359587 25680965006140820088539381)
  ·
    refine ⟨2407590469325701883300567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25680965006140820088539381 2407590469325701883300567)
    ·
      refine ⟨3611385703988552824950851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407590469325701883300567 3611385703988552824950851)
      ·
        refine ⟨5417078555982829237426277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611385703988552824950851 5417078555982829237426277)
        ·
          refine ⟨1015702229246780482017427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5417078555982829237426277 1015702229246780482017427)
          ·
            refine ⟨1523553343870170723026141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015702229246780482017427 1523553343870170723026141)
            ·
              refine ⟨571332503951314021134803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1523553343870170723026141 571332503951314021134803)
              ·
                refine ⟨856998755926971031702205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571332503951314021134803 856998755926971031702205)
                ·
                  refine ⟨321374533472614136888327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856998755926971031702205 321374533472614136888327)
                  ·
                    rfl

theorem cell20_704109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_704109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704109 prefixEnd_704109 := by exact prefixLift 704109
  have htrace : WordTrace (prefixWord ++ tailWord_704109) baseStart_704109 baseEnd_704109 := by
    simpa [prefixWord, tailWord_704109, baseEnd_704109] using wordTrace_append hprefix tailTrace_704109
  have hstable : (prefixWord ++ tailWord_704109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704109).length < 2 ^ (prefixWord ++ tailWord_704109).sum := by decide
  have hdescent : baseEnd_704109 < baseStart_704109 := by decide
  rcases family_descends (prefixWord ++ tailWord_704109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704137 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 2]
def baseStart_704137 : Nat := 118140960795 + 704137 * 2 ^ 59
def prefixEnd_704137 : Nat := 4983230072969 + 3 ^ 40 * 704137 * 2
def baseEnd_704137 : Nat := 321387313435570483954879

theorem tailTrace_704137 : CollatzResearch.WordTrace tailWord_704137 prefixEnd_704137 321387313435570483954879 := by
  unfold tailWord_704137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681986250039380870558665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17121324166692920580372443 25681986250039380870558665)
  ·
    refine ⟨19261489687529535652918999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25681986250039380870558665 19261489687529535652918999)
    ·
      refine ⟨28892234531294303479378499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19261489687529535652918999 28892234531294303479378499)
      ·
        refine ⟨43338351796941455219067749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28892234531294303479378499 43338351796941455219067749)
        ·
          refine ⟨8125940961926522853575203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43338351796941455219067749 8125940961926522853575203)
          ·
            refine ⟨12188911442889784280362805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125940961926522853575203 12188911442889784280362805)
            ·
              refine ⟨1142710447770917276284013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12188911442889784280362805 1142710447770917276284013)
              ·
                refine ⟨428516417914093978606505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142710447770917276284013 428516417914093978606505)
                ·
                  refine ⟨321387313435570483954879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428516417914093978606505 321387313435570483954879)
                  ·
                    rfl

theorem cell20_704137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_704137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704137 prefixEnd_704137 := by exact prefixLift 704137
  have htrace : WordTrace (prefixWord ++ tailWord_704137) baseStart_704137 baseEnd_704137 := by
    simpa [prefixWord, tailWord_704137, baseEnd_704137] using wordTrace_append hprefix tailTrace_704137
  have hstable : (prefixWord ++ tailWord_704137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704137).length < 2 ^ (prefixWord ++ tailWord_704137).sum := by decide
  have hdescent : baseEnd_704137 < baseStart_704137 := by decide
  rcases family_descends (prefixWord ++ tailWord_704137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704179 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_704179 : Nat := 118140960795 + 704179 * 2 ^ 59
def prefixEnd_704179 : Nat := 4983230072969 + 3 ^ 40 * 704179 * 2
def baseEnd_704179 : Nat := 321406483380005004554707

theorem tailTrace_704179 : CollatzResearch.WordTrace tailWord_704179 prefixEnd_704179 321406483380005004554707 := by
  unfold tailWord_704179
  simp only [CollatzResearch.WordTrace]
  refine ⟨25683518115887222043587591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17122345410591481362391727 25683518115887222043587591)
  ·
    refine ⟨38525277173830833065381387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25683518115887222043587591 38525277173830833065381387)
    ·
      refine ⟨57787915760746249598072081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38525277173830833065381387 57787915760746249598072081)
      ·
        refine ⟨43340936820559687198554061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57787915760746249598072081 43340936820559687198554061)
        ·
          refine ⟨16252851307709882699457773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43340936820559687198554061 16252851307709882699457773)
          ·
            refine ⟨6094819240391206012296665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16252851307709882699457773 6094819240391206012296665)
            ·
              refine ⟨4571114430293404509222499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6094819240391206012296665 4571114430293404509222499)
              ·
                refine ⟨6856671645440106763833749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571114430293404509222499 6856671645440106763833749)
                ·
                  refine ⟨321406483380005004554707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6856671645440106763833749 321406483380005004554707)
                  ·
                    rfl

theorem cell20_704179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_704179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704179 prefixEnd_704179 := by exact prefixLift 704179
  have htrace : WordTrace (prefixWord ++ tailWord_704179) baseStart_704179 baseEnd_704179 := by
    simpa [prefixWord, tailWord_704179, baseEnd_704179] using wordTrace_append hprefix tailTrace_704179
  have hstable : (prefixWord ++ tailWord_704179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704179).length < 2 ^ (prefixWord ++ tailWord_704179).sum := by decide
  have hdescent : baseEnd_704179 < baseStart_704179 := by decide
  rcases family_descends (prefixWord ++ tailWord_704179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704282 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_704282 : Nat := 118140960795 + 704282 * 2 ^ 59
def prefixEnd_704282 : Nat := 4983230072969 + 3 ^ 40 * 704282 * 2
def baseEnd_704282 : Nat := 321453495386594424120953

theorem tailTrace_704282 : CollatzResearch.WordTrace tailWord_704282 prefixEnd_704282 321453495386594424120953 := by
  unfold tailWord_704282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421818708628517658646775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17124849889676047089724733 6421818708628517658646775)
  ·
    refine ⟨9632728062942776487970163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6421818708628517658646775 9632728062942776487970163)
    ·
      refine ⟨14449092094414164731955245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632728062942776487970163 14449092094414164731955245)
      ·
        refine ⟨5418409535405311774483217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14449092094414164731955245 5418409535405311774483217)
        ·
          refine ⟨4063807151553983830862413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418409535405311774483217 4063807151553983830862413)
          ·
            refine ⟨1523927681832743936573405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4063807151553983830862413 1523927681832743936573405)
            ·
              refine ⟨571472880687278976215027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1523927681832743936573405 571472880687278976215027)
              ·
                refine ⟨857209321030918464322541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571472880687278976215027 857209321030918464322541)
                ·
                  refine ⟨321453495386594424120953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857209321030918464322541 321453495386594424120953)
                  ·
                    rfl

theorem cell20_704282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_704282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704282 prefixEnd_704282 := by exact prefixLift 704282
  have htrace : WordTrace (prefixWord ++ tailWord_704282) baseStart_704282 baseEnd_704282 := by
    simpa [prefixWord, tailWord_704282, baseEnd_704282] using wordTrace_append hprefix tailTrace_704282
  have hstable : (prefixWord ++ tailWord_704282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704282).length < 2 ^ (prefixWord ++ tailWord_704282).sum := by decide
  have hdescent : baseEnd_704282 < baseStart_704282 := by decide
  rcases family_descends (prefixWord ++ tailWord_704282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704296 : List Nat := [2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_704296 : Nat := 118140960795 + 704296 * 2 ^ 59
def prefixEnd_704296 : Nat := 4983230072969 + 3 ^ 40 * 704296 * 2
def baseEnd_704296 : Nat := 107153295122690865884743

theorem tailTrace_704296 : CollatzResearch.WordTrace tailWord_704296 prefixEnd_704296 107153295122690865884743 := by
  unfold tailWord_704296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843892728231675512798371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17125190304308900683731161 12843892728231675512798371)
  ·
    refine ⟨19265839092347513269197557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843892728231675512798371 19265839092347513269197557)
    ·
      refine ⟨1806172414907579368987271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19265839092347513269197557 1806172414907579368987271)
      ·
        refine ⟨2709258622361369053480907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806172414907579368987271 2709258622361369053480907)
        ·
          refine ⟨4063887933542053580221361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709258622361369053480907 4063887933542053580221361)
          ·
            refine ⟨3047915950156540185166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4063887933542053580221361 3047915950156540185166021)
            ·
              refine ⟨571484240654351284718629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3047915950156540185166021 571484240654351284718629)
              ·
                refine ⟨107153295122690865884743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571484240654351284718629 107153295122690865884743)
                ·
                  rfl

theorem cell20_704296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_704296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704296 prefixEnd_704296 := by exact prefixLift 704296
  have htrace : WordTrace (prefixWord ++ tailWord_704296) baseStart_704296 baseEnd_704296 := by
    simpa [prefixWord, tailWord_704296, baseEnd_704296] using wordTrace_append hprefix tailTrace_704296
  have hstable : (prefixWord ++ tailWord_704296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704296).length < 2 ^ (prefixWord ++ tailWord_704296).sum := by decide
  have hdescent : baseEnd_704296 < baseStart_704296 := by decide
  rcases family_descends (prefixWord ++ tailWord_704296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704302 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_704302 : Nat := 118140960795 + 704302 * 2 ^ 59
def prefixEnd_704302 : Nat := 4983230072969 + 3 ^ 40 * 704302 * 2
def baseEnd_704302 : Nat := 321462623931563243454205

theorem tailTrace_704302 : CollatzResearch.WordTrace tailWord_704302 prefixEnd_704302 321462623931563243454205 := by
  unfold tailWord_704302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211000536805201756289395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17125336196294409366876773 3211000536805201756289395)
  ·
    refine ⟨4816500805207802634434093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3211000536805201756289395 4816500805207802634434093)
    ·
      refine ⟨1806187801952925987912785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4816500805207802634434093 1806187801952925987912785)
      ·
        refine ⟨1354640851464694490934589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1806187801952925987912785 1354640851464694490934589)
        ·
          refine ⟨507990319299260434100471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1354640851464694490934589 507990319299260434100471)
          ·
            refine ⟨761985478948890651150707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507990319299260434100471 761985478948890651150707)
            ·
              refine ⟨1142978218423335976726061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761985478948890651150707 1142978218423335976726061)
              ·
                refine ⟨428616831908750991272273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142978218423335976726061 428616831908750991272273)
                ·
                  refine ⟨321462623931563243454205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428616831908750991272273 321462623931563243454205)
                  ·
                    rfl

theorem cell20_704302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_704302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704302 prefixEnd_704302 := by exact prefixLift 704302
  have htrace : WordTrace (prefixWord ++ tailWord_704302) baseStart_704302 baseEnd_704302 := by
    simpa [prefixWord, tailWord_704302, baseEnd_704302] using wordTrace_append hprefix tailTrace_704302
  have hstable : (prefixWord ++ tailWord_704302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704302).length < 2 ^ (prefixWord ++ tailWord_704302).sum := by decide
  have hdescent : baseEnd_704302 < baseStart_704302 := by decide
  rcases family_descends (prefixWord ++ tailWord_704302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704306 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_704306 : Nat := 118140960795 + 704306 * 2 ^ 59
def prefixEnd_704306 : Nat := 4983230072969 + 3 ^ 40 * 704306 * 2
def baseEnd_704306 : Nat := 321464449640557007320855

theorem tailTrace_704306 : CollatzResearch.WordTrace tailWord_704306 prefixEnd_704306 321464449640557007320855 := by
  unfold tailWord_704306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422037546606780683365193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17125433457618081822307181 6422037546606780683365193)
  ·
    refine ⟨4816528159955085512523895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6422037546606780683365193 4816528159955085512523895)
    ·
      refine ⟨7224792239932628268785843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4816528159955085512523895 7224792239932628268785843)
      ·
        refine ⟨10837188359898942403178765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7224792239932628268785843 10837188359898942403178765)
        ·
          refine ⟨4063945634962103401192037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10837188359898942403178765 4063945634962103401192037)
          ·
            refine ⟨761989806555394387723507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4063945634962103401192037 761989806555394387723507)
            ·
              refine ⟨1142984709833091581585261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761989806555394387723507 1142984709833091581585261)
              ·
                refine ⟨428619266187409343094473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142984709833091581585261 428619266187409343094473)
                ·
                  refine ⟨321464449640557007320855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428619266187409343094473 321464449640557007320855)
                  ·
                    rfl

theorem cell20_704306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_704306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704306 prefixEnd_704306 := by exact prefixLift 704306
  have htrace : WordTrace (prefixWord ++ tailWord_704306) baseStart_704306 baseEnd_704306 := by
    simpa [prefixWord, tailWord_704306, baseEnd_704306] using wordTrace_append hprefix tailTrace_704306
  have hstable : (prefixWord ++ tailWord_704306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704306).length < 2 ^ (prefixWord ++ tailWord_704306).sum := by decide
  have hdescent : baseEnd_704306 < baseStart_704306 := by decide
  rcases family_descends (prefixWord ++ tailWord_704306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704313 : List Nat := [1, 2, 1, 7, 2, 1, 6]
def baseStart_704313 : Nat := 118140960795 + 704313 * 2 ^ 59
def prefixEnd_704313 : Nat := 4983230072969 + 3 ^ 40 * 704313 * 2
def baseEnd_704313 : Nat := 35718627181255121565277

theorem tailTrace_704313 : CollatzResearch.WordTrace tailWord_704313 prefixEnd_704313 35718627181255121565277 := by
  unfold tailWord_704313
  simp only [CollatzResearch.WordTrace]
  refine ⟨25688405497401762928965593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17125603664934508619310395 25688405497401762928965593)
  ·
    refine ⟨19266304123051322196724195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25688405497401762928965593 19266304123051322196724195)
    ·
      refine ⟨28899456184576983295086293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19266304123051322196724195 28899456184576983295086293)
      ·
        refine ⟨677331004326023045978585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28899456184576983295086293 677331004326023045978585)
        ·
          refine ⟨507998253244517284483939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677331004326023045978585 507998253244517284483939)
          ·
            refine ⟨761997379866775926725909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507998253244517284483939 761997379866775926725909)
            ·
              refine ⟨35718627181255121565277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761997379866775926725909 35718627181255121565277)
              ·
                rfl

theorem cell20_704313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 6].length) (baseStart_704313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704313 prefixEnd_704313 := by exact prefixLift 704313
  have htrace : WordTrace (prefixWord ++ tailWord_704313) baseStart_704313 baseEnd_704313 := by
    simpa [prefixWord, tailWord_704313, baseEnd_704313] using wordTrace_append hprefix tailTrace_704313
  have hstable : (prefixWord ++ tailWord_704313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704313).length < 2 ^ (prefixWord ++ tailWord_704313).sum := by decide
  have hdescent : baseEnd_704313 < baseStart_704313 := by decide
  rcases family_descends (prefixWord ++ tailWord_704313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704317 : List Nat := [1, 4, 1, 4, 1, 1, 8]
def baseStart_704317 : Nat := 118140960795 + 704317 * 2 ^ 59
def prefixEnd_704317 : Nat := 4983230072969 + 3 ^ 40 * 704317 * 2
def baseEnd_704317 : Nat := 35718830037809984217127

theorem tailTrace_704317 : CollatzResearch.WordTrace tailWord_704317 prefixEnd_704317 35718830037809984217127 := by
  unfold tailWord_704317
  simp only [CollatzResearch.WordTrace]
  refine ⟨25688551389387271612111205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17125700926258181074740803 25688551389387271612111205)
  ·
    refine ⟨4816603385510113427270851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25688551389387271612111205 4816603385510113427270851)
    ·
      refine ⟨7224905078265170140906277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4816603385510113427270851 7224905078265170140906277)
      ·
        refine ⟨1354669702174719401419927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7224905078265170140906277 1354669702174719401419927)
        ·
          refine ⟨2032004553262079102129891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354669702174719401419927 2032004553262079102129891)
          ·
            refine ⟨3048006829893118653194837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032004553262079102129891 3048006829893118653194837)
            ·
              refine ⟨35718830037809984217127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3048006829893118653194837 35718830037809984217127)
              ·
                rfl

theorem cell20_704317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_704317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704317 prefixEnd_704317 := by exact prefixLift 704317
  have htrace : WordTrace (prefixWord ++ tailWord_704317) baseStart_704317 baseEnd_704317 := by
    simpa [prefixWord, tailWord_704317, baseEnd_704317] using wordTrace_append hprefix tailTrace_704317
  have hstable : (prefixWord ++ tailWord_704317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704317).length < 2 ^ (prefixWord ++ tailWord_704317).sum := by decide
  have hdescent : baseEnd_704317 < baseStart_704317 := by decide
  rcases family_descends (prefixWord ++ tailWord_704317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704341 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_704341 : Nat := 118140960795 + 704341 * 2 ^ 59
def prefixEnd_704341 : Nat := 4983230072969 + 3 ^ 40 * 704341 * 2
def baseEnd_704341 : Nat := 321480424594252441154045

theorem tailTrace_704341 : CollatzResearch.WordTrace tailWord_704341 prefixEnd_704341 321480424594252441154045 := by
  unfold tailWord_704341
  simp only [CollatzResearch.WordTrace]
  refine ⟨25689426741300323710984877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17126284494200215807323251 25689426741300323710984877)
  ·
    refine ⟨9633535027987621391619329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25689426741300323710984877 9633535027987621391619329)
    ·
      refine ⟨7225151270990716043714497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9633535027987621391619329 7225151270990716043714497)
      ·
        refine ⟨5418863453243037032785873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7225151270990716043714497 5418863453243037032785873)
        ·
          refine ⟨4064147589932277774589405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418863453243037032785873 4064147589932277774589405)
          ·
            refine ⟨1524055346224604165471027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4064147589932277774589405 1524055346224604165471027)
            ·
              refine ⟨2286083019336906248206541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524055346224604165471027 2286083019336906248206541)
              ·
                refine ⟨857281132251339843077453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2286083019336906248206541 857281132251339843077453)
                ·
                  refine ⟨321480424594252441154045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857281132251339843077453 321480424594252441154045)
                  ·
                    rfl

theorem cell20_704341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_704341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704341 prefixEnd_704341 := by exact prefixLift 704341
  have htrace : WordTrace (prefixWord ++ tailWord_704341) baseStart_704341 baseEnd_704341 := by
    simpa [prefixWord, tailWord_704341, baseEnd_704341] using wordTrace_append hprefix tailTrace_704341
  have hstable : (prefixWord ++ tailWord_704341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704341).length < 2 ^ (prefixWord ++ tailWord_704341).sum := by decide
  have hdescent : baseEnd_704341 < baseStart_704341 := by decide
  rcases family_descends (prefixWord ++ tailWord_704341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704407 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_704407 : Nat := 118140960795 + 704407 * 2 ^ 59
def prefixEnd_704407 : Nat := 4983230072969 + 3 ^ 40 * 704407 * 2
def baseEnd_704407 : Nat := 321510548792649544953775

theorem tailTrace_704407 : CollatzResearch.WordTrace tailWord_704407 prefixEnd_704407 321510548792649544953775 := by
  unfold tailWord_704407
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691833959061216982887475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17127889306040811321924983 25691833959061216982887475)
  ·
    refine ⟨38537750938591825474331213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25691833959061216982887475 38537750938591825474331213)
    ·
      refine ⟨14451656601971934552874205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38537750938591825474331213 14451656601971934552874205)
      ·
        refine ⟨5419371225739475457327827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14451656601971934552874205 5419371225739475457327827)
        ·
          refine ⟨8129056838609213185991741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419371225739475457327827 8129056838609213185991741)
          ·
            refine ⟨3048396314478454944746903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8129056838609213185991741 3048396314478454944746903)
            ·
              refine ⟨4572594471717682417120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048396314478454944746903 4572594471717682417120355)
              ·
                refine ⟨6858891707576523625680533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4572594471717682417120355 6858891707576523625680533)
                ·
                  refine ⟨321510548792649544953775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6858891707576523625680533 321510548792649544953775)
                  ·
                    rfl

theorem cell20_704407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_704407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704407 prefixEnd_704407 := by exact prefixLift 704407
  have htrace : WordTrace (prefixWord ++ tailWord_704407) baseStart_704407 baseEnd_704407 := by
    simpa [prefixWord, tailWord_704407, baseEnd_704407] using wordTrace_append hprefix tailTrace_704407
  have hstable : (prefixWord ++ tailWord_704407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704407).length < 2 ^ (prefixWord ++ tailWord_704407).sum := by decide
  have hdescent : baseEnd_704407 < baseStart_704407 := by decide
  rcases family_descends (prefixWord ++ tailWord_704407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704410 : List Nat := [3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_704410 : Nat := 118140960795 + 704410 * 2 ^ 59
def prefixEnd_704410 : Nat := 4983230072969 + 3 ^ 40 * 704410 * 2
def baseEnd_704410 : Nat := 107170639358131622617921

theorem tailTrace_704410 : CollatzResearch.WordTrace tailWord_704410 prefixEnd_704410 107170639358131622617921 := by
  unfold tailWord_704410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422985844512587123811671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17127962252033565663497789 6422985844512587123811671)
  ·
    refine ⟨9634478766768880685717507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6422985844512587123811671 9634478766768880685717507)
    ·
      refine ⟨14451718150153321028576261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9634478766768880685717507 14451718150153321028576261)
      ·
        refine ⟨2709697153153747692858049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14451718150153321028576261 2709697153153747692858049)
        ·
          refine ⟨2032272864865310769643537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2709697153153747692858049 2032272864865310769643537)
          ·
            refine ⟨1524204648648983077232653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2032272864865310769643537 1524204648648983077232653)
            ·
              refine ⟨571576743243368653962245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1524204648648983077232653 571576743243368653962245)
              ·
                refine ⟨107170639358131622617921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571576743243368653962245 107170639358131622617921)
                ·
                  rfl

theorem cell20_704410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_704410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704410 prefixEnd_704410 := by exact prefixLift 704410
  have htrace : WordTrace (prefixWord ++ tailWord_704410) baseStart_704410 baseEnd_704410 := by
    simpa [prefixWord, tailWord_704410, baseEnd_704410] using wordTrace_append hprefix tailTrace_704410
  have hstable : (prefixWord ++ tailWord_704410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704410).length < 2 ^ (prefixWord ++ tailWord_704410).sum := by decide
  have hdescent : baseEnd_704410 < baseStart_704410 := by decide
  rcases family_descends (prefixWord ++ tailWord_704410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704469 : List Nat := [1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_704469 : Nat := 118140960795 + 704469 * 2 ^ 59
def prefixEnd_704469 : Nat := 4983230072969 + 3 ^ 40 * 704469 * 2
def baseEnd_704469 : Nat := 107179615760684294962285

theorem tailTrace_704469 : CollatzResearch.WordTrace tailWord_704469 prefixEnd_704469 107179615760684294962285 := by
  unfold tailWord_704469
  simp only [CollatzResearch.WordTrace]
  refine ⟨25694095284836601571644461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17129396856557734381096307 25694095284836601571644461)
  ·
    refine ⟨9635285731813725589366673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25694095284836601571644461 9635285731813725589366673)
    ·
      refine ⟨7226464298860294192025005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9635285731813725589366673 7226464298860294192025005)
      ·
        refine ⟨2709924112072610322009377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7226464298860294192025005 2709924112072610322009377)
        ·
          refine ⟨2032443084054457741507033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2709924112072610322009377 2032443084054457741507033)
          ·
            refine ⟨1524332313040843306130275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2032443084054457741507033 1524332313040843306130275)
            ·
              refine ⟨2286498469561264959195413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524332313040843306130275 2286498469561264959195413)
              ·
                refine ⟨107179615760684294962285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2286498469561264959195413 107179615760684294962285)
                ·
                  rfl

theorem cell20_704469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_704469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704469 prefixEnd_704469 := by exact prefixLift 704469
  have htrace : WordTrace (prefixWord ++ tailWord_704469) baseStart_704469 baseEnd_704469 := by
    simpa [prefixWord, tailWord_704469, baseEnd_704469] using wordTrace_append hprefix tailTrace_704469
  have hstable : (prefixWord ++ tailWord_704469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704469).length < 2 ^ (prefixWord ++ tailWord_704469).sum := by decide
  have hdescent : baseEnd_704469 < baseStart_704469 := by decide
  rcases family_descends (prefixWord ++ tailWord_704469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704479 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 2]
def baseStart_704479 : Nat := 118140960795 + 704479 * 2 ^ 59
def prefixEnd_704479 : Nat := 4983230072969 + 3 ^ 40 * 704479 * 2
def baseEnd_704479 : Nat := 321543411554537294553481

theorem tailTrace_704479 : CollatzResearch.WordTrace tailWord_704479 prefixEnd_704479 321543411554537294553481 := by
  unfold tailWord_704479
  simp only [CollatzResearch.WordTrace]
  refine ⟨25694460014800373279508491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17129640009866915519672327 25694460014800373279508491)
  ·
    refine ⟨38541690022200559919262737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25694460014800373279508491 38541690022200559919262737)
    ·
      refine ⟨28906267516650419939447053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38541690022200559919262737 28906267516650419939447053)
      ·
        refine ⟨10839850318743907477292645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28906267516650419939447053 10839850318743907477292645)
        ·
          refine ⟨2032471934764482651992371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10839850318743907477292645 2032471934764482651992371)
          ·
            refine ⟨3048707902146723977988557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032471934764482651992371 3048707902146723977988557)
            ·
              refine ⟨1143265463305021491745709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3048707902146723977988557 1143265463305021491745709)
              ·
                refine ⟨428724548739383059404641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1143265463305021491745709 428724548739383059404641)
                ·
                  refine ⟨321543411554537294553481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428724548739383059404641 321543411554537294553481)
                  ·
                    rfl

theorem cell20_704479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2].length) (baseStart_704479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704479 prefixEnd_704479 := by exact prefixLift 704479
  have htrace : WordTrace (prefixWord ++ tailWord_704479) baseStart_704479 baseEnd_704479 := by
    simpa [prefixWord, tailWord_704479, baseEnd_704479] using wordTrace_append hprefix tailTrace_704479
  have hstable : (prefixWord ++ tailWord_704479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704479).length < 2 ^ (prefixWord ++ tailWord_704479).sum := by decide
  have hdescent : baseEnd_704479 < baseStart_704479 := by decide
  rcases family_descends (prefixWord ++ tailWord_704479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704510 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_704510 : Nat := 118140960795 + 704510 * 2 ^ 59
def prefixEnd_704510 : Nat := 4983230072969 + 3 ^ 40 * 704510 * 2
def baseEnd_704510 : Nat := 321557560799238964520021

theorem tailTrace_704510 : CollatzResearch.WordTrace tailWord_704510 prefixEnd_704510 321557560799238964520021 := by
  unfold tailWord_704510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211948834711008196735873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17130393785125377049257989 3211948834711008196735873)
  ·
    refine ⟨2408961626033256147551905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3211948834711008196735873 2408961626033256147551905)
    ·
      refine ⟨1806721219524942110663929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408961626033256147551905 1806721219524942110663929)
      ·
        refine ⟨1355040914643706582997947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1806721219524942110663929 1355040914643706582997947)
        ·
          refine ⟨2032561371965559874496921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355040914643706582997947 2032561371965559874496921)
          ·
            refine ⟨1524421028974169905872691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2032561371965559874496921 1524421028974169905872691)
            ·
              refine ⟨2286631543461254858809037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524421028974169905872691 2286631543461254858809037)
              ·
                refine ⟨857486828797970572053389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2286631543461254858809037 857486828797970572053389)
                ·
                  refine ⟨321557560799238964520021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857486828797970572053389 321557560799238964520021)
                  ·
                    rfl

theorem cell20_704510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_704510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704510 prefixEnd_704510 := by exact prefixLift 704510
  have htrace : WordTrace (prefixWord ++ tailWord_704510) baseStart_704510 baseEnd_704510 := by
    simpa [prefixWord, tailWord_704510, baseEnd_704510] using wordTrace_append hprefix tailTrace_704510
  have hstable : (prefixWord ++ tailWord_704510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704510).length < 2 ^ (prefixWord ++ tailWord_704510).sum := by decide
  have hdescent : baseEnd_704510 < baseStart_704510 := by decide
  rcases family_descends (prefixWord ++ tailWord_704510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704545 : List Nat := [1, 2, 3, 2, 5, 7]
def baseStart_704545 : Nat := 118140960795 + 704545 * 2 ^ 59
def prefixEnd_704545 : Nat := 4983230072969 + 3 ^ 40 * 704545 * 2
def baseEnd_704545 : Nat := 11910130953812385124193

theorem tailTrace_704545 : CollatzResearch.WordTrace tailWord_704545 prefixEnd_704545 11910130953812385124193 := by
  unfold tailWord_704545
  simp only [CollatzResearch.WordTrace]
  refine ⟨25696867232561266551411089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17131244821707511034274059 25696867232561266551411089)
  ·
    refine ⟨19272650424420949913558317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25696867232561266551411089 19272650424420949913558317)
    ·
      refine ⟨7227243909157856217584369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19272650424420949913558317 7227243909157856217584369)
      ·
        refine ⟨5420432931868392163188277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227243909157856217584369 5420432931868392163188277)
        ·
          refine ⟨508165587362661765298901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5420432931868392163188277 508165587362661765298901)
          ·
            refine ⟨11910130953812385124193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 508165587362661765298901 11910130953812385124193)
            ·
              rfl

theorem cell20_704545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 7].length) (baseStart_704545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704545 prefixEnd_704545 := by exact prefixLift 704545
  have htrace : WordTrace (prefixWord ++ tailWord_704545) baseStart_704545 baseEnd_704545 := by
    simpa [prefixWord, tailWord_704545, baseEnd_704545] using wordTrace_append hprefix tailTrace_704545
  have hstable : (prefixWord ++ tailWord_704545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704545).length < 2 ^ (prefixWord ++ tailWord_704545).sum := by decide
  have hdescent : baseEnd_704545 < baseStart_704545 := by decide
  rcases family_descends (prefixWord ++ tailWord_704545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704548 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_704548 : Nat := 118140960795 + 704548 * 2 ^ 59
def prefixEnd_704548 : Nat := 4983230072969 + 3 ^ 40 * 704548 * 2
def baseEnd_704548 : Nat := 321574905034679721253199

theorem tailTrace_704548 : CollatzResearch.WordTrace tailWord_704548 prefixEnd_704548 321574905034679721253199 := by
  unfold tailWord_704548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12848488325775199031885149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17131317767700265375846865 12848488325775199031885149)
  ·
    refine ⟨4818183122165699636956931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12848488325775199031885149 4818183122165699636956931)
    ·
      refine ⟨7227274683248549455435397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818183122165699636956931 7227274683248549455435397)
      ·
        refine ⟨1355114003109103022894137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7227274683248549455435397 1355114003109103022894137)
        ·
          refine ⟨1016335502331827267170603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355114003109103022894137 1016335502331827267170603)
          ·
            refine ⟨1524503253497740900755905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016335502331827267170603 1524503253497740900755905)
            ·
              refine ⟨1143377440123305675566929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524503253497740900755905 1143377440123305675566929)
              ·
                refine ⟨857533080092479256675197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143377440123305675566929 857533080092479256675197)
                ·
                  refine ⟨321574905034679721253199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857533080092479256675197 321574905034679721253199)
                  ·
                    rfl

theorem cell20_704548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_704548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704548 prefixEnd_704548 := by exact prefixLift 704548
  have htrace : WordTrace (prefixWord ++ tailWord_704548) baseStart_704548 baseEnd_704548 := by
    simpa [prefixWord, tailWord_704548, baseEnd_704548] using wordTrace_append hprefix tailTrace_704548
  have hstable : (prefixWord ++ tailWord_704548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704548).length < 2 ^ (prefixWord ++ tailWord_704548).sum := by decide
  have hdescent : baseEnd_704548 < baseStart_704548 := by decide
  rcases family_descends (prefixWord ++ tailWord_704548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704583 : List Nat := [1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_704583 : Nat := 118140960795 + 704583 * 2 ^ 59
def prefixEnd_704583 : Nat := 4983230072969 + 3 ^ 40 * 704583 * 2
def baseEnd_704583 : Nat := 107196959996125051695463

theorem tailTrace_704583 : CollatzResearch.WordTrace tailWord_704583 prefixEnd_704583 107196959996125051695463 := by
  unfold tailWord_704583
  simp only [CollatzResearch.WordTrace]
  refine ⟨25698253206423599041294403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17132168804282399360862935 25698253206423599041294403)
  ·
    refine ⟨38547379809635398561941605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25698253206423599041294403 38547379809635398561941605)
    ·
      refine ⟨7227633714306637230364051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38547379809635398561941605 7227633714306637230364051)
      ·
        refine ⟨10841450571459955845546077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7227633714306637230364051 10841450571459955845546077)
        ·
          refine ⟨4065543964297483442079779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10841450571459955845546077 4065543964297483442079779)
          ·
            refine ⟨6098315946446225163119669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065543964297483442079779 6098315946446225163119669)
            ·
              refine ⟨571717119979333609042469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6098315946446225163119669 571717119979333609042469)
              ·
                refine ⟨107196959996125051695463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571717119979333609042469 107196959996125051695463)
                ·
                  rfl

theorem cell20_704583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_704583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704583 prefixEnd_704583 := by exact prefixLift 704583
  have htrace : WordTrace (prefixWord ++ tailWord_704583) baseStart_704583 baseEnd_704583 := by
    simpa [prefixWord, tailWord_704583, baseEnd_704583] using wordTrace_append hprefix tailTrace_704583
  have hstable : (prefixWord ++ tailWord_704583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704583).length < 2 ^ (prefixWord ++ tailWord_704583).sum := by decide
  have hdescent : baseEnd_704583 < baseStart_704583 := by decide
  rcases family_descends (prefixWord ++ tailWord_704583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704648 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_704648 : Nat := 118140960795 + 704648 * 2 ^ 59
def prefixEnd_704648 : Nat := 4983230072969 + 3 ^ 40 * 704648 * 2
def baseEnd_704648 : Nat := 321620547759523817919457

theorem tailTrace_704648 : CollatzResearch.WordTrace tailWord_704648 prefixEnd_704648 321620547759523817919457 := by
  unfold tailWord_704648
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850311975594057571205299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17133749300792076761607065 12850311975594057571205299)
  ·
    refine ⟨19275467963391086356807949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12850311975594057571205299 19275467963391086356807949)
    ·
      refine ⟨7228300486271657383802981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19275467963391086356807949 7228300486271657383802981)
      ·
        refine ⟨1355306341175935759463059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7228300486271657383802981 1355306341175935759463059)
        ·
          refine ⟨2032959511763903639194589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355306341175935759463059 2032959511763903639194589)
          ·
            refine ⟨762359816911463864697971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2032959511763903639194589 762359816911463864697971)
            ·
              refine ⟨1143539725367195797046957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762359816911463864697971 1143539725367195797046957)
              ·
                refine ⟨428827397012698423892609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1143539725367195797046957 428827397012698423892609)
                ·
                  refine ⟨321620547759523817919457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428827397012698423892609 321620547759523817919457)
                  ·
                    rfl

theorem cell20_704648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_704648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704648 prefixEnd_704648 := by exact prefixLift 704648
  have htrace : WordTrace (prefixWord ++ tailWord_704648) baseStart_704648 baseEnd_704648 := by
    simpa [prefixWord, tailWord_704648, baseEnd_704648] using wordTrace_append hprefix tailTrace_704648
  have hstable : (prefixWord ++ tailWord_704648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704648).length < 2 ^ (prefixWord ++ tailWord_704648).sum := by decide
  have hdescent : baseEnd_704648 < baseStart_704648 := by decide
  rcases family_descends (prefixWord ++ tailWord_704648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704649 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_704649 : Nat := 118140960795 + 704649 * 2 ^ 59
def prefixEnd_704649 : Nat := 4983230072969 + 3 ^ 40 * 704649 * 2
def baseEnd_704649 : Nat := 321621004186772258886119

theorem tailTrace_704649 : CollatzResearch.WordTrace tailWord_704649 prefixEnd_704649 321621004186772258886119 := by
  unfold tailWord_704649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25700660424184492313197001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17133773616122994875464667 25700660424184492313197001)
  ·
    refine ⟨19275495318138369234897751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25700660424184492313197001 19275495318138369234897751)
    ·
      refine ⟨28913242977207553852346627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19275495318138369234897751 28913242977207553852346627)
      ·
        refine ⟨43369864465811330778519941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28913242977207553852346627 43369864465811330778519941)
        ·
          refine ⟨8131849587339624520972489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43369864465811330778519941 8131849587339624520972489)
          ·
            refine ⟨6098887190504718390729367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8131849587339624520972489 6098887190504718390729367)
            ·
              refine ⟨9148330785757077586094051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098887190504718390729367 9148330785757077586094051)
              ·
                refine ⟨13722496178635616379141077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9148330785757077586094051 13722496178635616379141077)
                ·
                  refine ⟨321621004186772258886119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13722496178635616379141077 321621004186772258886119)
                  ·
                    rfl

theorem cell20_704649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_704649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704649 prefixEnd_704649 := by exact prefixLift 704649
  have htrace : WordTrace (prefixWord ++ tailWord_704649) baseStart_704649 baseEnd_704649 := by
    simpa [prefixWord, tailWord_704649, baseEnd_704649] using wordTrace_append hprefix tailTrace_704649
  have hstable : (prefixWord ++ tailWord_704649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704649).length < 2 ^ (prefixWord ++ tailWord_704649).sum := by decide
  have hdescent : baseEnd_704649 < baseStart_704649 := by decide
  rcases family_descends (prefixWord ++ tailWord_704649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704679 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 3]
def baseStart_704679 : Nat := 118140960795 + 704679 * 2 ^ 59
def prefixEnd_704679 : Nat := 4983230072969 + 3 ^ 40 * 704679 * 2
def baseEnd_704679 : Nat := 321634697004225487885997

theorem tailTrace_704679 : CollatzResearch.WordTrace tailWord_704679 prefixEnd_704679 321634697004225487885997 := by
  unfold tailWord_704679
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701754614075807436789091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17134503076050538291192727 25701754614075807436789091)
  ·
    refine ⟨38552631921113711155183637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25701754614075807436789091 38552631921113711155183637)
    ·
      refine ⟨1807154621302205210399233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38552631921113711155183637 1807154621302205210399233)
      ·
        refine ⟨1355365965976653907799425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1807154621302205210399233 1355365965976653907799425)
        ·
          refine ⟨1016524474482490430849569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355365965976653907799425 1016524474482490430849569)
          ·
            refine ⟨762393355861867823137177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016524474482490430849569 762393355861867823137177)
            ·
              refine ⟨571795016896400867352883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762393355861867823137177 571795016896400867352883)
              ·
                refine ⟨857692525344601301029325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571795016896400867352883 857692525344601301029325)
                ·
                  refine ⟨321634697004225487885997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857692525344601301029325 321634697004225487885997)
                  ·
                    rfl

theorem cell20_704679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_704679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704679 prefixEnd_704679 := by exact prefixLift 704679
  have htrace : WordTrace (prefixWord ++ tailWord_704679) baseStart_704679 baseEnd_704679 := by
    simpa [prefixWord, tailWord_704679, baseEnd_704679] using wordTrace_append hprefix tailTrace_704679
  have hstable : (prefixWord ++ tailWord_704679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704679).length < 2 ^ (prefixWord ++ tailWord_704679).sum := by decide
  have hdescent : baseEnd_704679 < baseStart_704679 := by decide
  rcases family_descends (prefixWord ++ tailWord_704679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704718 : List Nat := [4, 1, 1, 1, 4, 9]
def baseStart_704718 : Nat := 118140960795 + 704718 * 2 ^ 59
def prefixEnd_704718 : Nat := 4983230072969 + 3 ^ 40 * 704718 * 2
def baseEnd_704718 : Nat := 11913055469144988355031

theorem tailTrace_704718 : CollatzResearch.WordTrace tailWord_704718 prefixEnd_704718 11913055469144988355031 := by
  unfold tailWord_704718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212897132616814637182351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17135451373956344731639205 3212897132616814637182351)
  ·
    refine ⟨4819345698925221955773527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3212897132616814637182351 4819345698925221955773527)
    ·
      refine ⟨7229018548387832933660291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4819345698925221955773527 7229018548387832933660291)
      ·
        refine ⟨10843527822581749400490437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229018548387832933660291 10843527822581749400490437)
        ·
          refine ⟨2033161466734078012591957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10843527822581749400490437 2033161466734078012591957)
          ·
            refine ⟨11913055469144988355031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2033161466734078012591957 11913055469144988355031)
            ·
              rfl

theorem cell20_704718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 9].length) (baseStart_704718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704718 prefixEnd_704718 := by exact prefixLift 704718
  have htrace : WordTrace (prefixWord ++ tailWord_704718) baseStart_704718 baseEnd_704718 := by
    simpa [prefixWord, tailWord_704718, baseEnd_704718] using wordTrace_append hprefix tailTrace_704718
  have hstable : (prefixWord ++ tailWord_704718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704718).length < 2 ^ (prefixWord ++ tailWord_704718).sum := by decide
  have hdescent : baseEnd_704718 < baseStart_704718 := by decide
  rcases family_descends (prefixWord ++ tailWord_704718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704807 : List Nat := [1, 1, 8, 1, 1, 1, 1, 6]
def baseStart_704807 : Nat := 118140960795 + 704807 * 2 ^ 59
def prefixEnd_704807 : Nat := 4983230072969 + 3 ^ 40 * 704807 * 2
def baseEnd_704807 : Nat := 107231039897341977206269

theorem tailTrace_704807 : CollatzResearch.WordTrace tailWord_704807 prefixEnd_704807 107231039897341977206269 := by
  unfold tailWord_704807
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706423157612085297448675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17137615438408056864965783 25706423157612085297448675)
  ·
    refine ⟨38559634736418127946173013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25706423157612085297448675 38559634736418127946173013)
    ·
      refine ⟨451870719567399936869215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 38559634736418127946173013 451870719567399936869215)
      ·
        refine ⟨677806079351099905303823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451870719567399936869215 677806079351099905303823)
        ·
          refine ⟨1016709119026649857955735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677806079351099905303823 1016709119026649857955735)
          ·
            refine ⟨1525063678539974786933603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016709119026649857955735 1525063678539974786933603)
            ·
              refine ⟨2287595517809962180400405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525063678539974786933603 2287595517809962180400405)
              ·
                refine ⟨107231039897341977206269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2287595517809962180400405 107231039897341977206269)
                ·
                  rfl

theorem cell20_704807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_704807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704807 prefixEnd_704807 := by exact prefixLift 704807
  have htrace : WordTrace (prefixWord ++ tailWord_704807) baseStart_704807 baseEnd_704807 := by
    simpa [prefixWord, tailWord_704807, baseEnd_704807] using wordTrace_append hprefix tailTrace_704807
  have hstable : (prefixWord ++ tailWord_704807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704807).length < 2 ^ (prefixWord ++ tailWord_704807).sum := by decide
  have hdescent : baseEnd_704807 < baseStart_704807 := by decide
  rcases family_descends (prefixWord ++ tailWord_704807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704839 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_704839 : Nat := 118140960795 + 704839 * 2 ^ 59
def prefixEnd_704839 : Nat := 4983230072969 + 3 ^ 40 * 704839 * 2
def baseEnd_704839 : Nat := 321707725363976042552009

theorem tailTrace_704839 : CollatzResearch.WordTrace tailWord_704839 prefixEnd_704839 321707725363976042552009 := by
  unfold tailWord_704839
  simp only [CollatzResearch.WordTrace]
  refine ⟨25707590293496154762613571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17138393528997436508409047 25707590293496154762613571)
  ·
    refine ⟨38561385440244232143920357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25707590293496154762613571 38561385440244232143920357)
    ·
      refine ⟨7230259770045793526985067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38561385440244232143920357 7230259770045793526985067)
      ·
        refine ⟨10845389655068690290477601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7230259770045793526985067 10845389655068690290477601)
        ·
          refine ⟨8134042241301517717858201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10845389655068690290477601 8134042241301517717858201)
          ·
            refine ⟨6100531680976138288393651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8134042241301517717858201 6100531680976138288393651)
            ·
              refine ⟨9150797521464207432590477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100531680976138288393651 9150797521464207432590477)
              ·
                refine ⟨3431549070549077787221429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9150797521464207432590477 3431549070549077787221429)
                ·
                  refine ⟨321707725363976042552009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431549070549077787221429 321707725363976042552009)
                  ·
                    rfl

theorem cell20_704839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_704839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704839 prefixEnd_704839 := by exact prefixLift 704839
  have htrace : WordTrace (prefixWord ++ tailWord_704839) baseStart_704839 baseEnd_704839 := by
    simpa [prefixWord, tailWord_704839, baseEnd_704839] using wordTrace_append hprefix tailTrace_704839
  have hstable : (prefixWord ++ tailWord_704839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704839).length < 2 ^ (prefixWord ++ tailWord_704839).sum := by decide
  have hdescent : baseEnd_704839 < baseStart_704839 := by decide
  rcases family_descends (prefixWord ++ tailWord_704839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704852 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_704852 : Nat := 118140960795 + 704852 * 2 ^ 59
def prefixEnd_704852 : Nat := 4983230072969 + 3 ^ 40 * 704852 * 2
def baseEnd_704852 : Nat := 321713658918205775118623

theorem tailTrace_704852 : CollatzResearch.WordTrace tailWord_704852 prefixEnd_704852 321713658918205775118623 := by
  unfold tailWord_704852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854032221224528991418405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17138709628299371988557873 12854032221224528991418405)
  ·
    refine ⟨2410131041479599185890951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12854032221224528991418405 2410131041479599185890951)
    ·
      refine ⟨3615196562219398778836427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410131041479599185890951 3615196562219398778836427)
      ·
        refine ⟨5422794843329098168254641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615196562219398778836427 5422794843329098168254641)
        ·
          refine ⟨4067096132496823626190981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5422794843329098168254641 4067096132496823626190981)
          ·
            refine ⟨762580524843154429910809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4067096132496823626190981 762580524843154429910809)
            ·
              refine ⟨571935393632365822433107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762580524843154429910809 571935393632365822433107)
              ·
                refine ⟨857903090448548733649661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571935393632365822433107 857903090448548733649661)
                ·
                  refine ⟨321713658918205775118623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857903090448548733649661 321713658918205775118623)
                  ·
                    rfl

theorem cell20_704852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_704852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704852 prefixEnd_704852 := by exact prefixLift 704852
  have htrace : WordTrace (prefixWord ++ tailWord_704852) baseStart_704852 baseEnd_704852 := by
    simpa [prefixWord, tailWord_704852, baseEnd_704852] using wordTrace_append hprefix tailTrace_704852
  have hstable : (prefixWord ++ tailWord_704852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704852).length < 2 ^ (prefixWord ++ tailWord_704852).sum := by decide
  have hdescent : baseEnd_704852 < baseStart_704852 := by decide
  rcases family_descends (prefixWord ++ tailWord_704852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704891 : List Nat := [1, 1, 1, 1, 1, 15]
def baseStart_704891 : Nat := 118140960795 + 704891 * 2 ^ 59
def prefixEnd_704891 : Nat := 4983230072969 + 3 ^ 40 * 704891 * 2
def baseEnd_704891 : Nat := 11915979984477591585869

theorem tailTrace_704891 : CollatzResearch.WordTrace tailWord_704891 prefixEnd_704891 11915979984477591585869 := by
  unfold tailWord_704891
  simp only [CollatzResearch.WordTrace]
  refine ⟨25709486889307767643506527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17139657926205178429004351 25709486889307767643506527)
  ·
    refine ⟨38564230333961651465259791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25709486889307767643506527 38564230333961651465259791)
    ·
      refine ⟨57846345500942477197889687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38564230333961651465259791 57846345500942477197889687)
      ·
        refine ⟨86769518251413715796834531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57846345500942477197889687 86769518251413715796834531)
        ·
          refine ⟨130154277377120573695251797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86769518251413715796834531 130154277377120573695251797)
          ·
            refine ⟨11915979984477591585869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 130154277377120573695251797 11915979984477591585869)
            ·
              rfl

theorem cell20_704891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 15].length) (baseStart_704891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704891 prefixEnd_704891 := by exact prefixLift 704891
  have htrace : WordTrace (prefixWord ++ tailWord_704891) baseStart_704891 baseEnd_704891 := by
    simpa [prefixWord, tailWord_704891, baseEnd_704891] using wordTrace_append hprefix tailTrace_704891
  have hstable : (prefixWord ++ tailWord_704891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704891).length < 2 ^ (prefixWord ++ tailWord_704891).sum := by decide
  have hdescent : baseEnd_704891 < baseStart_704891 := by decide
  rcases family_descends (prefixWord ++ tailWord_704891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704897 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 2]
def baseStart_704897 : Nat := 118140960795 + 704897 * 2 ^ 59
def prefixEnd_704897 : Nat := 4983230072969 + 3 ^ 40 * 704897 * 2
def baseEnd_704897 : Nat := 321734198144385618618439

theorem tailTrace_704897 : CollatzResearch.WordTrace tailWord_704897 prefixEnd_704897 321734198144385618618439 := by
  unfold tailWord_704897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25709705727286030668224945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17139803818190687112149963 25709705727286030668224945)
  ·
    refine ⟨19282279295464523001168709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25709705727286030668224945 19282279295464523001168709)
    ·
      refine ⟨3615427367899598062719133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19282279295464523001168709 3615427367899598062719133)
      ·
        refine ⟨1355785262962349273519675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3615427367899598062719133 1355785262962349273519675)
        ·
          refine ⟨2033677894443523910279513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355785262962349273519675 2033677894443523910279513)
          ·
            refine ⟨1525258420832642932709635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033677894443523910279513 1525258420832642932709635)
            ·
              refine ⟨2287887631248964399064453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525258420832642932709635 2287887631248964399064453)
              ·
                refine ⟨428978930859180824824585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2287887631248964399064453 428978930859180824824585)
                ·
                  refine ⟨321734198144385618618439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428978930859180824824585 321734198144385618618439)
                  ·
                    rfl

theorem cell20_704897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_704897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704897 prefixEnd_704897 := by exact prefixLift 704897
  have htrace : WordTrace (prefixWord ++ tailWord_704897) baseStart_704897 baseEnd_704897 := by
    simpa [prefixWord, tailWord_704897, baseEnd_704897] using wordTrace_append hprefix tailTrace_704897
  have hstable : (prefixWord ++ tailWord_704897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704897).length < 2 ^ (prefixWord ++ tailWord_704897).sum := by decide
  have hdescent : baseEnd_704897 < baseStart_704897 := by decide
  rcases family_descends (prefixWord ++ tailWord_704897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704908 : List Nat := [2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_704908 : Nat := 118140960795 + 704908 * 2 ^ 59
def prefixEnd_704908 : Nat := 4983230072969 + 3 ^ 40 * 704908 * 2
def baseEnd_704908 : Nat := 107246406281372823083909

theorem tailTrace_704908 : CollatzResearch.WordTrace tailWord_704908 prefixEnd_704908 107246406281372823083909 := by
  unfold tailWord_704908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12855053465123089773437689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17140071286830786364583585 12855053465123089773437689)
  ·
    refine ⟨9641290098842317330078267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12855053465123089773437689 9641290098842317330078267)
    ·
      refine ⟨14461935148263475995117401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641290098842317330078267 14461935148263475995117401)
      ·
        refine ⟨10846451361197606996338051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14461935148263475995117401 10846451361197606996338051)
        ·
          refine ⟨16269677041796410494507077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10846451361197606996338051 16269677041796410494507077)
          ·
            refine ⟨3050564445336826967720077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16269677041796410494507077 3050564445336826967720077)
            ·
              refine ⟨1143961667001310112895029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3050564445336826967720077 1143961667001310112895029)
              ·
                refine ⟨107246406281372823083909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1143961667001310112895029 107246406281372823083909)
                ·
                  rfl

theorem cell20_704908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_704908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704908 prefixEnd_704908 := by exact prefixLift 704908
  have htrace : WordTrace (prefixWord ++ tailWord_704908) baseStart_704908 baseEnd_704908 := by
    simpa [prefixWord, tailWord_704908, baseEnd_704908] using wordTrace_append hprefix tailTrace_704908
  have hstable : (prefixWord ++ tailWord_704908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704908).length < 2 ^ (prefixWord ++ tailWord_704908).sum := by decide
  have hdescent : baseEnd_704908 < baseStart_704908 := by decide
  rcases family_descends (prefixWord ++ tailWord_704908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704935 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 2]
def baseStart_704935 : Nat := 118140960795 + 704935 * 2 ^ 59
def prefixEnd_704935 : Nat := 4983230072969 + 3 ^ 40 * 704935 * 2
def baseEnd_704935 : Nat := 321751542379826375351617

theorem tailTrace_704935 : CollatzResearch.WordTrace tailWord_704935 prefixEnd_704935 321751542379826375351617 := by
  unfold tailWord_704935
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711091701148363158108259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17140727800765575438738839 25711091701148363158108259)
  ·
    refine ⟨38566637551722544737162389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25711091701148363158108259 38566637551722544737162389)
    ·
      refine ⟨1807811135236994284554487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38566637551722544737162389 1807811135236994284554487)
      ·
        refine ⟨2711716702855491426831731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807811135236994284554487 2711716702855491426831731)
        ·
          refine ⟨4067575054283237140247597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711716702855491426831731 4067575054283237140247597)
          ·
            refine ⟨1525340645356213927592849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4067575054283237140247597 1525340645356213927592849)
            ·
              refine ⟨1144005484017160445694637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525340645356213927592849 1144005484017160445694637)
              ·
                refine ⟨429002056506435167135489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1144005484017160445694637 429002056506435167135489)
                ·
                  refine ⟨321751542379826375351617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429002056506435167135489 321751542379826375351617)
                  ·
                    rfl

theorem cell20_704935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2].length) (baseStart_704935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704935 prefixEnd_704935 := by exact prefixLift 704935
  have htrace : WordTrace (prefixWord ++ tailWord_704935) baseStart_704935 baseEnd_704935 := by
    simpa [prefixWord, tailWord_704935, baseEnd_704935] using wordTrace_append hprefix tailTrace_704935
  have hstable : (prefixWord ++ tailWord_704935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704935).length < 2 ^ (prefixWord ++ tailWord_704935).sum := by decide
  have hdescent : baseEnd_704935 < baseStart_704935 := by decide
  rcases family_descends (prefixWord ++ tailWord_704935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704956 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_704956 : Nat := 118140960795 + 704956 * 2 ^ 59
def prefixEnd_704956 : Nat := 4983230072969 + 3 ^ 40 * 704956 * 2
def baseEnd_704956 : Nat := 321761127352043635651531

theorem tailTrace_704956 : CollatzResearch.WordTrace tailWord_704956 prefixEnd_704956 321761127352043635651531 := by
  unfold tailWord_704956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12855928817036141872311361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17141238422714855829748481 12855928817036141872311361)
  ·
    refine ⟨9641946612777106404233521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12855928817036141872311361 9641946612777106404233521)
    ·
      refine ⟨7231459959582829803175141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9641946612777106404233521 7231459959582829803175141)
      ·
        refine ⟨1355898742421780588095339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7231459959582829803175141 1355898742421780588095339)
        ·
          refine ⟨2033848113632670882143009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355898742421780588095339 2033848113632670882143009)
          ·
            refine ⟨1525386085224503161607257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033848113632670882143009 1525386085224503161607257)
            ·
              refine ⟨1144039563918377371205443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525386085224503161607257 1144039563918377371205443)
              ·
                refine ⟨1716059345877566056808165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144039563918377371205443 1716059345877566056808165)
                ·
                  refine ⟨321761127352043635651531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716059345877566056808165 321761127352043635651531)
                  ·
                    rfl

theorem cell20_704956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_704956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704956 prefixEnd_704956 := by exact prefixLift 704956
  have htrace : WordTrace (prefixWord ++ tailWord_704956) baseStart_704956 baseEnd_704956 := by
    simpa [prefixWord, tailWord_704956, baseEnd_704956] using wordTrace_append hprefix tailTrace_704956
  have hstable : (prefixWord ++ tailWord_704956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704956).length < 2 ^ (prefixWord ++ tailWord_704956).sum := by decide
  have hdescent : baseEnd_704956 < baseStart_704956 := by decide
  rcases family_descends (prefixWord ++ tailWord_704956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704980 : List Nat := [2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_704980 : Nat := 118140960795 + 704980 * 2 ^ 59
def prefixEnd_704980 : Nat := 4983230072969 + 3 ^ 40 * 704980 * 2
def baseEnd_704980 : Nat := 107257360535335406283811

theorem tailTrace_704980 : CollatzResearch.WordTrace tailWord_704980 prefixEnd_704980 107257360535335406283811 := by
  unfold tailWord_704980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856366492992667921748197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17141821990656890562330929 12856366492992667921748197)
  ·
    refine ⟨2410568717436125235327787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12856366492992667921748197 2410568717436125235327787)
    ·
      refine ⟨3615853076154187852991681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410568717436125235327787 3615853076154187852991681)
      ·
        refine ⟨2711889807115640889743761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3615853076154187852991681 2711889807115640889743761)
        ·
          refine ⟨2033917355336730667307821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2711889807115640889743761 2033917355336730667307821)
          ·
            refine ⟨762719008251274000240433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2033917355336730667307821 762719008251274000240433)
            ·
              refine ⟨572039256188455500180325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762719008251274000240433 572039256188455500180325)
              ·
                refine ⟨107257360535335406283811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572039256188455500180325 107257360535335406283811)
                ·
                  rfl

theorem cell20_704980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_704980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704980 prefixEnd_704980 := by exact prefixLift 704980
  have htrace : WordTrace (prefixWord ++ tailWord_704980) baseStart_704980 baseEnd_704980 := by
    simpa [prefixWord, tailWord_704980, baseEnd_704980] using wordTrace_append hprefix tailTrace_704980
  have hstable : (prefixWord ++ tailWord_704980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704980).length < 2 ^ (prefixWord ++ tailWord_704980).sum := by decide
  have hdescent : baseEnd_704980 < baseStart_704980 := by decide
  rcases family_descends (prefixWord ++ tailWord_704980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704991 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_704991 : Nat := 118140960795 + 704991 * 2 ^ 59
def prefixEnd_704991 : Nat := 4983230072969 + 3 ^ 40 * 704991 * 2
def baseEnd_704991 : Nat := 321777102305739069484721

theorem tailTrace_704991 : CollatzResearch.WordTrace tailWord_704991 prefixEnd_704991 321777102305739069484721 := by
  unfold tailWord_704991
  simp only [CollatzResearch.WordTrace]
  refine ⟨25713134188945484722146827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17142089459296989814764551 25713134188945484722146827)
  ·
    refine ⟨38569701283418227083220241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25713134188945484722146827 38569701283418227083220241)
    ·
      refine ⟨28927275962563670312415181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38569701283418227083220241 28927275962563670312415181)
      ·
        refine ⟨10847728485961376367155693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28927275962563670312415181 10847728485961376367155693)
        ·
          refine ⟨4067898182235516137683385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10847728485961376367155693 4067898182235516137683385)
          ·
            refine ⟨3050923636676637103262539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067898182235516137683385 3050923636676637103262539)
            ·
              refine ⟨4576385455014955654893809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050923636676637103262539 4576385455014955654893809)
              ·
                refine ⟨3432289091261216741170357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576385455014955654893809 3432289091261216741170357)
                ·
                  refine ⟨321777102305739069484721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432289091261216741170357 321777102305739069484721)
                  ·
                    rfl

theorem cell20_704991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_704991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_704991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_704991 prefixEnd_704991 := by exact prefixLift 704991
  have htrace : WordTrace (prefixWord ++ tailWord_704991) baseStart_704991 baseEnd_704991 := by
    simpa [prefixWord, tailWord_704991, baseEnd_704991] using wordTrace_append hprefix tailTrace_704991
  have hstable : (prefixWord ++ tailWord_704991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704991).length < 2 ^ (prefixWord ++ tailWord_704991).sum := by decide
  have hdescent : baseEnd_704991 < baseStart_704991 := by decide
  rcases family_descends (prefixWord ++ tailWord_704991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705025 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 3]
def baseStart_705025 : Nat := 118140960795 + 705025 * 2 ^ 59
def prefixEnd_705025 : Nat := 4983230072969 + 3 ^ 40 * 705025 * 2
def baseEnd_705025 : Nat := 321792620832186062351249

theorem tailTrace_705025 : CollatzResearch.WordTrace tailWord_705025 prefixEnd_705025 321792620832186062351249 := by
  unfold tailWord_705025
  simp only [CollatzResearch.WordTrace]
  refine ⟨25714374270822308528884529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17142916180548205685923019 25714374270822308528884529)
  ·
    refine ⟨19285780703116731396663397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25714374270822308528884529 19285780703116731396663397)
    ·
      refine ⟨3616083881834387136874387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19285780703116731396663397 3616083881834387136874387)
      ·
        refine ⟨5424125822751580705311581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616083881834387136874387 5424125822751580705311581)
        ·
          refine ⟨2034047183531842764491843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5424125822751580705311581 2034047183531842764491843)
          ·
            refine ⟨3051070775297764146737765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034047183531842764491843 3051070775297764146737765)
            ·
              refine ⟨572075770368330777513331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3051070775297764146737765 572075770368330777513331)
              ·
                refine ⟨858113655552496166269997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572075770368330777513331 858113655552496166269997)
                ·
                  refine ⟨321792620832186062351249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858113655552496166269997 321792620832186062351249)
                  ·
                    rfl

theorem cell20_705025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_705025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705025 prefixEnd_705025 := by exact prefixLift 705025
  have htrace : WordTrace (prefixWord ++ tailWord_705025) baseStart_705025 baseEnd_705025 := by
    simpa [prefixWord, tailWord_705025, baseEnd_705025] using wordTrace_append hprefix tailTrace_705025
  have hstable : (prefixWord ++ tailWord_705025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705025).length < 2 ^ (prefixWord ++ tailWord_705025).sum := by decide
  have hdescent : baseEnd_705025 < baseStart_705025 := by decide
  rcases family_descends (prefixWord ++ tailWord_705025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705043 : List Nat := [1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_705043 : Nat := 118140960795 + 705043 * 2 ^ 59
def prefixEnd_705043 : Nat := 4983230072969 + 3 ^ 40 * 705043 * 2
def baseEnd_705043 : Nat := 107266945507552666583725

theorem tailTrace_705043 : CollatzResearch.WordTrace tailWord_705043 prefixEnd_705043 107266945507552666583725 := by
  unfold tailWord_705043
  simp only [CollatzResearch.WordTrace]
  refine ⟨25715030784757097603039783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17143353856504731735359855 25715030784757097603039783)
  ·
    refine ⟨38572546177135646404559675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25715030784757097603039783 38572546177135646404559675)
    ·
      refine ⟨57858819265703469606839513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38572546177135646404559675 57858819265703469606839513)
      ·
        refine ⟨43394114449277602205129635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57858819265703469606839513 43394114449277602205129635)
        ·
          refine ⟨65091171673916403307694453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43394114449277602205129635 65091171673916403307694453)
          ·
            refine ⟨6102297344429662810096355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65091171673916403307694453 6102297344429662810096355)
            ·
              refine ⟨9153446016644494215144533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102297344429662810096355 9153446016644494215144533)
              ·
                refine ⟨107266945507552666583725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9153446016644494215144533 107266945507552666583725)
                ·
                  rfl

theorem cell20_705043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_705043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705043 prefixEnd_705043 := by exact prefixLift 705043
  have htrace : WordTrace (prefixWord ++ tailWord_705043) baseStart_705043 baseEnd_705043 := by
    simpa [prefixWord, tailWord_705043, baseEnd_705043] using wordTrace_append hprefix tailTrace_705043
  have hstable : (prefixWord ++ tailWord_705043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705043).length < 2 ^ (prefixWord ++ tailWord_705043).sum := by decide
  have hdescent : baseEnd_705043 < baseStart_705043 := by decide
  rcases family_descends (prefixWord ++ tailWord_705043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705060 : List Nat := [2, 3, 1, 5, 9]
def baseStart_705060 : Nat := 118140960795 + 705060 * 2 ^ 59
def prefixEnd_705060 : Nat := 4983230072969 + 3 ^ 40 * 705060 * 2
def baseEnd_705060 : Nat := 3972945626986191310919

theorem tailTrace_705060 : CollatzResearch.WordTrace tailWord_705060 prefixEnd_705060 3972945626986191310919 := by
  unfold tailWord_705060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857825412847754753204317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17143767217130339670939089 12857825412847754753204317)
  ·
    refine ⟨4821684529817908032451619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12857825412847754753204317 4821684529817908032451619)
    ·
      refine ⟨7232526794726862048677429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821684529817908032451619 7232526794726862048677429)
      ·
        refine ⟨678049387005643317063509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7232526794726862048677429 678049387005643317063509)
        ·
          refine ⟨3972945626986191310919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 678049387005643317063509 3972945626986191310919)
          ·
            rfl

theorem cell20_705060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 9].length) (baseStart_705060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705060 prefixEnd_705060 := by exact prefixLift 705060
  have htrace : WordTrace (prefixWord ++ tailWord_705060) baseStart_705060 baseEnd_705060 := by
    simpa [prefixWord, tailWord_705060, baseEnd_705060] using wordTrace_append hprefix tailTrace_705060
  have hstable : (prefixWord ++ tailWord_705060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705060).length < 2 ^ (prefixWord ++ tailWord_705060).sum := by decide
  have hdescent : baseEnd_705060 < baseStart_705060 := by decide
  rcases family_descends (prefixWord ++ tailWord_705060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705066 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_705066 : Nat := 118140960795 + 705066 * 2 ^ 59
def prefixEnd_705066 : Nat := 4983230072969 + 3 ^ 40 * 705066 * 2
def baseEnd_705066 : Nat := 321811334349372141984415

theorem tailTrace_705066 : CollatzResearch.WordTrace tailWord_705066 prefixEnd_705066 321811334349372141984415 := by
  unfold tailWord_705066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428967415918443132781763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17143913109115848354084701 6428967415918443132781763)
  ·
    refine ⟨9643451123877664699172645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6428967415918443132781763 9643451123877664699172645)
    ·
      refine ⟨1808147085727062131094871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9643451123877664699172645 1808147085727062131094871)
      ·
        refine ⟨2712220628590593196642307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808147085727062131094871 2712220628590593196642307)
        ·
          refine ⟨4068330942885889794963461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712220628590593196642307 4068330942885889794963461)
          ·
            refine ⟨762812051791104336555649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4068330942885889794963461 762812051791104336555649)
            ·
              refine ⟨572109038843328252416737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762812051791104336555649 572109038843328252416737)
              ·
                refine ⟨429081779132496189312553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572109038843328252416737 429081779132496189312553)
                ·
                  refine ⟨321811334349372141984415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429081779132496189312553 321811334349372141984415)
                  ·
                    rfl

theorem cell20_705066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_705066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705066 prefixEnd_705066 := by exact prefixLift 705066
  have htrace : WordTrace (prefixWord ++ tailWord_705066) baseStart_705066 baseEnd_705066 := by
    simpa [prefixWord, tailWord_705066, baseEnd_705066] using wordTrace_append hprefix tailTrace_705066
  have hstable : (prefixWord ++ tailWord_705066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705066).length < 2 ^ (prefixWord ++ tailWord_705066).sum := by decide
  have hdescent : baseEnd_705066 < baseStart_705066 := by decide
  rcases family_descends (prefixWord ++ tailWord_705066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705084 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_705084 : Nat := 118140960795 + 705084 * 2 ^ 59
def prefixEnd_705084 : Nat := 4983230072969 + 3 ^ 40 * 705084 * 2
def baseEnd_705084 : Nat := 321819550039844079384341

theorem tailTrace_705084 : CollatzResearch.WordTrace tailWord_705084 prefixEnd_705084 321819550039844079384341 := by
  unfold tailWord_705084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858263088804280802641153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17144350785072374403521537 12858263088804280802641153)
  ·
    refine ⟨9643697316603210601980865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12858263088804280802641153 9643697316603210601980865)
    ·
      refine ⟨7232772987452407951485649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9643697316603210601980865 7232772987452407951485649)
      ·
        refine ⟨5424579740589305963614237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7232772987452407951485649 5424579740589305963614237)
        ·
          refine ⟨2034217402720989736355339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5424579740589305963614237 2034217402720989736355339)
          ·
            refine ⟨3051326104081484604533009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034217402720989736355339 3051326104081484604533009)
            ·
              refine ⟨2288494578061113453399757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3051326104081484604533009 2288494578061113453399757)
              ·
                refine ⟨858185466772917545024909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2288494578061113453399757 858185466772917545024909)
                ·
                  refine ⟨321819550039844079384341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858185466772917545024909 321819550039844079384341)
                  ·
                    rfl

theorem cell20_705084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_705084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705084 prefixEnd_705084 := by exact prefixLift 705084
  have htrace : WordTrace (prefixWord ++ tailWord_705084) baseStart_705084 baseEnd_705084 := by
    simpa [prefixWord, tailWord_705084, baseEnd_705084] using wordTrace_append hprefix tailTrace_705084
  have hstable : (prefixWord ++ tailWord_705084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705084).length < 2 ^ (prefixWord ++ tailWord_705084).sum := by decide
  have hdescent : baseEnd_705084 < baseStart_705084 := by decide
  rcases family_descends (prefixWord ++ tailWord_705084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705108 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_705108 : Nat := 118140960795 + 705108 * 2 ^ 59
def prefixEnd_705108 : Nat := 4983230072969 + 3 ^ 40 * 705108 * 2
def baseEnd_705108 : Nat := 321830504293806662584243

theorem tailTrace_705108 : CollatzResearch.WordTrace tailWord_705108 prefixEnd_705108 321830504293806662584243 := by
  unfold tailWord_705108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858700764760806852077989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17144934353014409136103985 12858700764760806852077989)
  ·
    refine ⟨2411006393392651284764623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12858700764760806852077989 2411006393392651284764623)
    ·
      refine ⟨3616509590088976927146935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411006393392651284764623 3616509590088976927146935)
      ·
        refine ⟨5424764385133465390720403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616509590088976927146935 5424764385133465390720403)
        ·
          refine ⟨8137146577700198086080605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5424764385133465390720403 8137146577700198086080605)
          ·
            refine ⟨3051429966637574282280227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8137146577700198086080605 3051429966637574282280227)
            ·
              refine ⟨4577144949956361423420341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051429966637574282280227 4577144949956361423420341)
              ·
                refine ⟨429107339058408883445657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4577144949956361423420341 429107339058408883445657)
                ·
                  refine ⟨321830504293806662584243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429107339058408883445657 321830504293806662584243)
                  ·
                    rfl

theorem cell20_705108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_705108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705108 prefixEnd_705108 := by exact prefixLift 705108
  have htrace : WordTrace (prefixWord ++ tailWord_705108) baseStart_705108 baseEnd_705108 := by
    simpa [prefixWord, tailWord_705108, baseEnd_705108] using wordTrace_append hprefix tailTrace_705108
  have hstable : (prefixWord ++ tailWord_705108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705108).length < 2 ^ (prefixWord ++ tailWord_705108).sum := by decide
  have hdescent : baseEnd_705108 < baseStart_705108 := by decide
  rcases family_descends (prefixWord ++ tailWord_705108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705143 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_705143 : Nat := 118140960795 + 705143 * 2 ^ 59
def prefixEnd_705143 : Nat := 4983230072969 + 3 ^ 40 * 705143 * 2
def baseEnd_705143 : Nat := 321846479247502096417433

theorem tailTrace_705143 : CollatzResearch.WordTrace tailWord_705143 prefixEnd_705143 321846479247502096417433 := by
  unfold tailWord_705143
  simp only [CollatzResearch.WordTrace]
  refine ⟨25718678084394814681680083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17145785389596543121120055 25718678084394814681680083)
  ·
    refine ⟨38578017126592222022520125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25718678084394814681680083 38578017126592222022520125)
    ·
      refine ⟨14466756422472083258445047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38578017126592222022520125 14466756422472083258445047)
      ·
        refine ⟨21700134633708124887667571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14466756422472083258445047 21700134633708124887667571)
        ·
          refine ⟨32550201950562187331501357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21700134633708124887667571 32550201950562187331501357)
          ·
            refine ⟨12206325731460820249313009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32550201950562187331501357 12206325731460820249313009)
            ·
              refine ⟨9154744298595615186984757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12206325731460820249313009 9154744298595615186984757)
              ·
                refine ⟨858257277993338923779821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9154744298595615186984757 858257277993338923779821)
                ·
                  refine ⟨321846479247502096417433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858257277993338923779821 321846479247502096417433)
                  ·
                    rfl

theorem cell20_705143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_705143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705143 prefixEnd_705143 := by exact prefixLift 705143
  have htrace : WordTrace (prefixWord ++ tailWord_705143) baseStart_705143 baseEnd_705143 := by
    simpa [prefixWord, tailWord_705143, baseEnd_705143] using wordTrace_append hprefix tailTrace_705143
  have hstable : (prefixWord ++ tailWord_705143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705143).length < 2 ^ (prefixWord ++ tailWord_705143).sum := by decide
  have hdescent : baseEnd_705143 < baseStart_705143 := by decide
  rcases family_descends (prefixWord ++ tailWord_705143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705181 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_705181 : Nat := 118140960795 + 705181 * 2 ^ 59
def prefixEnd_705181 : Nat := 4983230072969 + 3 ^ 40 * 705181 * 2
def baseEnd_705181 : Nat := 321863823482942853150611

theorem tailTrace_705181 : CollatzResearch.WordTrace tailWord_705181 prefixEnd_705181 321863823482942853150611 := by
  unfold tailWord_705181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25720064058257147171563397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17146709372171431447708931 25720064058257147171563397)
  ·
    refine ⟨4822512010923215094668137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25720064058257147171563397 4822512010923215094668137)
    ·
      refine ⟨3616884008192411321001103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4822512010923215094668137 3616884008192411321001103)
      ·
        refine ⟨5425326012288616981501655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616884008192411321001103 5425326012288616981501655)
        ·
          refine ⟨8137989018432925472252483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425326012288616981501655 8137989018432925472252483)
          ·
            refine ⟨12206983527649388208378725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137989018432925472252483 12206983527649388208378725)
            ·
              refine ⟨2288809411434260289071011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12206983527649388208378725 2288809411434260289071011)
              ·
                refine ⟨3433214117151390433606517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288809411434260289071011 3433214117151390433606517)
                ·
                  refine ⟨321863823482942853150611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3433214117151390433606517 321863823482942853150611)
                  ·
                    rfl

theorem cell20_705181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_705181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705181 prefixEnd_705181 := by exact prefixLift 705181
  have htrace : WordTrace (prefixWord ++ tailWord_705181) baseStart_705181 baseEnd_705181 := by
    simpa [prefixWord, tailWord_705181, baseEnd_705181] using wordTrace_append hprefix tailTrace_705181
  have hstable : (prefixWord ++ tailWord_705181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705181).length < 2 ^ (prefixWord ++ tailWord_705181).sum := by decide
  have hdescent : baseEnd_705181 < baseStart_705181 := by decide
  rcases family_descends (prefixWord ++ tailWord_705181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705184 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_705184 : Nat := 118140960795 + 705184 * 2 ^ 59
def prefixEnd_705184 : Nat := 4983230072969 + 3 ^ 40 * 705184 * 2
def baseEnd_705184 : Nat := 321865192764688176050599

theorem tailTrace_705184 : CollatzResearch.WordTrace tailWord_705184 prefixEnd_705184 321865192764688176050599 := by
  unfold tailWord_705184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12860086738623139341961303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17146782318164185789281737 12860086738623139341961303)
  ·
    refine ⟨19290130107934709012941955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12860086738623139341961303 19290130107934709012941955)
    ·
      refine ⟨28935195161902063519412933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19290130107934709012941955 28935195161902063519412933)
      ·
        refine ⟨5425349092856636909889925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28935195161902063519412933 5425349092856636909889925)
        ·
          refine ⟨1017252954910619420604361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5425349092856636909889925 1017252954910619420604361)
          ·
            refine ⟨762939716182964565453271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017252954910619420604361 762939716182964565453271)
            ·
              refine ⟨1144409574274446848179907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762939716182964565453271 1144409574274446848179907)
              ·
                refine ⟨1716614361411670272269861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144409574274446848179907 1716614361411670272269861)
                ·
                  refine ⟨321865192764688176050599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716614361411670272269861 321865192764688176050599)
                  ·
                    rfl

theorem cell20_705184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_705184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705184 prefixEnd_705184 := by exact prefixLift 705184
  have htrace : WordTrace (prefixWord ++ tailWord_705184) baseStart_705184 baseEnd_705184 := by
    simpa [prefixWord, tailWord_705184, baseEnd_705184] using wordTrace_append hprefix tailTrace_705184
  have hstable : (prefixWord ++ tailWord_705184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705184).length < 2 ^ (prefixWord ++ tailWord_705184).sum := by decide
  have hdescent : baseEnd_705184 < baseStart_705184 := by decide
  rcases family_descends (prefixWord ++ tailWord_705184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705194 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_705194 : Nat := 118140960795 + 705194 * 2 ^ 59
def prefixEnd_705194 : Nat := 4983230072969 + 3 ^ 40 * 705194 * 2
def baseEnd_705194 : Nat := 321869757037172585717225

theorem tailTrace_705194 : CollatzResearch.WordTrace tailWord_705194 prefixEnd_705194 321869757037172585717225 := by
  unfold tailWord_705194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430134551802512597946659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17147025471473366927857757 6430134551802512597946659)
  ·
    refine ⟨9645201827703768896919989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6430134551802512597946659 9645201827703768896919989)
    ·
      refine ⟨904237671347228334086249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9645201827703768896919989 904237671347228334086249)
      ·
        refine ⟨678178253510421250564687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 904237671347228334086249 678178253510421250564687)
        ·
          refine ⟨1017267380265631875847031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678178253510421250564687 1017267380265631875847031)
          ·
            refine ⟨1525901070398447813770547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017267380265631875847031 1525901070398447813770547)
            ·
              refine ⟨2288851605597671720655821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525901070398447813770547 2288851605597671720655821)
              ·
                refine ⟨858319352099126895245933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2288851605597671720655821 858319352099126895245933)
                ·
                  refine ⟨321869757037172585717225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858319352099126895245933 321869757037172585717225)
                  ·
                    rfl

theorem cell20_705194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_705194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705194 prefixEnd_705194 := by exact prefixLift 705194
  have htrace : WordTrace (prefixWord ++ tailWord_705194) baseStart_705194 baseEnd_705194 := by
    simpa [prefixWord, tailWord_705194, baseEnd_705194] using wordTrace_append hprefix tailTrace_705194
  have hstable : (prefixWord ++ tailWord_705194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705194).length < 2 ^ (prefixWord ++ tailWord_705194).sum := by decide
  have hdescent : baseEnd_705194 < baseStart_705194 := by decide
  rcases family_descends (prefixWord ++ tailWord_705194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705229 : List Nat := [1, 6, 2, 1, 2, 8]
def baseStart_705229 : Nat := 118140960795 + 705229 * 2 ^ 59
def prefixEnd_705229 : Nat := 4983230072969 + 3 ^ 40 * 705229 * 2
def baseEnd_705229 : Nat := 11921693777439556279645

theorem tailTrace_705229 : CollatzResearch.WordTrace tailWord_705229 prefixEnd_705229 11921693777439556279645 := by
  unfold tailWord_705229
  simp only [CollatzResearch.WordTrace]
  refine ⟨25721814762083251369310741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17147876508055500912873827 25721814762083251369310741)
  ·
    refine ⟨1205710066972652407936441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25721814762083251369310741 1205710066972652407936441)
    ·
      refine ⟨904282550229489305952331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1205710066972652407936441 904282550229489305952331)
      ·
        refine ⟨1356423825344233958928497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904282550229489305952331 1356423825344233958928497)
        ·
          refine ⟨1017317869008175469196373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356423825344233958928497 1017317869008175469196373)
          ·
            refine ⟨11921693777439556279645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1017317869008175469196373 11921693777439556279645)
            ·
              rfl

theorem cell20_705229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 8].length) (baseStart_705229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705229 prefixEnd_705229 := by exact prefixLift 705229
  have htrace : WordTrace (prefixWord ++ tailWord_705229) baseStart_705229 baseEnd_705229 := by
    simpa [prefixWord, tailWord_705229, baseEnd_705229] using wordTrace_append hprefix tailTrace_705229
  have hstable : (prefixWord ++ tailWord_705229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705229).length < 2 ^ (prefixWord ++ tailWord_705229).sum := by decide
  have hdescent : baseEnd_705229 < baseStart_705229 := by decide
  rcases family_descends (prefixWord ++ tailWord_705229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705239 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 2]
def baseStart_705239 : Nat := 118140960795 + 705239 * 2 ^ 59
def prefixEnd_705239 : Nat := 4983230072969 + 3 ^ 40 * 705239 * 2
def baseEnd_705239 : Nat := 321890296263352429217041

theorem tailTrace_705239 : CollatzResearch.WordTrace tailWord_705239 prefixEnd_705239 321890296263352429217041 := by
  unfold tailWord_705239
  simp only [CollatzResearch.WordTrace]
  refine ⟨25722179492047023077174771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17148119661364682051449847 25722179492047023077174771)
  ·
    refine ⟨38583269238070534615762157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25722179492047023077174771 38583269238070534615762157)
    ·
      refine ⟨14468725964276450480910809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38583269238070534615762157 14468725964276450480910809)
      ·
        refine ⟨10851544473207337860683107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14468725964276450480910809 10851544473207337860683107)
        ·
          refine ⟨16277316709811006791024661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851544473207337860683107 16277316709811006791024661)
          ·
            refine ⟨762999220772390943329281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16277316709811006791024661 762999220772390943329281)
            ·
              refine ⟨572249415579293207496961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762999220772390943329281 572249415579293207496961)
              ·
                refine ⟨429187061684469905622721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572249415579293207496961 429187061684469905622721)
                ·
                  refine ⟨321890296263352429217041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429187061684469905622721 321890296263352429217041)
                  ·
                    rfl

theorem cell20_705239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2].length) (baseStart_705239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705239 prefixEnd_705239 := by exact prefixLift 705239
  have htrace : WordTrace (prefixWord ++ tailWord_705239) baseStart_705239 baseEnd_705239 := by
    simpa [prefixWord, tailWord_705239, baseEnd_705239] using wordTrace_append hprefix tailTrace_705239
  have hstable : (prefixWord ++ tailWord_705239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705239).length < 2 ^ (prefixWord ++ tailWord_705239).sum := by decide
  have hdescent : baseEnd_705239 < baseStart_705239 := by decide
  rcases family_descends (prefixWord ++ tailWord_705239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705257 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_705257 : Nat := 118140960795 + 705257 * 2 ^ 59
def prefixEnd_705257 : Nat := 4983230072969 + 3 ^ 40 * 705257 * 2
def baseEnd_705257 : Nat := 321898511953824366616967

theorem tailTrace_705257 : CollatzResearch.WordTrace tailWord_705257 prefixEnd_705257 321898511953824366616967 := by
  unfold tailWord_705257
  simp only [CollatzResearch.WordTrace]
  refine ⟨25722836005981812151330025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17148557337321208100886683 25722836005981812151330025)
  ·
    refine ⟨19292127004486359113497519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25722836005981812151330025 19292127004486359113497519)
    ·
      refine ⟨28938190506729538670246279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19292127004486359113497519 28938190506729538670246279)
      ·
        refine ⟨43407285760094308005369419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28938190506729538670246279 43407285760094308005369419)
        ·
          refine ⟨65110928640141462008054129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43407285760094308005369419 65110928640141462008054129)
          ·
            refine ⟨48833196480106096506040597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65110928640141462008054129 48833196480106096506040597)
            ·
              refine ⟨2289056085004973273720653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48833196480106096506040597 2289056085004973273720653)
              ·
                refine ⟨858396031876864977645245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2289056085004973273720653 858396031876864977645245)
                ·
                  refine ⟨321898511953824366616967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858396031876864977645245 321898511953824366616967)
                  ·
                    rfl

theorem cell20_705257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_705257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705257 prefixEnd_705257 := by exact prefixLift 705257
  have htrace : WordTrace (prefixWord ++ tailWord_705257) baseStart_705257 baseEnd_705257 := by
    simpa [prefixWord, tailWord_705257, baseEnd_705257] using wordTrace_append hprefix tailTrace_705257
  have hstable : (prefixWord ++ tailWord_705257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705257).length < 2 ^ (prefixWord ++ tailWord_705257).sum := by decide
  have hdescent : baseEnd_705257 < baseStart_705257 := by decide
  rcases family_descends (prefixWord ++ tailWord_705257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705264 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_705264 : Nat := 118140960795 + 705264 * 2 ^ 59
def prefixEnd_705264 : Nat := 4983230072969 + 3 ^ 40 * 705264 * 2
def baseEnd_705264 : Nat := 321901706944563453383605

theorem tailTrace_705264 : CollatzResearch.WordTrace tailWord_705264 prefixEnd_705264 321901706944563453383605 := by
  unfold tailWord_705264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861545658478226173417423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17148727544637634897889897 12861545658478226173417423)
  ·
    refine ⟨19292318487717339260126135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12861545658478226173417423 19292318487717339260126135)
    ·
      refine ⟨28938477731576008890189203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19292318487717339260126135 28938477731576008890189203)
      ·
        refine ⟨43407716597364013335283805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28938477731576008890189203 43407716597364013335283805)
        ·
          refine ⟨16277893724011505000731427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43407716597364013335283805 16277893724011505000731427)
          ·
            refine ⟨24416840586017257501097141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16277893724011505000731427 24416840586017257501097141)
            ·
              refine ⟨2289078804939117890727857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24416840586017257501097141 2289078804939117890727857)
              ·
                refine ⟨1716809103704338418045893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289078804939117890727857 1716809103704338418045893)
                ·
                  refine ⟨321901706944563453383605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716809103704338418045893 321901706944563453383605)
                  ·
                    rfl

theorem cell20_705264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_705264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705264 prefixEnd_705264 := by exact prefixLift 705264
  have htrace : WordTrace (prefixWord ++ tailWord_705264) baseStart_705264 baseEnd_705264 := by
    simpa [prefixWord, tailWord_705264, baseEnd_705264] using wordTrace_append hprefix tailTrace_705264
  have hstable : (prefixWord ++ tailWord_705264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705264).length < 2 ^ (prefixWord ++ tailWord_705264).sum := by decide
  have hdescent : baseEnd_705264 < baseStart_705264 := by decide
  rcases family_descends (prefixWord ++ tailWord_705264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705332 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_705332 : Nat := 118140960795 + 705332 * 2 ^ 59
def prefixEnd_705332 : Nat := 4983230072969 + 3 ^ 40 * 705332 * 2
def baseEnd_705332 : Nat := 321932743997457439116661

theorem tailTrace_705332 : CollatzResearch.WordTrace tailWord_705332 prefixEnd_705332 321932743997457439116661 := by
  unfold tailWord_705332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12862785740355049980155125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17150380987140066640206833 12862785740355049980155125)
  ·
    refine ⟨1205886163158285935639543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12862785740355049980155125 1205886163158285935639543)
    ·
      refine ⟨1808829244737428903459315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205886163158285935639543 1808829244737428903459315)
      ·
        refine ⟨2713243867106143355188973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808829244737428903459315 2713243867106143355188973)
        ·
          refine ⟨1017466450164803758195865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2713243867106143355188973 1017466450164803758195865)
          ·
            refine ⟨763099837623602818646899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017466450164803758195865 763099837623602818646899)
            ·
              refine ⟨1144649756435404227970349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763099837623602818646899 1144649756435404227970349)
              ·
                refine ⟨429243658663276585488881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1144649756435404227970349 429243658663276585488881)
                ·
                  refine ⟨321932743997457439116661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429243658663276585488881 321932743997457439116661)
                  ·
                    rfl

theorem cell20_705332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_705332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705332 prefixEnd_705332 := by exact prefixLift 705332
  have htrace : WordTrace (prefixWord ++ tailWord_705332) baseStart_705332 baseEnd_705332 := by
    simpa [prefixWord, tailWord_705332, baseEnd_705332] using wordTrace_append hprefix tailTrace_705332
  have hstable : (prefixWord ++ tailWord_705332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705332).length < 2 ^ (prefixWord ++ tailWord_705332).sum := by decide
  have hdescent : baseEnd_705332 < baseStart_705332 := by decide
  rcases family_descends (prefixWord ++ tailWord_705332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705333 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_705333 : Nat := 118140960795 + 705333 * 2 ^ 59
def prefixEnd_705333 : Nat := 4983230072969 + 3 ^ 40 * 705333 * 2
def baseEnd_705333 : Nat := 321933200424705880083323

theorem tailTrace_705333 : CollatzResearch.WordTrace tailWord_705333 prefixEnd_705333 321933200424705880083323 := by
  unfold tailWord_705333
  simp only [CollatzResearch.WordTrace]
  refine ⟨25725607953706477131096653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17150405302470984754064435 25725607953706477131096653)
  ·
    refine ⟨9647102982639928924161245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25725607953706477131096653 9647102982639928924161245)
    ·
      refine ⟨3617663618489973346560467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9647102982639928924161245 3617663618489973346560467)
      ·
        refine ⟨5426495427734960019840701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617663618489973346560467 5426495427734960019840701)
        ·
          refine ⟨2034935785400610007440263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5426495427734960019840701 2034935785400610007440263)
          ·
            refine ⟨3052403678100915011160395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034935785400610007440263 3052403678100915011160395)
            ·
              refine ⟨4578605517151372516740593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052403678100915011160395 4578605517151372516740593)
              ·
                refine ⟨3433954137863529387555445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578605517151372516740593 3433954137863529387555445)
                ·
                  refine ⟨321933200424705880083323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3433954137863529387555445 321933200424705880083323)
                  ·
                    rfl

theorem cell20_705333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_705333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705333 prefixEnd_705333 := by exact prefixLift 705333
  have htrace : WordTrace (prefixWord ++ tailWord_705333) baseStart_705333 baseEnd_705333 := by
    simpa [prefixWord, tailWord_705333, baseEnd_705333] using wordTrace_append hprefix tailTrace_705333
  have hstable : (prefixWord ++ tailWord_705333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705333).length < 2 ^ (prefixWord ++ tailWord_705333).sum := by decide
  have hdescent : baseEnd_705333 < baseStart_705333 := by decide
  rcases family_descends (prefixWord ++ tailWord_705333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705367 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 3]
def baseStart_705367 : Nat := 118140960795 + 705367 * 2 ^ 59
def prefixEnd_705367 : Nat := 4983230072969 + 3 ^ 40 * 705367 * 2
def baseEnd_705367 : Nat := 321948718951152872949851

theorem tailTrace_705367 : CollatzResearch.WordTrace tailWord_705367 prefixEnd_705367 321948718951152872949851 := by
  unfold tailWord_705367
  simp only [CollatzResearch.WordTrace]
  refine ⟨25726848035583300937834355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17151232023722200625222903 25726848035583300937834355)
  ·
    refine ⟨38590272053374951406751533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25726848035583300937834355 38590272053374951406751533)
    ·
      refine ⟨14471352020015606777531825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38590272053374951406751533 14471352020015606777531825)
      ·
        refine ⟨10853514015011705083148869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14471352020015606777531825 10853514015011705083148869)
        ·
          refine ⟨2035033877814694703090413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10853514015011705083148869 2035033877814694703090413)
          ·
            refine ⟨763137704180510513658905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2035033877814694703090413 763137704180510513658905)
            ·
              refine ⟨572353278135382885244179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763137704180510513658905 572353278135382885244179)
              ·
                refine ⟨858529917203074327866269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572353278135382885244179 858529917203074327866269)
                ·
                  refine ⟨321948718951152872949851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858529917203074327866269 321948718951152872949851)
                  ·
                    rfl

theorem cell20_705367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_705367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705367 prefixEnd_705367 := by exact prefixLift 705367
  have htrace : WordTrace (prefixWord ++ tailWord_705367) baseStart_705367 baseEnd_705367 := by
    simpa [prefixWord, tailWord_705367, baseEnd_705367] using wordTrace_append hprefix tailTrace_705367
  have hstable : (prefixWord ++ tailWord_705367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705367).length < 2 ^ (prefixWord ++ tailWord_705367).sum := by decide
  have hdescent : baseEnd_705367 < baseStart_705367 := by decide
  rcases family_descends (prefixWord ++ tailWord_705367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705392 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_705392 : Nat := 118140960795 + 705392 * 2 ^ 59
def prefixEnd_705392 : Nat := 4983230072969 + 3 ^ 40 * 705392 * 2
def baseEnd_705392 : Nat := 321960129632363897116415

theorem tailTrace_705392 : CollatzResearch.WordTrace tailWord_705392 prefixEnd_705392 321960129632363897116415 := by
  unfold tailWord_705392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863879930246365103747215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17151839906995153471662953 12863879930246365103747215)
  ·
    refine ⟨19295819895369547655620823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12863879930246365103747215 19295819895369547655620823)
    ·
      refine ⟨28943729843054321483431235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19295819895369547655620823 28943729843054321483431235)
      ·
        refine ⟨43415594764581482225146853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28943729843054321483431235 43415594764581482225146853)
        ·
          refine ⟨8140424018359027917215035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43415594764581482225146853 8140424018359027917215035)
          ·
            refine ⟨12210636027538541875822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140424018359027917215035 12210636027538541875822553)
            ·
              refine ⟨9157977020653906406866915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12210636027538541875822553 9157977020653906406866915)
              ·
                refine ⟨13736965530980859610300373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157977020653906406866915 13736965530980859610300373)
                ·
                  refine ⟨321960129632363897116415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13736965530980859610300373 321960129632363897116415)
                  ·
                    rfl

theorem cell20_705392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_705392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705392 prefixEnd_705392 := by exact prefixLift 705392
  have htrace : WordTrace (prefixWord ++ tailWord_705392) baseStart_705392 baseEnd_705392 := by
    simpa [prefixWord, tailWord_705392, baseEnd_705392] using wordTrace_append hprefix tailTrace_705392
  have hstable : (prefixWord ++ tailWord_705392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705392).length < 2 ^ (prefixWord ++ tailWord_705392).sum := by decide
  have hdescent : baseEnd_705392 < baseStart_705392 := by decide
  rcases family_descends (prefixWord ++ tailWord_705392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705460 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_705460 : Nat := 118140960795 + 705460 * 2 ^ 59
def prefixEnd_705460 : Nat := 4983230072969 + 3 ^ 40 * 705460 * 2
def baseEnd_705460 : Nat := 321991166685257882849471

theorem tailTrace_705460 : CollatzResearch.WordTrace tailWord_705460 prefixEnd_705460 321991166685257882849471 := by
  unfold tailWord_705460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865120012123188910484917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17153493349497585213979889 12865120012123188910484917)
  ·
    refine ⟨1206105001136548960357961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12865120012123188910484917 1206105001136548960357961)
    ·
      refine ⟨904578750852411720268471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206105001136548960357961 904578750852411720268471)
      ·
        refine ⟨1356868126278617580402707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904578750852411720268471 1356868126278617580402707)
        ·
          refine ⟨2035302189417926370604061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356868126278617580402707 2035302189417926370604061)
          ·
            refine ⟨763238321031722388976523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2035302189417926370604061 763238321031722388976523)
            ·
              refine ⟨1144857481547583583464785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763238321031722388976523 1144857481547583583464785)
              ·
                refine ⟨858643111160687687598589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144857481547583583464785 858643111160687687598589)
                ·
                  refine ⟨321991166685257882849471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858643111160687687598589 321991166685257882849471)
                  ·
                    rfl

theorem cell20_705460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_705460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705460 prefixEnd_705460 := by exact prefixLift 705460
  have htrace : WordTrace (prefixWord ++ tailWord_705460) baseStart_705460 baseEnd_705460 := by
    simpa [prefixWord, tailWord_705460, baseEnd_705460] using wordTrace_append hprefix tailTrace_705460
  have hstable : (prefixWord ++ tailWord_705460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705460).length < 2 ^ (prefixWord ++ tailWord_705460).sum := by decide
  have hdescent : baseEnd_705460 < baseStart_705460 := by decide
  rcases family_descends (prefixWord ++ tailWord_705460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705461 : List Nat := [1, 3, 3, 2, 1, 1, 9]
def baseStart_705461 : Nat := 118140960795 + 705461 * 2 ^ 59
def prefixEnd_705461 : Nat := 4983230072969 + 3 ^ 40 * 705461 * 2
def baseEnd_705461 : Nat := 35776847012500702646237

theorem tailTrace_705461 : CollatzResearch.WordTrace tailWord_705461 prefixEnd_705461 35776847012500702646237 := by
  unfold tailWord_705461
  simp only [CollatzResearch.WordTrace]
  refine ⟨25730276497242754991756237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17153517664828503327837491 25730276497242754991756237)
  ·
    refine ⟨9648853686466033121908589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25730276497242754991756237 9648853686466033121908589)
    ·
      refine ⟨3618320132424762420715721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9648853686466033121908589 3618320132424762420715721)
      ·
        refine ⟨2713740099318571815536791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3618320132424762420715721 2713740099318571815536791)
        ·
          refine ⟨4070610148977857723305187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713740099318571815536791 4070610148977857723305187)
          ·
            refine ⟨6105915223466786584957781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070610148977857723305187 6105915223466786584957781)
            ·
              refine ⟨35776847012500702646237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6105915223466786584957781 35776847012500702646237)
              ·
                rfl

theorem cell20_705461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_705461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705461 prefixEnd_705461 := by exact prefixLift 705461
  have htrace : WordTrace (prefixWord ++ tailWord_705461) baseStart_705461 baseEnd_705461 := by
    simpa [prefixWord, tailWord_705461, baseEnd_705461] using wordTrace_append hprefix tailTrace_705461
  have hstable : (prefixWord ++ tailWord_705461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705461).length < 2 ^ (prefixWord ++ tailWord_705461).sum := by decide
  have hdescent : baseEnd_705461 < baseStart_705461 := by decide
  rcases family_descends (prefixWord ++ tailWord_705461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705464 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_705464 : Nat := 118140960795 + 705464 * 2 ^ 59
def prefixEnd_705464 : Nat := 4983230072969 + 3 ^ 40 * 705464 * 2
def baseEnd_705464 : Nat := 321992992394251646716121

theorem tailTrace_705464 : CollatzResearch.WordTrace tailWord_705464 prefixEnd_705464 321992992394251646716121 := by
  unfold tailWord_705464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865192958115943252057723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17153590610821257669410297 12865192958115943252057723)
  ·
    refine ⟨19297789437173914878086585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12865192958115943252057723 19297789437173914878086585)
    ·
      refine ⟨14473342077880436158564939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19297789437173914878086585 14473342077880436158564939)
      ·
        refine ⟨21710013116820654237847409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14473342077880436158564939 21710013116820654237847409)
        ·
          refine ⟨16282509837615490678385557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21710013116820654237847409 16282509837615490678385557)
          ·
            refine ⟨763242648638226125549323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16282509837615490678385557 763242648638226125549323)
            ·
              refine ⟨1144863972957339188323985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763242648638226125549323 1144863972957339188323985)
              ·
                refine ⟨858647979718004391242989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144863972957339188323985 858647979718004391242989)
                ·
                  refine ⟨321992992394251646716121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858647979718004391242989 321992992394251646716121)
                  ·
                    rfl

theorem cell20_705464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_705464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705464 prefixEnd_705464 := by exact prefixLift 705464
  have htrace : WordTrace (prefixWord ++ tailWord_705464) baseStart_705464 baseEnd_705464 := by
    simpa [prefixWord, tailWord_705464, baseEnd_705464] using wordTrace_append hprefix tailTrace_705464
  have hstable : (prefixWord ++ tailWord_705464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705464).length < 2 ^ (prefixWord ++ tailWord_705464).sum := by decide
  have hdescent : baseEnd_705464 < baseStart_705464 := by decide
  rcases family_descends (prefixWord ++ tailWord_705464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705475 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_705475 : Nat := 118140960795 + 705475 * 2 ^ 59
def prefixEnd_705475 : Nat := 4983230072969 + 3 ^ 40 * 705475 * 2
def baseEnd_705475 : Nat := 321998013093984497349409

theorem tailTrace_705475 : CollatzResearch.WordTrace tailWord_705475 prefixEnd_705475 321998013093984497349409 := by
  unfold tailWord_705475
  simp only [CollatzResearch.WordTrace]
  refine ⟨25730787119192035382765879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17153858079461356921843919 25730787119192035382765879)
  ·
    refine ⟨38596180678788053074148819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25730787119192035382765879 38596180678788053074148819)
    ·
      refine ⟨57894271018182079611223229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38596180678788053074148819 57894271018182079611223229)
      ·
        refine ⟨21710351631818279854208711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57894271018182079611223229 21710351631818279854208711)
        ·
          refine ⟨32565527447727419781313067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21710351631818279854208711 32565527447727419781313067)
          ·
            refine ⟨48848291171591129671969601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32565527447727419781313067 48848291171591129671969601)
            ·
              refine ⟨36636218378693347253977201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48848291171591129671969601 36636218378693347253977201)
              ·
                refine ⟨27477163784020010440482901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36636218378693347253977201 27477163784020010440482901)
                ·
                  refine ⟨321998013093984497349409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27477163784020010440482901 321998013093984497349409)
                  ·
                    rfl

theorem cell20_705475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_705475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705475 prefixEnd_705475 := by exact prefixLift 705475
  have htrace : WordTrace (prefixWord ++ tailWord_705475) baseStart_705475 baseEnd_705475 := by
    simpa [prefixWord, tailWord_705475, baseEnd_705475] using wordTrace_append hprefix tailTrace_705475
  have hstable : (prefixWord ++ tailWord_705475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705475).length < 2 ^ (prefixWord ++ tailWord_705475).sum := by decide
  have hdescent : baseEnd_705475 < baseStart_705475 := by decide
  rcases family_descends (prefixWord ++ tailWord_705475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705522 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_705522 : Nat := 118140960795 + 705522 * 2 ^ 59
def prefixEnd_705522 : Nat := 4983230072969 + 3 ^ 40 * 705522 * 2
def baseEnd_705522 : Nat := 322019465174661222782551

theorem tailTrace_705522 : CollatzResearch.WordTrace tailWord_705522 prefixEnd_705522 322019465174661222782551 := by
  unfold tailWord_705522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433125337505440602431705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17155000900014508273151213 6433125337505440602431705)
  ·
    refine ⟨4824844003129080451823779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6433125337505440602431705 4824844003129080451823779)
    ·
      refine ⟨7237266004693620677735669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824844003129080451823779 7237266004693620677735669)
      ·
        refine ⟨678493687940026938537719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7237266004693620677735669 678493687940026938537719)
        ·
          refine ⟨1017740531910040407806579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678493687940026938537719 1017740531910040407806579)
          ·
            refine ⟨1526610797865060611709869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017740531910040407806579 1526610797865060611709869)
            ·
              refine ⟨572479049199397729391201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1526610797865060611709869 572479049199397729391201)
              ·
                refine ⟨429359286899548297043401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572479049199397729391201 429359286899548297043401)
                ·
                  refine ⟨322019465174661222782551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429359286899548297043401 322019465174661222782551)
                  ·
                    rfl

theorem cell20_705522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_705522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705522 prefixEnd_705522 := by exact prefixLift 705522
  have htrace : WordTrace (prefixWord ++ tailWord_705522) baseStart_705522 baseEnd_705522 := by
    simpa [prefixWord, tailWord_705522, baseEnd_705522] using wordTrace_append hprefix tailTrace_705522
  have hstable : (prefixWord ++ tailWord_705522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705522).length < 2 ^ (prefixWord ++ tailWord_705522).sum := by decide
  have hdescent : baseEnd_705522 < baseStart_705522 := by decide
  rcases family_descends (prefixWord ++ tailWord_705522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705526 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_705526 : Nat := 118140960795 + 705526 * 2 ^ 59
def prefixEnd_705526 : Nat := 4983230072969 + 3 ^ 40 * 705526 * 2
def baseEnd_705526 : Nat := 322021290883654986649201

theorem tailTrace_705526 : CollatzResearch.WordTrace tailWord_705526 prefixEnd_705526 322021290883654986649201 := by
  unfold tailWord_705526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608290452625454443304527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17155098161338180728581621 1608290452625454443304527)
  ·
    refine ⟨2412435678938181664956791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1608290452625454443304527 2412435678938181664956791)
    ·
      refine ⟨3618653518407272497435187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412435678938181664956791 3618653518407272497435187)
      ·
        refine ⟨5427980277610908746152781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618653518407272497435187 5427980277610908746152781)
        ·
          refine ⟨2035492604104090779807293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5427980277610908746152781 2035492604104090779807293)
          ·
            refine ⟨763309726539034042427735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2035492604104090779807293 763309726539034042427735)
            ·
              refine ⟨1144964589808551063641603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763309726539034042427735 1144964589808551063641603)
              ·
                refine ⟨1717446884712826595462405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144964589808551063641603 1717446884712826595462405)
                ·
                  refine ⟨322021290883654986649201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717446884712826595462405 322021290883654986649201)
                  ·
                    rfl

theorem cell20_705526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_705526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705526 prefixEnd_705526 := by exact prefixLift 705526
  have htrace : WordTrace (prefixWord ++ tailWord_705526) baseStart_705526 baseEnd_705526 := by
    simpa [prefixWord, tailWord_705526, baseEnd_705526] using wordTrace_append hprefix tailTrace_705526
  have hstable : (prefixWord ++ tailWord_705526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705526).length < 2 ^ (prefixWord ++ tailWord_705526).sum := by decide
  have hdescent : baseEnd_705526 < baseStart_705526 := by decide
  rcases family_descends (prefixWord ++ tailWord_705526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705537 : List Nat := [1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_705537 : Nat := 118140960795 + 705537 * 2 ^ 59
def prefixEnd_705537 : Nat := 4983230072969 + 3 ^ 40 * 705537 * 2
def baseEnd_705537 : Nat := 107342103861129279094163

theorem tailTrace_705537 : CollatzResearch.WordTrace tailWord_705537 prefixEnd_705537 107342103861129279094163 := by
  unfold tailWord_705537
  simp only [CollatzResearch.WordTrace]
  refine ⟨25733048444967419971522865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17155365629978279981015243 25733048444967419971522865)
  ·
    refine ⟨19299786333725564978642149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25733048444967419971522865 19299786333725564978642149)
    ·
      refine ⟨3618709937573543433495403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19299786333725564978642149 3618709937573543433495403)
      ·
        refine ⟨5428064906360315150243105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618709937573543433495403 5428064906360315150243105)
        ·
          refine ⟨4071048679770236362682329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5428064906360315150243105 4071048679770236362682329)
          ·
            refine ⟨3053286509827677272011747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071048679770236362682329 3053286509827677272011747)
            ·
              refine ⟨4579929764741515908017621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053286509827677272011747 4579929764741515908017621)
              ·
                refine ⟨107342103861129279094163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4579929764741515908017621 107342103861129279094163)
                ·
                  rfl

theorem cell20_705537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_705537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705537 prefixEnd_705537 := by exact prefixLift 705537
  have htrace : WordTrace (prefixWord ++ tailWord_705537) baseStart_705537 baseEnd_705537 := by
    simpa [prefixWord, tailWord_705537, baseEnd_705537] using wordTrace_append hprefix tailTrace_705537
  have hstable : (prefixWord ++ tailWord_705537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705537).length < 2 ^ (prefixWord ++ tailWord_705537).sum := by decide
  have hdescent : baseEnd_705537 < baseStart_705537 := by decide
  rcases family_descends (prefixWord ++ tailWord_705537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705585 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 2]
def baseStart_705585 : Nat := 118140960795 + 705585 * 2 ^ 59
def prefixEnd_705585 : Nat := 4983230072969 + 3 ^ 40 * 705585 * 2
def baseEnd_705585 : Nat := 322048220091313003682293

theorem tailTrace_705585 : CollatzResearch.WordTrace tailWord_705585 prefixEnd_705585 322048220091313003682293 := by
  unfold tailWord_705585
  simp only [CollatzResearch.WordTrace]
  refine ⟨25734799148793524169270209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17156532765862349446180139 25734799148793524169270209)
  ·
    refine ⟨19301099361595143126952657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25734799148793524169270209 19301099361595143126952657)
    ·
      refine ⟨14475824521196357345214493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19301099361595143126952657 14475824521196357345214493)
      ·
        refine ⟨5428434195448634004455435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14475824521196357345214493 5428434195448634004455435)
        ·
          refine ⟨8142651293172951006683153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428434195448634004455435 8142651293172951006683153)
          ·
            refine ⟨6106988469879713255012365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142651293172951006683153 6106988469879713255012365)
            ·
              refine ⟨2290120676204892470629637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6106988469879713255012365 2290120676204892470629637)
              ·
                refine ⟨429397626788417338243057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2290120676204892470629637 429397626788417338243057)
                ·
                  refine ⟨322048220091313003682293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429397626788417338243057 322048220091313003682293)
                  ·
                    rfl

theorem cell20_705585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_705585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705585 prefixEnd_705585 := by exact prefixLift 705585
  have htrace : WordTrace (prefixWord ++ tailWord_705585) baseStart_705585 baseEnd_705585 := by
    simpa [prefixWord, tailWord_705585, baseEnd_705585] using wordTrace_append hprefix tailTrace_705585
  have hstable : (prefixWord ++ tailWord_705585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705585).length < 2 ^ (prefixWord ++ tailWord_705585).sum := by decide
  have hdescent : baseEnd_705585 < baseStart_705585 := by decide
  rcases family_descends (prefixWord ++ tailWord_705585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705592 : List Nat := [2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_705592 : Nat := 118140960795 + 705592 * 2 ^ 59
def prefixEnd_705592 : Nat := 4983230072969 + 3 ^ 40 * 705592 * 2
def baseEnd_705592 : Nat := 107350471694017363482977

theorem tailTrace_705592 : CollatzResearch.WordTrace tailWord_705592 prefixEnd_705592 107350471694017363482977 := by
  unfold tailWord_705592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12867527229884082182387515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17156702973178776243183353 12867527229884082182387515)
  ·
    refine ⟨19301290844826123273581273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12867527229884082182387515 19301290844826123273581273)
    ·
      refine ⟨14475968133619592455185955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19301290844826123273581273 14475968133619592455185955)
      ·
        refine ⟨21713952200429388682778933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14475968133619592455185955 21713952200429388682778933)
        ·
          refine ⟨2035683018790255189010525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21713952200429388682778933 2035683018790255189010525)
          ·
            refine ⟨763381132046345695878947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2035683018790255189010525 763381132046345695878947)
            ·
              refine ⟨1145071698069518543818421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763381132046345695878947 1145071698069518543818421)
              ·
                refine ⟨107350471694017363482977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145071698069518543818421 107350471694017363482977)
                ·
                  rfl

theorem cell20_705592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_705592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705592 prefixEnd_705592 := by exact prefixLift 705592
  have htrace : WordTrace (prefixWord ++ tailWord_705592) baseStart_705592 baseEnd_705592 := by
    simpa [prefixWord, tailWord_705592, baseEnd_705592] using wordTrace_append hprefix tailTrace_705592
  have hstable : (prefixWord ++ tailWord_705592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705592).length < 2 ^ (prefixWord ++ tailWord_705592).sum := by decide
  have hdescent : baseEnd_705592 < baseStart_705592 := by decide
  rcases family_descends (prefixWord ++ tailWord_705592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705640 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_705640 : Nat := 118140960795 + 705640 * 2 ^ 59
def prefixEnd_705640 : Nat := 4983230072969 + 3 ^ 40 * 705640 * 2
def baseEnd_705640 : Nat := 322073323589977256848735

theorem tailTrace_705640 : CollatzResearch.WordTrace tailWord_705640 prefixEnd_705640 322073323589977256848735 := by
  unfold tailWord_705640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868402581797134281261187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17157870109062845708348249 12868402581797134281261187)
  ·
    refine ⟨19302603872695701421891781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12868402581797134281261187 19302603872695701421891781)
    ·
      refine ⟨3619238226130444016604709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19302603872695701421891781 3619238226130444016604709)
      ·
        refine ⟨678607167399458253113383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3619238226130444016604709 678607167399458253113383)
        ·
          refine ⟨1017910751099187379670075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678607167399458253113383 1017910751099187379670075)
          ·
            refine ⟨1526866126648781069505113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017910751099187379670075 1526866126648781069505113)
            ·
              refine ⟨1145149594986585802128835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526866126648781069505113 1145149594986585802128835)
              ·
                refine ⟨1717724392479878703193253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145149594986585802128835 1717724392479878703193253)
                ·
                  refine ⟨322073323589977256848735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717724392479878703193253 322073323589977256848735)
                  ·
                    rfl

theorem cell20_705640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_705640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705640 prefixEnd_705640 := by exact prefixLift 705640
  have htrace : WordTrace (prefixWord ++ tailWord_705640) baseStart_705640 baseEnd_705640 := by
    simpa [prefixWord, tailWord_705640, baseEnd_705640] using wordTrace_append hprefix tailTrace_705640
  have hstable : (prefixWord ++ tailWord_705640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705640).length < 2 ^ (prefixWord ++ tailWord_705640).sum := by decide
  have hdescent : baseEnd_705640 < baseStart_705640 := by decide
  rcases family_descends (prefixWord ++ tailWord_705640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705644 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_705644 : Nat := 118140960795 + 705644 * 2 ^ 59
def prefixEnd_705644 : Nat := 4983230072969 + 3 ^ 40 * 705644 * 2
def baseEnd_705644 : Nat := 322075149298971020715385

theorem tailTrace_705644 : CollatzResearch.WordTrace tailWord_705644 prefixEnd_705644 322075149298971020715385 := by
  unfold tailWord_705644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868475527789888622833993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17157967370386518163778657 12868475527789888622833993)
  ·
    refine ⟨9651356645842416467125495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12868475527789888622833993 9651356645842416467125495)
    ·
      refine ⟨14477034968763624700688243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9651356645842416467125495 14477034968763624700688243)
      ·
        refine ⟨21715552453145437051032365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14477034968763624700688243 21715552453145437051032365)
        ·
          refine ⟨8143332169929538894137137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21715552453145437051032365 8143332169929538894137137)
          ·
            refine ⟨6107499127447154170602853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8143332169929538894137137 6107499127447154170602853)
            ·
              refine ⟨1145156086396341406988035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6107499127447154170602853 1145156086396341406988035)
              ·
                refine ⟨1717734129594512110482053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145156086396341406988035 1717734129594512110482053)
                ·
                  refine ⟨322075149298971020715385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717734129594512110482053 322075149298971020715385)
                  ·
                    rfl

theorem cell20_705644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_705644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705644 prefixEnd_705644 := by exact prefixLift 705644
  have htrace : WordTrace (prefixWord ++ tailWord_705644) baseStart_705644 baseEnd_705644 := by
    simpa [prefixWord, tailWord_705644, baseEnd_705644] using wordTrace_append hprefix tailTrace_705644
  have hstable : (prefixWord ++ tailWord_705644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705644).length < 2 ^ (prefixWord ++ tailWord_705644).sum := by decide
  have hdescent : baseEnd_705644 < baseStart_705644 := by decide
  rcases family_descends (prefixWord ++ tailWord_705644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705668 : List Nat := [2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_705668 : Nat := 118140960795 + 705668 * 2 ^ 59
def prefixEnd_705668 : Nat := 4983230072969 + 3 ^ 40 * 705668 * 2
def baseEnd_705668 : Nat := 107362034517644534638429

theorem tailTrace_705668 : CollatzResearch.WordTrace tailWord_705668 prefixEnd_705668 107362034517644534638429 := by
  unfold tailWord_705668
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868913203746414672270829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17158550938328552896361105 12868913203746414672270829)
  ·
    refine ⟨4825842451404905502101561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12868913203746414672270829 4825842451404905502101561)
    ·
      refine ⟨3619381838553679126576171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4825842451404905502101561 3619381838553679126576171)
      ·
        refine ⟨5429072757830518689864257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619381838553679126576171 5429072757830518689864257)
        ·
          refine ⟨4071804568372889017398193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429072757830518689864257 4071804568372889017398193)
          ·
            refine ⟨3053853426279666763048645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071804568372889017398193 3053853426279666763048645)
            ·
              refine ⟨572597517427437518071621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3053853426279666763048645 572597517427437518071621)
              ·
                refine ⟨107362034517644534638429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572597517427437518071621 107362034517644534638429)
                ·
                  rfl

theorem cell20_705668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_705668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705668 prefixEnd_705668 := by exact prefixLift 705668
  have htrace : WordTrace (prefixWord ++ tailWord_705668) baseStart_705668 baseEnd_705668 := by
    simpa [prefixWord, tailWord_705668, baseEnd_705668] using wordTrace_append hprefix tailTrace_705668
  have hstable : (prefixWord ++ tailWord_705668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705668).length < 2 ^ (prefixWord ++ tailWord_705668).sum := by decide
  have hdescent : baseEnd_705668 < baseStart_705668 := by decide
  rcases family_descends (prefixWord ++ tailWord_705668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
