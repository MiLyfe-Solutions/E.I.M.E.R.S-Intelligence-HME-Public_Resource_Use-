import V185TrunkScan23Chunk0705

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4173834 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_4173834 : Nat := 118140960795 + 4173834 * 2 ^ 59
def prefixEnd_4173834 : Nat := 4983230072969 + 3 ^ 40 * 4173834 * 2
def baseEnd_4173834 : Nat := 714394338026042696326631

theorem tailTrace_4173834 : CollatzResearch.WordTrace tailWord_4173834 prefixEnd_4173834 714394338026042696326631 := by
  unfold tailWord_4173834
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058058090229931735172139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101488154907279817960459037 38058058090229931735172139)
  ·
    refine ⟨57087087135344897602758209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38058058090229931735172139 57087087135344897602758209)
    ·
      refine ⟨42815315351508673202068657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57087087135344897602758209 42815315351508673202068657)
      ·
        refine ⟨32111486513631504901551493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42815315351508673202068657 32111486513631504901551493)
        ·
          refine ⟨6020903721305907169040905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32111486513631504901551493 6020903721305907169040905)
          ·
            refine ⟨4515677790979430376780679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020903721305907169040905 4515677790979430376780679)
            ·
              refine ⟨6773516686469145565171019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515677790979430376780679 6773516686469145565171019)
              ·
                refine ⟨10160275029703718347756529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773516686469145565171019 10160275029703718347756529)
                ·
                  refine ⟨7620206272277788760817397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160275029703718347756529 7620206272277788760817397)
                  ·
                    refine ⟨714394338026042696326631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7620206272277788760817397 714394338026042696326631)
                    ·
                      rfl

theorem cell23_4173834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_4173834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173834 prefixEnd_4173834 := by exact prefixLift 4173834
  have htrace : WordTrace (prefixWord ++ tailWord_4173834) baseStart_4173834 baseEnd_4173834 := by
    simpa [prefixWord, tailWord_4173834, baseEnd_4173834] using wordTrace_append hprefix tailTrace_4173834
  have hstable : (prefixWord ++ tailWord_4173834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173834).length < 2 ^ (prefixWord ++ tailWord_4173834).sum := by decide
  have hdescent : baseEnd_4173834 < baseStart_4173834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173840 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_4173840 : Nat := 118140960795 + 4173840 * 2 ^ 59
def prefixEnd_4173840 : Nat := 4983230072969 + 3 ^ 40 * 4173840 * 2
def baseEnd_4173840 : Nat := 2143186094962055065504865

theorem tailTrace_4173840 : CollatzResearch.WordTrace tailWord_4173840 prefixEnd_4173840 2143186094962055065504865 := by
  unfold tailWord_4173840
  simp only [CollatzResearch.WordTrace]
  refine ⟨76116225599448994982703487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101488300799265326643604649 76116225599448994982703487)
  ·
    refine ⟨114174338399173492474055231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76116225599448994982703487 114174338399173492474055231)
    ·
      refine ⟨171261507598760238711082847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114174338399173492474055231 171261507598760238711082847)
      ·
        refine ⟨256892261398140358066624271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171261507598760238711082847 256892261398140358066624271)
        ·
          refine ⟨385338392097210537099936407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256892261398140358066624271 385338392097210537099936407)
          ·
            refine ⟨578007588145815805649904611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385338392097210537099936407 578007588145815805649904611)
            ·
              refine ⟨867011382218723708474856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578007588145815805649904611 867011382218723708474856917)
              ·
                refine ⟨20320579270751336917379459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 867011382218723708474856917 20320579270751336917379459)
                ·
                  refine ⟨30480868906127005376069189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20320579270751336917379459 30480868906127005376069189)
                  ·
                    refine ⟨5715162919898813508012973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30480868906127005376069189 5715162919898813508012973)
                    ·
                      refine ⟨2143186094962055065504865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5715162919898813508012973 2143186094962055065504865)
                      ·
                        rfl

theorem cell23_4173840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_4173840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173840 prefixEnd_4173840 := by exact prefixLift 4173840
  have htrace : WordTrace (prefixWord ++ tailWord_4173840) baseStart_4173840 baseEnd_4173840 := by
    simpa [prefixWord, tailWord_4173840, baseEnd_4173840] using wordTrace_append hprefix tailTrace_4173840
  have hstable : (prefixWord ++ tailWord_4173840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173840).length < 2 ^ (prefixWord ++ tailWord_4173840).sum := by decide
  have hdescent : baseEnd_4173840 < baseStart_4173840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173850 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4173850 : Nat := 118140960795 + 4173850 * 2 ^ 59
def prefixEnd_4173850 : Nat := 4983230072969 + 3 ^ 40 * 4173850 * 2
def baseEnd_4173850 : Nat := 2143191229768600026379819

theorem tailTrace_4173850 : CollatzResearch.WordTrace tailWord_4173850 prefixEnd_4173850 2143191229768600026379819 := by
  unfold tailWord_4173850
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058203982215440418317751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101488543952574507782180669 38058203982215440418317751)
  ·
    refine ⟨57087305973323160627476627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38058203982215440418317751 57087305973323160627476627)
    ·
      refine ⟨85630958959984740941214941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57087305973323160627476627 85630958959984740941214941)
      ·
        refine ⟨32111609609994277852955603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85630958959984740941214941 32111609609994277852955603)
        ·
          refine ⟨48167414414991416779433405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32111609609994277852955603 48167414414991416779433405)
          ·
            refine ⟨18062780405621781292287527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48167414414991416779433405 18062780405621781292287527)
            ·
              refine ⟨27094170608432671938431291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062780405621781292287527 27094170608432671938431291)
              ·
                refine ⟨40641255912649007907646937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27094170608432671938431291 40641255912649007907646937)
                ·
                  refine ⟨30480941934486755930735203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40641255912649007907646937 30480941934486755930735203)
                  ·
                    refine ⟨45721412901730133896102805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30480941934486755930735203 45721412901730133896102805)
                    ·
                      refine ⟨2143191229768600026379819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45721412901730133896102805 2143191229768600026379819)
                      ·
                        rfl

theorem cell23_4173850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4173850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173850 prefixEnd_4173850 := by exact prefixLift 4173850
  have htrace : WordTrace (prefixWord ++ tailWord_4173850) baseStart_4173850 baseEnd_4173850 := by
    simpa [prefixWord, tailWord_4173850, baseEnd_4173850] using wordTrace_append hprefix tailTrace_4173850
  have hstable : (prefixWord ++ tailWord_4173850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173850).length < 2 ^ (prefixWord ++ tailWord_4173850).sum := by decide
  have hdescent : baseEnd_4173850 < baseStart_4173850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173897 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 5, 2]
def baseStart_4173897 : Nat := 118140960795 + 4173897 * 2 ^ 59
def prefixEnd_4173897 : Nat := 4983230072969 + 3 ^ 40 * 4173897 * 2
def baseEnd_4173897 : Nat := 2143215363359361342492103

theorem tailTrace_4173897 : CollatzResearch.WordTrace tailWord_4173897 prefixEnd_4173897 2143215363359361342492103 := by
  unfold tailWord_4173897
  simp only [CollatzResearch.WordTrace]
  refine ⟨152234530159691488700231945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101489686773127659133487963 152234530159691488700231945)
  ·
    refine ⟨114175897619768616525173959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152234530159691488700231945 114175897619768616525173959)
    ·
      refine ⟨171263846429652924787760939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114175897619768616525173959 171263846429652924787760939)
      ·
        refine ⟨256895769644479387181641409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171263846429652924787760939 256895769644479387181641409)
        ·
          refine ⟨192671827233359540386231057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256895769644479387181641409 192671827233359540386231057)
          ·
            refine ⟨144503870425019655289673293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192671827233359540386231057 144503870425019655289673293)
            ·
              refine ⟨54188951409382370733627485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144503870425019655289673293 54188951409382370733627485)
              ·
                refine ⟨20320856778518389025110307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54188951409382370733627485 20320856778518389025110307)
                ·
                  refine ⟨30481285167777583537665461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20320856778518389025110307 30481285167777583537665461)
                  ·
                    refine ⟨2857620484479148456656137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30481285167777583537665461 2857620484479148456656137)
                    ·
                      refine ⟨2143215363359361342492103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857620484479148456656137 2143215363359361342492103)
                      ·
                        rfl

theorem cell23_4173897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5, 2].length) (baseStart_4173897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173897 prefixEnd_4173897 := by exact prefixLift 4173897
  have htrace : WordTrace (prefixWord ++ tailWord_4173897) baseStart_4173897 baseEnd_4173897 := by
    simpa [prefixWord, tailWord_4173897, baseEnd_4173897] using wordTrace_append hprefix tailTrace_4173897
  have hstable : (prefixWord ++ tailWord_4173897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173897).length < 2 ^ (prefixWord ++ tailWord_4173897).sum := by decide
  have hdescent : baseEnd_4173897 < baseStart_4173897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173914 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_4173914 : Nat := 118140960795 + 4173914 * 2 ^ 59
def prefixEnd_4173914 : Nat := 4983230072969 + 3 ^ 40 * 4173914 * 2
def baseEnd_4173914 : Nat := 2143224092530487775979525

theorem tailTrace_4173914 : CollatzResearch.WordTrace tailWord_4173914 prefixEnd_4173914 2143224092530487775979525 := by
  unfold tailWord_4173914
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058787550157475150900199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101490100133753267069067197 38058787550157475150900199)
  ·
    refine ⟨57088181325236212726350299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38058787550157475150900199 57088181325236212726350299)
    ·
      refine ⟨85632271987854319089525449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57088181325236212726350299 85632271987854319089525449)
      ·
        refine ⟨64224203990890739317144087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85632271987854319089525449 64224203990890739317144087)
        ·
          refine ⟨96336305986336108975716131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64224203990890739317144087 96336305986336108975716131)
          ·
            refine ⟨144504458979504163463574197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96336305986336108975716131 144504458979504163463574197)
            ·
              refine ⟨13547293029328515324710081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144504458979504163463574197 13547293029328515324710081)
              ·
                refine ⟨10160469771996386493532561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13547293029328515324710081 10160469771996386493532561)
                ·
                  refine ⟨7620352328997289870149421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160469771996386493532561 7620352328997289870149421)
                  ·
                    refine ⟨2857632123373983701306033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7620352328997289870149421 2857632123373983701306033)
                    ·
                      refine ⟨2143224092530487775979525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857632123373983701306033 2143224092530487775979525)
                      ·
                        rfl

theorem cell23_4173914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_4173914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173914 prefixEnd_4173914 := by exact prefixLift 4173914
  have htrace : WordTrace (prefixWord ++ tailWord_4173914) baseStart_4173914 baseEnd_4173914 := by
    simpa [prefixWord, tailWord_4173914, baseEnd_4173914] using wordTrace_append hprefix tailTrace_4173914
  have hstable : (prefixWord ++ tailWord_4173914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173914).length < 2 ^ (prefixWord ++ tailWord_4173914).sum := by decide
  have hdescent : baseEnd_4173914 < baseStart_4173914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173927 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_4173927 : Nat := 118140960795 + 4173927 * 2 ^ 59
def prefixEnd_4173927 : Nat := 4983230072969 + 3 ^ 40 * 4173927 * 2
def baseEnd_4173927 : Nat := 2143230767778996225116965

theorem tailTrace_4173927 : CollatzResearch.WordTrace tailWord_4173927 prefixEnd_4173927 2143230767778996225116965 := by
  unfold tailWord_4173927
  simp only [CollatzResearch.WordTrace]
  refine ⟨152235624349582803823824035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101490416233055202549216023 152235624349582803823824035)
  ·
    refine ⟨228353436524374205735736053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152235624349582803823824035 228353436524374205735736053)
    ·
      refine ⟨21408134674160081787725255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228353436524374205735736053 21408134674160081787725255)
      ·
        refine ⟨32112202011240122681587883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21408134674160081787725255 32112202011240122681587883)
        ·
          refine ⟨48168303016860184022381825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112202011240122681587883 48168303016860184022381825)
          ·
            refine ⟨36126227262645138016786369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48168303016860184022381825 36126227262645138016786369)
            ·
              refine ⟨27094670446983853512589777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36126227262645138016786369 27094670446983853512589777)
              ·
                refine ⟨20321002835237890134442333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27094670446983853512589777 20321002835237890134442333)
                ·
                  refine ⟨7620376063214208800415875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20321002835237890134442333 7620376063214208800415875)
                  ·
                    refine ⟨11430564094821313200623813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620376063214208800415875 11430564094821313200623813)
                    ·
                      refine ⟨2143230767778996225116965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11430564094821313200623813 2143230767778996225116965)
                      ·
                        rfl

theorem cell23_4173927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_4173927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173927 prefixEnd_4173927 := by exact prefixLift 4173927
  have htrace : WordTrace (prefixWord ++ tailWord_4173927) baseStart_4173927 baseEnd_4173927 := by
    simpa [prefixWord, tailWord_4173927, baseEnd_4173927] using wordTrace_append hprefix tailTrace_4173927
  have hstable : (prefixWord ++ tailWord_4173927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173927).length < 2 ^ (prefixWord ++ tailWord_4173927).sum := by decide
  have hdescent : baseEnd_4173927 < baseStart_4173927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173944 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_4173944 : Nat := 118140960795 + 4173944 * 2 ^ 59
def prefixEnd_4173944 : Nat := 4983230072969 + 3 ^ 40 * 4173944 * 2
def baseEnd_4173944 : Nat := 2143239496950122658604387

theorem tailTrace_4173944 : CollatzResearch.WordTrace tailWord_4173944 prefixEnd_4173944 2143239496950122658604387 := by
  unfold tailWord_4173944
  simp only [CollatzResearch.WordTrace]
  refine ⟨76118122195260607863596443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101490829593680810484795257 76118122195260607863596443)
  ·
    refine ⟨114177183292890911795394665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76118122195260607863596443 114177183292890911795394665)
    ·
      refine ⟨85632887469668183846545999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114177183292890911795394665 85632887469668183846545999)
      ·
        refine ⟨128449331204502275769818999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85632887469668183846545999 128449331204502275769818999)
        ·
          refine ⟨192673996806753413654728499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128449331204502275769818999 192673996806753413654728499)
          ·
            refine ⟨289010995210130120482092749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192673996806753413654728499 289010995210130120482092749)
            ·
              refine ⟨108379123203798795180784781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289010995210130120482092749 108379123203798795180784781)
              ·
                refine ⟨40642171201424548192794293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108379123203798795180784781 40642171201424548192794293)
                ·
                  refine ⟨3810203550133551393074465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40642171201424548192794293 3810203550133551393074465)
                  ·
                    refine ⟨2857652662600163544805849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810203550133551393074465 2857652662600163544805849)
                    ·
                      refine ⟨2143239496950122658604387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857652662600163544805849 2143239496950122658604387)
                      ·
                        rfl

theorem cell23_4173944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_4173944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173944 prefixEnd_4173944 := by exact prefixLift 4173944
  have htrace : WordTrace (prefixWord ++ tailWord_4173944) baseStart_4173944 baseEnd_4173944 := by
    simpa [prefixWord, tailWord_4173944, baseEnd_4173944] using wordTrace_append hprefix tailTrace_4173944
  have hstable : (prefixWord ++ tailWord_4173944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173944).length < 2 ^ (prefixWord ++ tailWord_4173944).sum := by decide
  have hdescent : baseEnd_4173944 < baseStart_4173944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173957 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_4173957 : Nat := 118140960795 + 4173957 * 2 ^ 59
def prefixEnd_4173957 : Nat := 4983230072969 + 3 ^ 40 * 4173957 * 2
def baseEnd_4173957 : Nat := 2143246172198631107741827

theorem tailTrace_4173957 : CollatzResearch.WordTrace tailWord_4173957 prefixEnd_4173957 2143246172198631107741827 := by
  unfold tailWord_4173957
  simp only [CollatzResearch.WordTrace]
  refine ⟨152236718539474118947416125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101491145692982745964944083 152236718539474118947416125)
  ·
    refine ⟨57088769452302794605281047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152236718539474118947416125 57088769452302794605281047)
    ·
      refine ⟨85633154178454191907921571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57088769452302794605281047 85633154178454191907921571)
      ·
        refine ⟨128449731267681287861882357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85633154178454191907921571 128449731267681287861882357)
        ·
          refine ⟨12042162306345120737051471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128449731267681287861882357 12042162306345120737051471)
          ·
            refine ⟨18063243459517681105577207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12042162306345120737051471 18063243459517681105577207)
            ·
              refine ⟨27094865189276521658365811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063243459517681105577207 27094865189276521658365811)
              ·
                refine ⟨40642297783914782487548717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27094865189276521658365811 40642297783914782487548717)
                ·
                  refine ⟨15240861668968043432830769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40642297783914782487548717 15240861668968043432830769)
                  ·
                    refine ⟨11430646251726032574623077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15240861668968043432830769 11430646251726032574623077)
                    ·
                      refine ⟨2143246172198631107741827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11430646251726032574623077 2143246172198631107741827)
                      ·
                        rfl

theorem cell23_4173957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_4173957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173957 prefixEnd_4173957 := by exact prefixLift 4173957
  have htrace : WordTrace (prefixWord ++ tailWord_4173957) baseStart_4173957 baseEnd_4173957 := by
    simpa [prefixWord, tailWord_4173957, baseEnd_4173957] using wordTrace_append hprefix tailTrace_4173957
  have hstable : (prefixWord ++ tailWord_4173957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173957).length < 2 ^ (prefixWord ++ tailWord_4173957).sum := by decide
  have hdescent : baseEnd_4173957 < baseStart_4173957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173991 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4173991 : Nat := 118140960795 + 4173991 * 2 ^ 59
def prefixEnd_4173991 : Nat := 4983230072969 + 3 ^ 40 * 4173991 * 2
def baseEnd_4173991 : Nat := 2143263630540883974716671

theorem tailTrace_4173991 : CollatzResearch.WordTrace tailWord_4173991 prefixEnd_4173991 2143263630540883974716671 := by
  unfold tailWord_4173991
  simp only [CollatzResearch.WordTrace]
  refine ⟨152237958621350942754153827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101491972414233961836102551 152237958621350942754153827)
  ·
    refine ⟨228356937932026414131230741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152237958621350942754153827 228356937932026414131230741)
    ·
      refine ⟨10704231465563738162401441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228356937932026414131230741 10704231465563738162401441)
      ·
        refine ⟨8028173599172803621801081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10704231465563738162401441 8028173599172803621801081)
        ·
          refine ⟨6021130199379602716350811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8028173599172803621801081 6021130199379602716350811)
          ·
            refine ⟨9031695299069404074526217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021130199379602716350811 9031695299069404074526217)
            ·
              refine ⟨6773771474302053055894663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031695299069404074526217 6773771474302053055894663)
              ·
                refine ⟨10160657211453079583841995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773771474302053055894663 10160657211453079583841995)
                ·
                  refine ⟨15240985817179619375762993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160657211453079583841995 15240985817179619375762993)
                  ·
                    refine ⟨11430739362884714531822245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15240985817179619375762993 11430739362884714531822245)
                    ·
                      refine ⟨2143263630540883974716671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11430739362884714531822245 2143263630540883974716671)
                      ·
                        rfl

theorem cell23_4173991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4173991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173991 prefixEnd_4173991 := by exact prefixLift 4173991
  have htrace : WordTrace (prefixWord ++ tailWord_4173991) baseStart_4173991 baseEnd_4173991 := by
    simpa [prefixWord, tailWord_4173991, baseEnd_4173991] using wordTrace_append hprefix tailTrace_4173991
  have hstable : (prefixWord ++ tailWord_4173991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173991).length < 2 ^ (prefixWord ++ tailWord_4173991).sum := by decide
  have hdescent : baseEnd_4173991 < baseStart_4173991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_4174000 : Nat := 118140960795 + 4174000 * 2 ^ 59
def prefixEnd_4174000 : Nat := 4983230072969 + 3 ^ 40 * 4174000 * 2
def baseEnd_4174000 : Nat := 2143268251866774439504129

theorem tailTrace_4174000 : CollatzResearch.WordTrace tailWord_4174000 prefixEnd_4174000 2143268251866774439504129 := by
  unfold tailWord_4174000
  simp only [CollatzResearch.WordTrace]
  refine ⟨76119143439159168645615727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101492191252212224860820969 76119143439159168645615727)
  ·
    refine ⟨114178715158738752968423591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76119143439159168645615727 114178715158738752968423591)
    ·
      refine ⟨171268072738108129452635387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114178715158738752968423591 171268072738108129452635387)
      ·
        refine ⟨256902109107162194178953081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171268072738108129452635387 256902109107162194178953081)
        ·
          refine ⟨192676581830371645634214811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256902109107162194178953081 192676581830371645634214811)
          ·
            refine ⟨289014872745557468451322217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192676581830371645634214811 289014872745557468451322217)
            ·
              refine ⟨216761154559168101338491663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289014872745557468451322217 216761154559168101338491663)
              ·
                refine ⟨325141731838752152007737495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216761154559168101338491663 325141731838752152007737495)
                ·
                  refine ⟨487712597758128228011606243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325141731838752152007737495 487712597758128228011606243)
                  ·
                    refine ⟨731568896637192342017409365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487712597758128228011606243 731568896637192342017409365)
                    ·
                      refine ⟨2143268251866774439504129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 731568896637192342017409365 2143268251866774439504129)
                      ·
                        rfl

theorem cell23_4174000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_4174000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174000 prefixEnd_4174000 := by exact prefixLift 4174000
  have htrace : WordTrace (prefixWord ++ tailWord_4174000) baseStart_4174000 baseEnd_4174000 := by
    simpa [prefixWord, tailWord_4174000, baseEnd_4174000] using wordTrace_append hprefix tailTrace_4174000
  have hstable : (prefixWord ++ tailWord_4174000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174000).length < 2 ^ (prefixWord ++ tailWord_4174000).sum := by decide
  have hdescent : baseEnd_4174000 < baseStart_4174000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174028 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4174028 : Nat := 118140960795 + 4174028 * 2 ^ 59
def prefixEnd_4174028 : Nat := 4983230072969 + 3 ^ 40 * 4174028 * 2
def baseEnd_4174028 : Nat := 2143282629325100329954001

theorem tailTrace_4174028 : CollatzResearch.WordTrace tailWord_4174028 prefixEnd_4174028 2143282629325100329954001 := by
  unfold tailWord_4174028
  simp only [CollatzResearch.WordTrace]
  refine ⟨76119654061108449036625369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101492872081477932048833825 76119654061108449036625369)
  ·
    refine ⟨57089740545831336777469027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76119654061108449036625369 57089740545831336777469027)
    ·
      refine ⟨85634610818747005166203541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57089740545831336777469027 85634610818747005166203541)
      ·
        refine ⟨4014122382128765867165791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85634610818747005166203541 4014122382128765867165791)
        ·
          refine ⟨6021183573193148800748687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014122382128765867165791 6021183573193148800748687)
          ·
            refine ⟨9031775359789723201123031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021183573193148800748687 9031775359789723201123031)
            ·
              refine ⟨13547663039684584801684547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031775359789723201123031 13547663039684584801684547)
              ·
                refine ⟨20321494559526877202526821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547663039684584801684547 20321494559526877202526821)
                ·
                  refine ⟨3810280229911289475473779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20321494559526877202526821 3810280229911289475473779)
                  ·
                    refine ⟨5715420344866934213210669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3810280229911289475473779 5715420344866934213210669)
                    ·
                      refine ⟨2143282629325100329954001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5715420344866934213210669 2143282629325100329954001)
                      ·
                        rfl

theorem cell23_4174028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4174028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174028 prefixEnd_4174028 := by exact prefixLift 4174028
  have htrace : WordTrace (prefixWord ++ tailWord_4174028) baseStart_4174028 baseEnd_4174028 := by
    simpa [prefixWord, tailWord_4174028, baseEnd_4174028] using wordTrace_append hprefix tailTrace_4174028
  have hstable : (prefixWord ++ tailWord_4174028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174028).length < 2 ^ (prefixWord ++ tailWord_4174028).sum := by decide
  have hdescent : baseEnd_4174028 < baseStart_4174028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174045 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4174045 : Nat := 118140960795 + 4174045 * 2 ^ 59
def prefixEnd_4174045 : Nat := 4983230072969 + 3 ^ 40 * 4174045 * 2
def baseEnd_4174045 : Nat := 2143291358496226763441423

theorem tailTrace_4174045 : CollatzResearch.WordTrace tailWord_4174045 prefixEnd_4174045 2143291358496226763441423 := by
  unfold tailWord_4174045
  simp only [CollatzResearch.WordTrace]
  refine ⟨152239928163155309976619589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101493285442103539984413059 152239928163155309976619589)
  ·
    refine ⟨28544986530591620620616173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152239928163155309976619589 28544986530591620620616173)
    ·
      refine ⟨10704369948971857732731065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28544986530591620620616173 10704369948971857732731065)
      ·
        refine ⟨8028277461728893299548299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10704369948971857732731065 8028277461728893299548299)
        ·
          refine ⟨12042416192593339949322449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028277461728893299548299 12042416192593339949322449)
          ·
            refine ⟨9031812144445004961991837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12042416192593339949322449 9031812144445004961991837)
            ·
              refine ⟨3386929554166876860746939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9031812144445004961991837 3386929554166876860746939)
              ·
                refine ⟨5080394331250315291120409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386929554166876860746939 5080394331250315291120409)
                ·
                  refine ⟨3810295748437736468340307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5080394331250315291120409 3810295748437736468340307)
                  ·
                    refine ⟨5715443622656604702510461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3810295748437736468340307 5715443622656604702510461)
                    ·
                      refine ⟨2143291358496226763441423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5715443622656604702510461 2143291358496226763441423)
                      ·
                        rfl

theorem cell23_4174045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4174045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174045 prefixEnd_4174045 := by exact prefixLift 4174045
  have htrace : WordTrace (prefixWord ++ tailWord_4174045) baseStart_4174045 baseEnd_4174045 := by
    simpa [prefixWord, tailWord_4174045, baseEnd_4174045] using wordTrace_append hprefix tailTrace_4174045
  have hstable : (prefixWord ++ tailWord_4174045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174045).length < 2 ^ (prefixWord ++ tailWord_4174045).sum := by decide
  have hdescent : baseEnd_4174045 < baseStart_4174045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174091 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 5]
def baseStart_4174091 : Nat := 118140960795 + 4174091 * 2 ^ 59
def prefixEnd_4174091 : Nat := 4983230072969 + 3 ^ 40 * 4174091 * 2
def baseEnd_4174091 : Nat := 238146108734037064829579

theorem tailTrace_4174091 : CollatzResearch.WordTrace tailWord_4174091 prefixEnd_4174091 238146108734037064829579 := by
  unfold tailWord_4174091
  simp only [CollatzResearch.WordTrace]
  refine ⟨152241605920988659832794127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101494403947325773221862751 152241605920988659832794127)
  ·
    refine ⟨228362408881482989749191191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152241605920988659832794127 228362408881482989749191191)
    ·
      refine ⟨342543613322224484623786787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228362408881482989749191191 342543613322224484623786787)
      ·
        refine ⟨513815419983336726935680181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342543613322224484623786787 513815419983336726935680181)
        ·
          refine ⟨48170195623437818150220017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 513815419983336726935680181 48170195623437818150220017)
          ·
            refine ⟨36127646717578363612665013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48170195623437818150220017 36127646717578363612665013)
            ·
              refine ⟨3386966879772971588687345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36127646717578363612665013 3386966879772971588687345)
              ·
                refine ⟨2540225159829728691515509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386966879772971588687345 2540225159829728691515509)
                ·
                  refine ⟨238146108734037064829579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540225159829728691515509 238146108734037064829579)
                  ·
                    rfl

theorem cell23_4174091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 5].length) (baseStart_4174091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174091 prefixEnd_4174091 := by exact prefixLift 4174091
  have htrace : WordTrace (prefixWord ++ tailWord_4174091) baseStart_4174091 baseEnd_4174091 := by
    simpa [prefixWord, tailWord_4174091, baseEnd_4174091] using wordTrace_append hprefix tailTrace_4174091
  have hstable : (prefixWord ++ tailWord_4174091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174091).length < 2 ^ (prefixWord ++ tailWord_4174091).sum := by decide
  have hdescent : baseEnd_4174091 < baseStart_4174091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174097 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_4174097 : Nat := 118140960795 + 4174097 * 2 ^ 59
def prefixEnd_4174097 : Nat := 4983230072969 + 3 ^ 40 * 4174097 * 2
def baseEnd_4174097 : Nat := 2143318059490260559991183

theorem tailTrace_4174097 : CollatzResearch.WordTrace tailWord_4174097 prefixEnd_4174097 2143318059490260559991183 := by
  unfold tailWord_4174097
  simp only [CollatzResearch.WordTrace]
  refine ⟨152241824758966922857512545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101494549839311281905008363 152241824758966922857512545)
  ·
    refine ⟨114181368569225192143134409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152241824758966922857512545 114181368569225192143134409)
    ·
      refine ⟨85636026426918894107350807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114181368569225192143134409 85636026426918894107350807)
      ·
        refine ⟨128454039640378341161026211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85636026426918894107350807 128454039640378341161026211)
        ·
          refine ⟨192681059460567511741539317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128454039640378341161026211 192681059460567511741539317)
          ·
            refine ⟨18063849324428204225769311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192681059460567511741539317 18063849324428204225769311)
            ·
              refine ⟨27095773986642306338653967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063849324428204225769311 27095773986642306338653967)
              ·
                refine ⟨40643660979963459507980951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27095773986642306338653967 40643660979963459507980951)
                ·
                  refine ⟨60965491469945189261971427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40643660979963459507980951 60965491469945189261971427)
                  ·
                    refine ⟨91448237204917783892957141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60965491469945189261971427 91448237204917783892957141)
                    ·
                      refine ⟨2143318059490260559991183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91448237204917783892957141 2143318059490260559991183)
                      ·
                        rfl

theorem cell23_4174097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_4174097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174097 prefixEnd_4174097 := by exact prefixLift 4174097
  have htrace : WordTrace (prefixWord ++ tailWord_4174097) baseStart_4174097 baseEnd_4174097 := by
    simpa [prefixWord, tailWord_4174097, baseEnd_4174097] using wordTrace_append hprefix tailTrace_4174097
  have hstable : (prefixWord ++ tailWord_4174097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174097).length < 2 ^ (prefixWord ++ tailWord_4174097).sum := by decide
  have hdescent : baseEnd_4174097 < baseStart_4174097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174107 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_4174107 : Nat := 118140960795 + 4174107 * 2 ^ 59
def prefixEnd_4174107 : Nat := 4983230072969 + 3 ^ 40 * 4174107 * 2
def baseEnd_4174107 : Nat := 2143323194296805520866137

theorem tailTrace_4174107 : CollatzResearch.WordTrace tailWord_4174107 prefixEnd_4174107 2143323194296805520866137 := by
  unfold tailWord_4174107
  simp only [CollatzResearch.WordTrace]
  refine ⟨152242189488930694565376575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101494792992620463043584383 152242189488930694565376575)
  ·
    refine ⟨228363284233396041848064863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152242189488930694565376575 228363284233396041848064863)
    ·
      refine ⟨342544926350094062772097295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228363284233396041848064863 342544926350094062772097295)
      ·
        refine ⟨513817389525141094158145943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342544926350094062772097295 513817389525141094158145943)
        ·
          refine ⟨770726084287711641237218915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513817389525141094158145943 770726084287711641237218915)
          ·
            refine ⟨1156089126431567461855828373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770726084287711641237218915 1156089126431567461855828373)
            ·
              refine ⟨54191677801479724774491955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1156089126431567461855828373 54191677801479724774491955)
              ·
                refine ⟨81287516702219587161737933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54191677801479724774491955 81287516702219587161737933)
                ·
                  refine ⟨30482818763332345185651725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81287516702219587161737933 30482818763332345185651725)
                  ·
                    refine ⟨11431057036249629444619397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30482818763332345185651725 11431057036249629444619397)
                    ·
                      refine ⟨2143323194296805520866137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11431057036249629444619397 2143323194296805520866137)
                      ·
                        rfl

theorem cell23_4174107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_4174107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174107 prefixEnd_4174107 := by exact prefixLift 4174107
  have htrace : WordTrace (prefixWord ++ tailWord_4174107) baseStart_4174107 baseEnd_4174107 := by
    simpa [prefixWord, tailWord_4174107, baseEnd_4174107] using wordTrace_append hprefix tailTrace_4174107
  have hstable : (prefixWord ++ tailWord_4174107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174107).length < 2 ^ (prefixWord ++ tailWord_4174107).sum := by decide
  have hdescent : baseEnd_4174107 < baseStart_4174107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174124 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_4174124 : Nat := 118140960795 + 4174124 * 2 ^ 59
def prefixEnd_4174124 : Nat := 4983230072969 + 3 ^ 40 * 4174124 * 2
def baseEnd_4174124 : Nat := 2143331923467931954353559

theorem tailTrace_4174124 : CollatzResearch.WordTrace tailWord_4174124 prefixEnd_4174124 2143331923467931954353559 := by
  unfold tailWord_4174124
  simp only [CollatzResearch.WordTrace]
  refine ⟨76121404764934553234372713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101495206353246070979163617 76121404764934553234372713)
  ·
    refine ⟨57091053573700914925779535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76121404764934553234372713 57091053573700914925779535)
    ·
      refine ⟨85636580360551372388669303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57091053573700914925779535 85636580360551372388669303)
      ·
        refine ⟨128454870540827058583003955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85636580360551372388669303 128454870540827058583003955)
        ·
          refine ⟨192682305811240587874505933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128454870540827058583003955 192682305811240587874505933)
          ·
            refine ⟨72255864679215220452939725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192682305811240587874505933 72255864679215220452939725)
            ·
              refine ⟨27095949254705707669852397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72255864679215220452939725 27095949254705707669852397)
              ·
                refine ⟨10160980970514640376194649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27095949254705707669852397 10160980970514640376194649)
                ·
                  refine ⟨7620735727885980282145987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160980970514640376194649 7620735727885980282145987)
                  ·
                    refine ⟨11431103591828970423218981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620735727885980282145987 11431103591828970423218981)
                    ·
                      refine ⟨2143331923467931954353559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11431103591828970423218981 2143331923467931954353559)
                      ·
                        rfl

theorem cell23_4174124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_4174124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174124 prefixEnd_4174124 := by exact prefixLift 4174124
  have htrace : WordTrace (prefixWord ++ tailWord_4174124) baseStart_4174124 baseEnd_4174124 := by
    simpa [prefixWord, tailWord_4174124, baseEnd_4174124] using wordTrace_append hprefix tailTrace_4174124
  have hstable : (prefixWord ++ tailWord_4174124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174124).length < 2 ^ (prefixWord ++ tailWord_4174124).sum := by decide
  have hdescent : baseEnd_4174124 < baseStart_4174124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174144 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_4174144 : Nat := 118140960795 + 4174144 * 2 ^ 59
def prefixEnd_4174144 : Nat := 4983230072969 + 3 ^ 40 * 4174144 * 2
def baseEnd_4174144 : Nat := 2143342193081021876103467

theorem tailTrace_4174144 : CollatzResearch.WordTrace tailWord_4174144 prefixEnd_4174144 2143342193081021876103467 := by
  unfold tailWord_4174144
  simp only [CollatzResearch.WordTrace]
  refine ⟨76121769494898324942236743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101495692659864433256315657 76121769494898324942236743)
  ·
    refine ⟨114182654242347487413355115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76121769494898324942236743 114182654242347487413355115)
    ·
      refine ⟨171273981363521231120032673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114182654242347487413355115 171273981363521231120032673)
      ·
        refine ⟨128455486022640923340024505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171273981363521231120032673 128455486022640923340024505)
        ·
          refine ⟨96341614516980692505018379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128455486022640923340024505 96341614516980692505018379)
          ·
            refine ⟨144512421775471038757527569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96341614516980692505018379 144512421775471038757527569)
            ·
              refine ⟨108384316331603279068145677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144512421775471038757527569 108384316331603279068145677)
              ·
                refine ⟨40644118624351229650554629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108384316331603279068145677 40644118624351229650554629)
                ·
                  refine ⟨7620772242065855559478993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40644118624351229650554629 7620772242065855559478993)
                  ·
                    refine ⟨5715579181549391669609245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620772242065855559478993 5715579181549391669609245)
                    ·
                      refine ⟨2143342193081021876103467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5715579181549391669609245 2143342193081021876103467)
                      ·
                        rfl

theorem cell23_4174144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_4174144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174144 prefixEnd_4174144 := by exact prefixLift 4174144
  have htrace : WordTrace (prefixWord ++ tailWord_4174144) baseStart_4174144 baseEnd_4174144 := by
    simpa [prefixWord, tailWord_4174144, baseEnd_4174144] using wordTrace_append hprefix tailTrace_4174144
  have hstable : (prefixWord ++ tailWord_4174144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174144).length < 2 ^ (prefixWord ++ tailWord_4174144).sum := by decide
  have hdescent : baseEnd_4174144 < baseStart_4174144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174147 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 8]
def baseStart_4174147 : Nat := 118140960795 + 4174147 * 2 ^ 59
def prefixEnd_4174147 : Nat := 4983230072969 + 3 ^ 40 * 4174147 * 2
def baseEnd_4174147 : Nat := 238149303724776151596217

theorem tailTrace_4174147 : CollatzResearch.WordTrace tailWord_4174147 prefixEnd_4174147 238149303724776151596217 := by
  unfold tailWord_4174147
  simp only [CollatzResearch.WordTrace]
  refine ⟨152243648408785781396832695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101495765605857187597888463 152243648408785781396832695)
  ·
    refine ⟨228365472613178672095249043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152243648408785781396832695 228365472613178672095249043)
    ·
      refine ⟨342548208919768008142873565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228365472613178672095249043 342548208919768008142873565)
      ·
        refine ⟨128455578344913003053577587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342548208919768008142873565 128455578344913003053577587)
        ·
          refine ⟨192683367517369504580366381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128455578344913003053577587 192683367517369504580366381)
          ·
            refine ⟨72256262819013564217637393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192683367517369504580366381 72256262819013564217637393)
            ·
              refine ⟨54192197114260173163228045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72256262819013564217637393 54192197114260173163228045)
              ·
                refine ⟨20322073917847564936210517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54192197114260173163228045 20322073917847564936210517)
                ·
                  refine ⟨238149303724776151596217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20322073917847564936210517 238149303724776151596217)
                  ·
                    rfl

theorem cell23_4174147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8].length) (baseStart_4174147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174147 prefixEnd_4174147 := by exact prefixLift 4174147
  have htrace : WordTrace (prefixWord ++ tailWord_4174147) baseStart_4174147 baseEnd_4174147 := by
    simpa [prefixWord, tailWord_4174147, baseEnd_4174147] using wordTrace_append hprefix tailTrace_4174147
  have hstable : (prefixWord ++ tailWord_4174147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174147).length < 2 ^ (prefixWord ++ tailWord_4174147).sum := by decide
  have hdescent : baseEnd_4174147 < baseStart_4174147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174178 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4174178 : Nat := 118140960795 + 4174178 * 2 ^ 59
def prefixEnd_4174178 : Nat := 4983230072969 + 3 ^ 40 * 4174178 * 2
def baseEnd_4174178 : Nat := 2143359651423274743078311

theorem tailTrace_4174178 : CollatzResearch.WordTrace tailWord_4174178 prefixEnd_4174178 2143359651423274743078311 := by
  unfold tailWord_4174178
  simp only [CollatzResearch.WordTrace]
  refine ⟨38061194767918368422802797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101496519381115649127474125 38061194767918368422802797)
  ·
    refine ⟨14272948037969388158551049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38061194767918368422802797 14272948037969388158551049)
    ·
      refine ⟨10704711028477041118913287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14272948037969388158551049 10704711028477041118913287)
      ·
        refine ⟨16057066542715561678369931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704711028477041118913287 16057066542715561678369931)
        ·
          refine ⟨24085599814073342517554897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057066542715561678369931 24085599814073342517554897)
          ·
            refine ⟨18064199860555006888166173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24085599814073342517554897 18064199860555006888166173)
            ·
              refine ⟨6774074947708127583062315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18064199860555006888166173 6774074947708127583062315)
              ·
                refine ⟨10161112421562191374593473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774074947708127583062315 10161112421562191374593473)
                ·
                  refine ⟨7620834316171643530945105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10161112421562191374593473 7620834316171643530945105)
                  ·
                    refine ⟨5715625737128732648208829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620834316171643530945105 5715625737128732648208829)
                    ·
                      refine ⟨2143359651423274743078311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5715625737128732648208829 2143359651423274743078311)
                      ·
                        rfl

theorem cell23_4174178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4174178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174178 prefixEnd_4174178 := by exact prefixLift 4174178
  have htrace : WordTrace (prefixWord ++ tailWord_4174178) baseStart_4174178 baseEnd_4174178 := by
    simpa [prefixWord, tailWord_4174178, baseEnd_4174178] using wordTrace_append hprefix tailTrace_4174178
  have hstable : (prefixWord ++ tailWord_4174178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174178).length < 2 ^ (prefixWord ++ tailWord_4174178).sum := by decide
  have hdescent : baseEnd_4174178 < baseStart_4174178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174187 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_4174187 : Nat := 118140960795 + 4174187 * 2 ^ 59
def prefixEnd_4174187 : Nat := 4983230072969 + 3 ^ 40 * 4174187 * 2
def baseEnd_4174187 : Nat := 2143364272749165207865769

theorem tailTrace_4174187 : CollatzResearch.WordTrace tailWord_4174187 prefixEnd_4174187 2143364272749165207865769 := by
  unfold tailWord_4174187
  simp only [CollatzResearch.WordTrace]
  refine ⟨152245107328640868228288815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101496738219093912152192543 152245107328640868228288815)
  ·
    refine ⟨228367660992961302342433223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152245107328640868228288815 228367660992961302342433223)
    ·
      refine ⟨342551491489441953513649835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228367660992961302342433223 342551491489441953513649835)
      ·
        refine ⟨513827237234162930270474753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342551491489441953513649835 513827237234162930270474753)
        ·
          refine ⟨385370427925622197702856065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513827237234162930270474753 385370427925622197702856065)
          ·
            refine ⟨289027820944216648277142049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385370427925622197702856065 289027820944216648277142049)
            ·
              refine ⟨216770865708162486207856537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289027820944216648277142049 216770865708162486207856537)
              ·
                refine ⟨162578149281121864655892403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216770865708162486207856537 162578149281121864655892403)
                ·
                  refine ⟨243867223921682796983838605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162578149281121864655892403 243867223921682796983838605)
                  ·
                    refine ⟨91450208970631048868939477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243867223921682796983838605 91450208970631048868939477)
                    ·
                      refine ⟨2143364272749165207865769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91450208970631048868939477 2143364272749165207865769)
                      ·
                        rfl

theorem cell23_4174187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_4174187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174187 prefixEnd_4174187 := by exact prefixLift 4174187
  have htrace : WordTrace (prefixWord ++ tailWord_4174187) baseStart_4174187 baseEnd_4174187 := by
    simpa [prefixWord, tailWord_4174187, baseEnd_4174187] using wordTrace_append hprefix tailTrace_4174187
  have hstable : (prefixWord ++ tailWord_4174187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174187).length < 2 ^ (prefixWord ++ tailWord_4174187).sum := by decide
  have hdescent : baseEnd_4174187 < baseStart_4174187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174198 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_4174198 : Nat := 118140960795 + 4174198 * 2 ^ 59
def prefixEnd_4174198 : Nat := 4983230072969 + 3 ^ 40 * 4174198 * 2
def baseEnd_4174198 : Nat := 238152213448484962758691

theorem tailTrace_4174198 : CollatzResearch.WordTrace tailWord_4174198 prefixEnd_4174198 238152213448484962758691 := by
  unfold tailWord_4174198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515344283225063569183703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101497005687734011404626165 9515344283225063569183703)
  ·
    refine ⟨14273016424837595353775555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515344283225063569183703 14273016424837595353775555)
    ·
      refine ⟨21409524637256393030663333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273016424837595353775555 21409524637256393030663333)
      ·
        refine ⟨4014285869485573693249375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21409524637256393030663333 4014285869485573693249375)
        ·
          refine ⟨6021428804228360539874063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014285869485573693249375 6021428804228360539874063)
          ·
            refine ⟨9032143206342540809811095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021428804228360539874063 9032143206342540809811095)
            ·
              refine ⟨13548214809513811214716643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032143206342540809811095 13548214809513811214716643)
              ·
                refine ⟨20322322214270716822074965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13548214809513811214716643 20322322214270716822074965)
                ·
                  refine ⟨238152213448484962758691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20322322214270716822074965 238152213448484962758691)
                  ·
                    rfl

theorem cell23_4174198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_4174198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174198 prefixEnd_4174198 := by exact prefixLift 4174198
  have htrace : WordTrace (prefixWord ++ tailWord_4174198) baseStart_4174198 baseEnd_4174198 := by
    simpa [prefixWord, tailWord_4174198, baseEnd_4174198] using wordTrace_append hprefix tailTrace_4174198
  have hstable : (prefixWord ++ tailWord_4174198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174198).length < 2 ^ (prefixWord ++ tailWord_4174198).sum := by decide
  have hdescent : baseEnd_4174198 < baseStart_4174198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174201 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 4, 3, 2]
def baseStart_4174201 : Nat := 118140960795 + 4174201 * 2 ^ 59
def prefixEnd_4174201 : Nat := 4983230072969 + 3 ^ 40 * 4174201 * 2
def baseEnd_4174201 : Nat := 2143371461478328153090705

theorem tailTrace_4174201 : CollatzResearch.WordTrace tailWord_4174201 prefixEnd_4174201 2143371461478328153090705 := by
  unfold tailWord_4174201
  simp only [CollatzResearch.WordTrace]
  refine ⟨152245617950590148619298457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101497078633726765746198971 152245617950590148619298457)
  ·
    refine ⟨114184213462942611464473843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152245617950590148619298457 114184213462942611464473843)
    ·
      refine ⟨171276320194413917196710765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114184213462942611464473843 171276320194413917196710765)
      ·
        refine ⟨64228620072905218948766537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171276320194413917196710765 64228620072905218948766537)
        ·
          refine ⟨48171465054678914211574903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64228620072905218948766537 48171465054678914211574903)
          ·
            refine ⟨72257197582018371317362355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48171465054678914211574903 72257197582018371317362355)
            ·
              refine ⟨108385796373027556976043533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72257197582018371317362355 108385796373027556976043533)
              ·
                refine ⟨40644673639885333866016325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108385796373027556976043533 40644673639885333866016325)
                ·
                  refine ⟨7620876307478500099878061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40644673639885333866016325 7620876307478500099878061)
                  ·
                    refine ⟨2857828615304437537454273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7620876307478500099878061 2857828615304437537454273)
                    ·
                      refine ⟨2143371461478328153090705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857828615304437537454273 2143371461478328153090705)
                      ·
                        rfl

theorem cell23_4174201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_4174201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174201 prefixEnd_4174201 := by exact prefixLift 4174201
  have htrace : WordTrace (prefixWord ++ tailWord_4174201) baseStart_4174201 baseEnd_4174201 := by
    simpa [prefixWord, tailWord_4174201, baseEnd_4174201] using wordTrace_append hprefix tailTrace_4174201
  have hstable : (prefixWord ++ tailWord_4174201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174201).length < 2 ^ (prefixWord ++ tailWord_4174201).sum := by decide
  have hdescent : baseEnd_4174201 < baseStart_4174201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174231 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_4174231 : Nat := 118140960795 + 4174231 * 2 ^ 59
def prefixEnd_4174231 : Nat := 4983230072969 + 3 ^ 40 * 4174231 * 2
def baseEnd_4174231 : Nat := 2143386865897963035715567

theorem tailTrace_4174231 : CollatzResearch.WordTrace tailWord_4174231 prefixEnd_4174231 2143386865897963035715567 := by
  unfold tailWord_4174231
  simp only [CollatzResearch.WordTrace]
  refine ⟨152246712140481463742890547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101497808093654309161927031 152246712140481463742890547)
  ·
    refine ⟨228370068210722195614335821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152246712140481463742890547 228370068210722195614335821)
    ·
      refine ⟨85638775579020823355375933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228370068210722195614335821 85638775579020823355375933)
      ·
        refine ⟨32114540842132808758265975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85638775579020823355375933 32114540842132808758265975)
        ·
          refine ⟨48171811263199213137398963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32114540842132808758265975 48171811263199213137398963)
          ·
            refine ⟨72257716894798819706098445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48171811263199213137398963 72257716894798819706098445)
            ·
              refine ⟨27096643835549557389786917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72257716894798819706098445 27096643835549557389786917)
              ·
                refine ⟨5080620719165542010585047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27096643835549557389786917 5080620719165542010585047)
                ·
                  refine ⟨7620931078748313015877571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080620719165542010585047 7620931078748313015877571)
                  ·
                    refine ⟨11431396618122469523816357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620931078748313015877571 11431396618122469523816357)
                    ·
                      refine ⟨2143386865897963035715567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11431396618122469523816357 2143386865897963035715567)
                      ·
                        rfl

theorem cell23_4174231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_4174231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174231 prefixEnd_4174231 := by exact prefixLift 4174231
  have htrace : WordTrace (prefixWord ++ tailWord_4174231) baseStart_4174231 baseEnd_4174231 := by
    simpa [prefixWord, tailWord_4174231, baseEnd_4174231] using wordTrace_append hprefix tailTrace_4174231
  have hstable : (prefixWord ++ tailWord_4174231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174231).length < 2 ^ (prefixWord ++ tailWord_4174231).sum := by decide
  have hdescent : baseEnd_4174231 < baseStart_4174231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174265 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4174265 : Nat := 118140960795 + 4174265 * 2 ^ 59
def prefixEnd_4174265 : Nat := 4983230072969 + 3 ^ 40 * 4174265 * 2
def baseEnd_4174265 : Nat := 2143404324240215902690411

theorem tailTrace_4174265 : CollatzResearch.WordTrace tailWord_4174265 prefixEnd_4174265 2143404324240215902690411 := by
  unfold tailWord_4174265
  simp only [CollatzResearch.WordTrace]
  refine ⟨152247952222358287549628249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101498634814905525033085499 152247952222358287549628249)
  ·
    refine ⟨114185964166768715662221187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152247952222358287549628249 114185964166768715662221187)
    ·
      refine ⟨171278946250153073493331781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114185964166768715662221187 171278946250153073493331781)
      ·
        refine ⟨32114802421903701279999709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171278946250153073493331781 32114802421903701279999709)
        ·
          refine ⟨12043050908213887979999891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32114802421903701279999709 12043050908213887979999891)
          ·
            refine ⟨18064576362320831969999837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043050908213887979999891 18064576362320831969999837)
            ·
              refine ⟨6774216135870311988749939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18064576362320831969999837 6774216135870311988749939)
              ·
                refine ⟨10161324203805467983124909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774216135870311988749939 10161324203805467983124909)
                ·
                  refine ⟨3810496576427050493671841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10161324203805467983124909 3810496576427050493671841)
                  ·
                    refine ⟨2857872432320287870253881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810496576427050493671841 2857872432320287870253881)
                    ·
                      refine ⟨2143404324240215902690411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857872432320287870253881 2143404324240215902690411)
                      ·
                        rfl

theorem cell23_4174265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4174265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174265 prefixEnd_4174265 := by exact prefixLift 4174265
  have htrace : WordTrace (prefixWord ++ tailWord_4174265) baseStart_4174265 baseEnd_4174265 := by
    simpa [prefixWord, tailWord_4174265, baseEnd_4174265] using wordTrace_append hprefix tailTrace_4174265
  have hstable : (prefixWord ++ tailWord_4174265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174265).length < 2 ^ (prefixWord ++ tailWord_4174265).sum := by decide
  have hdescent : baseEnd_4174265 < baseStart_4174265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174378 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_4174378 : Nat := 118140960795 + 4174378 * 2 ^ 59
def prefixEnd_4174378 : Nat := 4983230072969 + 3 ^ 40 * 4174378 * 2
def baseEnd_4174378 : Nat := 238162483061574884508599

theorem tailTrace_4174378 : CollatzResearch.WordTrace tailWord_4174378 prefixEnd_4174378 238162483061574884508599 := by
  unfold tailWord_4174378
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063018417737226962122947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101501382447299271898994525 38063018417737226962122947)
  ·
    refine ⟨57094527626605840443184421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38063018417737226962122947 57094527626605840443184421)
    ·
      refine ⟨10705223929988595083097079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57094527626605840443184421 10705223929988595083097079)
      ·
        refine ⟨16057835894982892624645619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705223929988595083097079 16057835894982892624645619)
        ·
          refine ⟨24086753842474338936968429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057835894982892624645619 24086753842474338936968429)
          ·
            refine ⟨9032532690927877101363161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24086753842474338936968429 9032532690927877101363161)
            ·
              refine ⟨6774399518195907826022371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9032532690927877101363161 6774399518195907826022371)
              ·
                refine ⟨10161599277293861739033557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774399518195907826022371 10161599277293861739033557)
                ·
                  refine ⟨238162483061574884508599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10161599277293861739033557 238162483061574884508599)
                  ·
                    rfl

theorem cell23_4174378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_4174378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174378 prefixEnd_4174378 := by exact prefixLift 4174378
  have htrace : WordTrace (prefixWord ++ tailWord_4174378) baseStart_4174378 baseEnd_4174378 := by
    simpa [prefixWord, tailWord_4174378, baseEnd_4174378] using wordTrace_append hprefix tailTrace_4174378
  have hstable : (prefixWord ++ tailWord_4174378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174378).length < 2 ^ (prefixWord ++ tailWord_4174378).sum := by decide
  have hdescent : baseEnd_4174378 < baseStart_4174378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174411 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_4174411 : Nat := 118140960795 + 4174411 * 2 ^ 59
def prefixEnd_4174411 : Nat := 4983230072969 + 3 ^ 40 * 4174411 * 2
def baseEnd_4174411 : Nat := 2143479292415772331464739

theorem tailTrace_4174411 : CollatzResearch.WordTrace tailWord_4174411 prefixEnd_4174411 2143479292415772331464739 := by
  unfold tailWord_4174411
  simp only [CollatzResearch.WordTrace]
  refine ⟨152253277279829354484443087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101502184853219569656295391 152253277279829354484443087)
  ·
    refine ⟨228379915919744031726664631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152253277279829354484443087 228379915919744031726664631)
    ·
      refine ⟨342569873879616047589996947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228379915919744031726664631 342569873879616047589996947)
      ·
        refine ⟨513854810819424071384995421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342569873879616047589996947 513854810819424071384995421)
        ·
          refine ⟨192695554057284026769373283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513854810819424071384995421 192695554057284026769373283)
          ·
            refine ⟨289043331085926040154059925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192695554057284026769373283 289043331085926040154059925)
            ·
              refine ⟨13548906144652783132221559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289043331085926040154059925 13548906144652783132221559)
              ·
                refine ⟨20323359216979174698332339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13548906144652783132221559 20323359216979174698332339)
                ·
                  refine ⟨30485038825468762047498509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20323359216979174698332339 30485038825468762047498509)
                  ·
                    refine ⟨11431889559550785767811941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30485038825468762047498509 11431889559550785767811941)
                    ·
                      refine ⟨2143479292415772331464739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11431889559550785767811941 2143479292415772331464739)
                      ·
                        rfl

theorem cell23_4174411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_4174411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174411 prefixEnd_4174411 := by exact prefixLift 4174411
  have htrace : WordTrace (prefixWord ++ tailWord_4174411) baseStart_4174411 baseEnd_4174411 := by
    simpa [prefixWord, tailWord_4174411, baseEnd_4174411] using wordTrace_append hprefix tailTrace_4174411
  have hstable : (prefixWord ++ tailWord_4174411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174411).length < 2 ^ (prefixWord ++ tailWord_4174411).sum := by decide
  have hdescent : baseEnd_4174411 < baseStart_4174411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174465 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_4174465 : Nat := 118140960795 + 4174465 * 2 ^ 59
def prefixEnd_4174465 : Nat := 4983230072969 + 3 ^ 40 * 4174465 * 2
def baseEnd_4174465 : Nat := 2143507020371115120189491

theorem tailTrace_4174465 : CollatzResearch.WordTrace tailWord_4174465 prefixEnd_4174465 2143507020371115120189491 := by
  unfold tailWord_4174465
  simp only [CollatzResearch.WordTrace]
  refine ⟨152255246821633721706908849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101503497881089147804605899 152255246821633721706908849)
  ·
    refine ⟨114191435116225291280181637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152255246821633721706908849 114191435116225291280181637)
    ·
      refine ⟨21410894084292242115034057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114191435116225291280181637 21410894084292242115034057)
      ·
        refine ⟨16058170563219181586275543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410894084292242115034057 16058170563219181586275543)
        ·
          refine ⟨24087255844828772379413315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058170563219181586275543 24087255844828772379413315)
          ·
            refine ⟨36130883767243158569119973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087255844828772379413315 36130883767243158569119973)
            ·
              refine ⟨6774540706358092231709995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36130883767243158569119973 6774540706358092231709995)
              ·
                refine ⟨10161811059537138347564993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774540706358092231709995 10161811059537138347564993)
                ·
                  refine ⟨7621358294652853760673745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10161811059537138347564993 7621358294652853760673745)
                  ·
                    refine ⟨5716018720989640320505309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7621358294652853760673745 5716018720989640320505309)
                    ·
                      refine ⟨2143507020371115120189491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5716018720989640320505309 2143507020371115120189491)
                      ·
                        rfl

theorem cell23_4174465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_4174465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174465 prefixEnd_4174465 := by exact prefixLift 4174465
  have htrace : WordTrace (prefixWord ++ tailWord_4174465) baseStart_4174465 baseEnd_4174465 := by
    simpa [prefixWord, tailWord_4174465, baseEnd_4174465] using wordTrace_append hprefix tailTrace_4174465
  have hstable : (prefixWord ++ tailWord_4174465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174465).length < 2 ^ (prefixWord ++ tailWord_4174465).sum := by decide
  have hdescent : baseEnd_4174465 < baseStart_4174465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174528 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_4174528 : Nat := 118140960795 + 4174528 * 2 ^ 59
def prefixEnd_4174528 : Nat := 4983230072969 + 3 ^ 40 * 4174528 * 2
def baseEnd_4174528 : Nat := 714513123217449457900567

theorem tailTrace_4174528 : CollatzResearch.WordTrace tailWord_4174528 prefixEnd_4174528 714513123217449457900567 := by
  unfold tailWord_4174528
  simp only [CollatzResearch.WordTrace]
  refine ⟨76128772310202741733226119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101505029746936988977634825 76128772310202741733226119)
  ·
    refine ⟨114193158465304112599839179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76128772310202741733226119 114193158465304112599839179)
    ·
      refine ⟨171289737697956168899758769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114193158465304112599839179 171289737697956168899758769)
      ·
        refine ⟨128467303273467126674819077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171289737697956168899758769 128467303273467126674819077)
        ·
          refine ⟨24087619363775086251528577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128467303273467126674819077 24087619363775086251528577)
          ·
            refine ⟨18065714522831314688646433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087619363775086251528577 18065714522831314688646433)
            ·
              refine ⟨13549285892123486016484825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18065714522831314688646433 13549285892123486016484825)
              ·
                refine ⟨10161964419092614512363619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13549285892123486016484825 10161964419092614512363619)
                ·
                  refine ⟨15242946628638921768545429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10161964419092614512363619 15242946628638921768545429)
                  ·
                    refine ⟨714513123217449457900567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15242946628638921768545429 714513123217449457900567)
                    ·
                      rfl

theorem cell23_4174528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_4174528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174528 prefixEnd_4174528 := by exact prefixLift 4174528
  have htrace : WordTrace (prefixWord ++ tailWord_4174528) baseStart_4174528 baseEnd_4174528 := by
    simpa [prefixWord, tailWord_4174528, baseEnd_4174528] using wordTrace_append hprefix tailTrace_4174528
  have hstable : (prefixWord ++ tailWord_4174528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174528).length < 2 ^ (prefixWord ++ tailWord_4174528).sum := by decide
  have hdescent : baseEnd_4174528 < baseStart_4174528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174532 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4174532 : Nat := 118140960795 + 4174532 * 2 ^ 59
def prefixEnd_4174532 : Nat := 4983230072969 + 3 ^ 40 * 4174532 * 2
def baseEnd_4174532 : Nat := 714513807858322119350561

theorem tailTrace_4174532 : CollatzResearch.WordTrace tailWord_4174532 prefixEnd_4174532 714513807858322119350561 := by
  unfold tailWord_4174532
  simp only [CollatzResearch.WordTrace]
  refine ⟨76128845256195496074798925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101505127008260661433065233 76128845256195496074798925)
  ·
    refine ⟨28548316971073311028049597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76128845256195496074798925 28548316971073311028049597)
    ·
      refine ⟨10705618864152491635518599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28548316971073311028049597 10705618864152491635518599)
      ·
        refine ⟨16058428296228737453277899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705618864152491635518599 16058428296228737453277899)
        ·
          refine ⟨24087642444343106179916849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058428296228737453277899 24087642444343106179916849)
          ·
            refine ⟨18065731833257329634937637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087642444343106179916849 18065731833257329634937637)
            ·
              refine ⟨3387324718735749306550807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18065731833257329634937637 3387324718735749306550807)
              ·
                refine ⟨5080987078103623959826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387324718735749306550807 5080987078103623959826211)
                ·
                  refine ⟨7621480617155435939739317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080987078103623959826211 7621480617155435939739317)
                  ·
                    refine ⟨714513807858322119350561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7621480617155435939739317 714513807858322119350561)
                    ·
                      rfl

theorem cell23_4174532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4174532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174532 prefixEnd_4174532 := by exact prefixLift 4174532
  have htrace : WordTrace (prefixWord ++ tailWord_4174532) baseStart_4174532 baseEnd_4174532 := by
    simpa [prefixWord, tailWord_4174532, baseEnd_4174532] using wordTrace_append hprefix tailTrace_4174532
  have hstable : (prefixWord ++ tailWord_4174532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174532).length < 2 ^ (prefixWord ++ tailWord_4174532).sum := by decide
  have hdescent : baseEnd_4174532 < baseStart_4174532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174552 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_4174552 : Nat := 118140960795 + 4174552 * 2 ^ 59
def prefixEnd_4174552 : Nat := 4983230072969 + 3 ^ 40 * 4174552 * 2
def baseEnd_4174552 : Nat := 2143551693188056279801591

theorem tailTrace_4174552 : CollatzResearch.WordTrace tailWord_4174552 prefixEnd_4174552 2143551693188056279801591 := by
  unfold tailWord_4174552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76129209986159267782662955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101505613314879023710217273 76129209986159267782662955)
  ·
    refine ⟨114193814979238901673994433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76129209986159267782662955 114193814979238901673994433)
    ·
      refine ⟨85645361234429176255495825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114193814979238901673994433 85645361234429176255495825)
      ·
        refine ⟨64234020925821882191621869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85645361234429176255495825 64234020925821882191621869)
        ·
          refine ⟨24087757847183205821858201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64234020925821882191621869 24087757847183205821858201)
          ·
            refine ⟨18065818385387404366393651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087757847183205821858201 18065818385387404366393651)
            ·
              refine ⟨27098727578081106549590477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065818385387404366393651 27098727578081106549590477)
              ·
                refine ⟨10162022841780414956096429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27098727578081106549590477 10162022841780414956096429)
                ·
                  refine ⟨3810758565667655608536161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10162022841780414956096429 3810758565667655608536161)
                  ·
                    refine ⟨2858068924250741706402121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810758565667655608536161 2858068924250741706402121)
                    ·
                      refine ⟨2143551693188056279801591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858068924250741706402121 2143551693188056279801591)
                      ·
                        rfl

theorem cell23_4174552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_4174552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174552 prefixEnd_4174552 := by exact prefixLift 4174552
  have htrace : WordTrace (prefixWord ++ tailWord_4174552) baseStart_4174552 baseEnd_4174552 := by
    simpa [prefixWord, tailWord_4174552, baseEnd_4174552] using wordTrace_append hprefix tailTrace_4174552
  have hstable : (prefixWord ++ tailWord_4174552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174552).length < 2 ^ (prefixWord ++ tailWord_4174552).sum := by decide
  have hdescent : baseEnd_4174552 < baseStart_4174552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174565 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4174565 : Nat := 118140960795 + 4174565 * 2 ^ 59
def prefixEnd_4174565 : Nat := 4983230072969 + 3 ^ 40 * 4174565 * 2
def baseEnd_4174565 : Nat := 2143558368436564728939031

theorem tailTrace_4174565 : CollatzResearch.WordTrace tailWord_4174565 prefixEnd_4174565 2143558368436564728939031 := by
  unfold tailWord_4174565
  simp only [CollatzResearch.WordTrace]
  refine ⟨152258894121271438785549149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101505929414180959190366099 152258894121271438785549149)
  ·
    refine ⟨57097085295476789544580931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152258894121271438785549149 57097085295476789544580931)
    ·
      refine ⟨85645627943215184316871397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57097085295476789544580931 85645627943215184316871397)
      ·
        refine ⟨16058555239352847059413387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85645627943215184316871397 16058555239352847059413387)
        ·
          refine ⟨24087832859029270589120081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058555239352847059413387 24087832859029270589120081)
          ·
            refine ⟨18065874644271952941840061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087832859029270589120081 18065874644271952941840061)
            ·
              refine ⟨6774702991601982353190023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18065874644271952941840061 6774702991601982353190023)
              ·
                refine ⟨10162054487402973529785035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774702991601982353190023 10162054487402973529785035)
                ·
                  refine ⟨15243081731104460294677553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162054487402973529785035 15243081731104460294677553)
                  ·
                    refine ⟨11432311298328345221008165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15243081731104460294677553 11432311298328345221008165)
                    ·
                      refine ⟨2143558368436564728939031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11432311298328345221008165 2143558368436564728939031)
                      ·
                        rfl

theorem cell23_4174565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4174565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174565 prefixEnd_4174565 := by exact prefixLift 4174565
  have htrace : WordTrace (prefixWord ++ tailWord_4174565) baseStart_4174565 baseEnd_4174565 := by
    simpa [prefixWord, tailWord_4174565, baseEnd_4174565] using wordTrace_append hprefix tailTrace_4174565
  have hstable : (prefixWord ++ tailWord_4174565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174565).length < 2 ^ (prefixWord ++ tailWord_4174565).sum := by decide
  have hdescent : baseEnd_4174565 < baseStart_4174565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174575 : List Nat := [1, 1, 2, 1, 5, 4, 2, 7]
def baseStart_4174575 : Nat := 118140960795 + 4174575 * 2 ^ 59
def prefixEnd_4174575 : Nat := 4983230072969 + 3 ^ 40 * 4174575 * 2
def baseEnd_4174575 : Nat := 79391240860855914437555

theorem tailTrace_4174575 : CollatzResearch.WordTrace tailWord_4174575 prefixEnd_4174575 79391240860855914437555 := by
  unfold tailWord_4174575
  simp only [CollatzResearch.WordTrace]
  refine ⟨152259258851235210493413179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101506172567490140328942119 152259258851235210493413179)
  ·
    refine ⟨228388888276852815740119769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152259258851235210493413179 228388888276852815740119769)
    ·
      refine ⟨171291666207639611805089827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228388888276852815740119769 171291666207639611805089827)
      ·
        refine ⟨256937499311459417707634741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171291666207639611805089827 256937499311459417707634741)
        ·
          refine ⟨24087890560449320410090757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256937499311459417707634741 24087890560449320410090757)
          ·
            refine ⟨4516479480084247576892017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24087890560449320410090757 4516479480084247576892017)
            ·
              refine ⟨3387359610063185682669013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516479480084247576892017 3387359610063185682669013)
              ·
                refine ⟨79391240860855914437555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3387359610063185682669013 79391240860855914437555)
                ·
                  rfl

theorem cell23_4174575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 7].length) (baseStart_4174575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174575 prefixEnd_4174575 := by exact prefixLift 4174575
  have htrace : WordTrace (prefixWord ++ tailWord_4174575) baseStart_4174575 baseEnd_4174575 := by
    simpa [prefixWord, tailWord_4174575, baseEnd_4174575] using wordTrace_append hprefix tailTrace_4174575
  have hstable : (prefixWord ++ tailWord_4174575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174575).length < 2 ^ (prefixWord ++ tailWord_4174575).sum := by decide
  have hdescent : baseEnd_4174575 < baseStart_4174575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174580 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4174580 : Nat := 118140960795 + 4174580 * 2 ^ 59
def prefixEnd_4174580 : Nat := 4983230072969 + 3 ^ 40 * 4174580 * 2
def baseEnd_4174580 : Nat := 2143566070646382170251463

theorem tailTrace_4174580 : CollatzResearch.WordTrace tailWord_4174580 prefixEnd_4174580 2143566070646382170251463 := by
  unfold tailWord_4174580
  simp only [CollatzResearch.WordTrace]
  refine ⟨76129720608108548173672597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101506294144144730898230129 76129720608108548173672597)
  ·
    refine ⟨3568580653505088195640903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76129720608108548173672597 3568580653505088195640903)
    ·
      refine ⟨5352870980257632293461355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568580653505088195640903 5352870980257632293461355)
      ·
        refine ⟨8029306470386448440192033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5352870980257632293461355 8029306470386448440192033)
        ·
          refine ⟨6021979852789836330144025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8029306470386448440192033 6021979852789836330144025)
          ·
            refine ⟨4516484889592377247608019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6021979852789836330144025 4516484889592377247608019)
            ·
              refine ⟨6774727334388565871412029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516484889592377247608019 6774727334388565871412029)
              ·
                refine ⟨2540522750395712201779511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6774727334388565871412029 2540522750395712201779511)
                ·
                  refine ⟨3810784125593568302669267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540522750395712201779511 3810784125593568302669267)
                  ·
                    refine ⟨5716176188390352454003901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3810784125593568302669267 5716176188390352454003901)
                    ·
                      refine ⟨2143566070646382170251463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5716176188390352454003901 2143566070646382170251463)
                      ·
                        rfl

theorem cell23_4174580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4174580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174580 prefixEnd_4174580 := by exact prefixLift 4174580
  have htrace : WordTrace (prefixWord ++ tailWord_4174580) baseStart_4174580 baseEnd_4174580 := by
    simpa [prefixWord, tailWord_4174580, baseEnd_4174580] using wordTrace_append hprefix tailTrace_4174580
  have hstable : (prefixWord ++ tailWord_4174580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174580).length < 2 ^ (prefixWord ++ tailWord_4174580).sum := by decide
  have hdescent : baseEnd_4174580 < baseStart_4174580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174595 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 5, 3, 2]
def baseStart_4174595 : Nat := 118140960795 + 4174595 * 2 ^ 59
def prefixEnd_4174595 : Nat := 4983230072969 + 3 ^ 40 * 4174595 * 2
def baseEnd_4174595 : Nat := 2143573772856199611563893

theorem tailTrace_4174595 : CollatzResearch.WordTrace tailWord_4174595 prefixEnd_4174595 2143573772856199611563893 := by
  unfold tailWord_4174595
  simp only [CollatzResearch.WordTrace]
  refine ⟨152259988311162753909141239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101506658874108502606094159 152259988311162753909141239)
  ·
    refine ⟨228389982466744130863711859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152259988311162753909141239 228389982466744130863711859)
    ·
      refine ⟨342584973700116196295567789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228389982466744130863711859 342584973700116196295567789)
      ·
        refine ⟨128469365137543573610837921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342584973700116196295567789 128469365137543573610837921)
        ·
          refine ⟨96352023853157680208128441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128469365137543573610837921 96352023853157680208128441)
          ·
            refine ⟨72264017889868260156096331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96352023853157680208128441 72264017889868260156096331)
            ·
              refine ⟨108396026834802390234144497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72264017889868260156096331 108396026834802390234144497)
              ·
                refine ⟨81297020126101792675608373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108396026834802390234144497 81297020126101792675608373)
                ·
                  refine ⟨7621595636822043063338285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81297020126101792675608373 7621595636822043063338285)
                  ·
                    refine ⟨2858098363808266148751857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7621595636822043063338285 2858098363808266148751857)
                    ·
                      refine ⟨2143573772856199611563893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858098363808266148751857 2143573772856199611563893)
                      ·
                        rfl

theorem cell23_4174595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_4174595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174595 prefixEnd_4174595 := by exact prefixLift 4174595
  have htrace : WordTrace (prefixWord ++ tailWord_4174595) baseStart_4174595 baseEnd_4174595 := by
    simpa [prefixWord, tailWord_4174595, baseEnd_4174595] using wordTrace_append hprefix tailTrace_4174595
  have hstable : (prefixWord ++ tailWord_4174595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174595).length < 2 ^ (prefixWord ++ tailWord_4174595).sum := by decide
  have hdescent : baseEnd_4174595 < baseStart_4174595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174602 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4174602 : Nat := 118140960795 + 4174602 * 2 ^ 59
def prefixEnd_4174602 : Nat := 4983230072969 + 3 ^ 40 * 4174602 * 2
def baseEnd_4174602 : Nat := 2143577367220781084176361

theorem tailTrace_4174602 : CollatzResearch.WordTrace tailWord_4174602 prefixEnd_4174602 2143577367220781084176361 := by
  unfold tailWord_4174602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065060905534348526161515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101506829081424929403097373 38065060905534348526161515)
  ·
    refine ⟨57097591358301522789242273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38065060905534348526161515 57097591358301522789242273)
    ·
      refine ⟨42823193518726142091931705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57097591358301522789242273 42823193518726142091931705)
      ·
        refine ⟨32117395139044606568948779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42823193518726142091931705 32117395139044606568948779)
        ·
          refine ⟨48176092708566909853423169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32117395139044606568948779 48176092708566909853423169)
          ·
            refine ⟨36132069531425182390067377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48176092708566909853423169 36132069531425182390067377)
            ·
              refine ⟨27099052148568886792550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36132069531425182390067377 27099052148568886792550533)
              ·
                refine ⟨5081072277856666273603225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27099052148568886792550533 5081072277856666273603225)
                ·
                  refine ⟨3810804208392499705202419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081072277856666273603225 3810804208392499705202419)
                  ·
                    refine ⟨5716206312588749557803629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3810804208392499705202419 5716206312588749557803629)
                    ·
                      refine ⟨2143577367220781084176361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5716206312588749557803629 2143577367220781084176361)
                      ·
                        rfl

theorem cell23_4174602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4174602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174602 prefixEnd_4174602 := by exact prefixLift 4174602
  have htrace : WordTrace (prefixWord ++ tailWord_4174602) baseStart_4174602 baseEnd_4174602 := by
    simpa [prefixWord, tailWord_4174602, baseEnd_4174602] using wordTrace_append hprefix tailTrace_4174602
  have hstable : (prefixWord ++ tailWord_4174602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174602).length < 2 ^ (prefixWord ++ tailWord_4174602).sum := by decide
  have hdescent : baseEnd_4174602 < baseStart_4174602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174618 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_4174618 : Nat := 118140960795 + 4174618 * 2 ^ 59
def prefixEnd_4174618 : Nat := 4983230072969 + 3 ^ 40 * 4174618 * 2
def baseEnd_4174618 : Nat := 714528527637084340525429

theorem tailTrace_4174618 : CollatzResearch.WordTrace tailWord_4174618 prefixEnd_4174618 714528527637084340525429 := by
  unfold tailWord_4174618
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065206797519857209307127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101507218126719619224819005 38065206797519857209307127)
  ·
    refine ⟨57097810196279785813960691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38065206797519857209307127 57097810196279785813960691)
    ·
      refine ⟨85646715294419678720941037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57097810196279785813960691 85646715294419678720941037)
      ·
        refine ⟨32117518235407379520352889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85646715294419678720941037 32117518235407379520352889)
        ·
          refine ⟨24088138676555534640264667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32117518235407379520352889 24088138676555534640264667)
          ·
            refine ⟨36132208014833301960397001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24088138676555534640264667 36132208014833301960397001)
            ·
              refine ⟨27099156011124976470297751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36132208014833301960397001 27099156011124976470297751)
              ·
                refine ⟨40648734016687464705446627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27099156011124976470297751 40648734016687464705446627)
                ·
                  refine ⟨60973101025031197058169941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40648734016687464705446627 60973101025031197058169941)
                  ·
                    refine ⟨714528527637084340525429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60973101025031197058169941 714528527637084340525429)
                    ·
                      rfl

theorem cell23_4174618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_4174618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174618 prefixEnd_4174618 := by exact prefixLift 4174618
  have htrace : WordTrace (prefixWord ++ tailWord_4174618) baseStart_4174618 baseEnd_4174618 := by
    simpa [prefixWord, tailWord_4174618, baseEnd_4174618] using wordTrace_append hprefix tailTrace_4174618
  have hstable : (prefixWord ++ tailWord_4174618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174618).length < 2 ^ (prefixWord ++ tailWord_4174618).sum := by decide
  have hdescent : baseEnd_4174618 < baseStart_4174618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174642 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_4174642 : Nat := 118140960795 + 4174642 * 2 ^ 59
def prefixEnd_4174642 : Nat := 4983230072969 + 3 ^ 40 * 4174642 * 2
def baseEnd_4174642 : Nat := 2143597906446960927676177

theorem tailTrace_4174642 : CollatzResearch.WordTrace tailWord_4174642 prefixEnd_4174642 2143597906446960927676177 := by
  unfold tailWord_4174642
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065425635498120234025545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101507801694661653957401453 38065425635498120234025545)
  ·
    refine ⟨28549069226623590175519159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38065425635498120234025545 28549069226623590175519159)
    ·
      refine ⟨42823603839935385263278739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28549069226623590175519159 42823603839935385263278739)
      ·
        refine ⟨64235405759903077894918109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42823603839935385263278739 64235405759903077894918109)
        ·
          refine ⟨24088277159963654210594291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64235405759903077894918109 24088277159963654210594291)
          ·
            refine ⟨36132415739945481315891437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24088277159963654210594291 36132415739945481315891437)
            ·
              refine ⟨13549655902479555493459289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36132415739945481315891437 13549655902479555493459289)
              ·
                refine ⟨10162241926859666620094467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13549655902479555493459289 10162241926859666620094467)
                ·
                  refine ⟨15243362890289499930141701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162241926859666620094467 15243362890289499930141701)
                  ·
                    refine ⟨2858130541929281236901569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15243362890289499930141701 2858130541929281236901569)
                    ·
                      refine ⟨2143597906446960927676177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858130541929281236901569 2143597906446960927676177)
                      ·
                        rfl

theorem cell23_4174642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_4174642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174642 prefixEnd_4174642 := by exact prefixLift 4174642
  have htrace : WordTrace (prefixWord ++ tailWord_4174642) baseStart_4174642 baseEnd_4174642 := by
    simpa [prefixWord, tailWord_4174642, baseEnd_4174642] using wordTrace_append hprefix tailTrace_4174642
  have hstable : (prefixWord ++ tailWord_4174642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174642).length < 2 ^ (prefixWord ++ tailWord_4174642).sum := by decide
  have hdescent : baseEnd_4174642 < baseStart_4174642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174645 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4174645 : Nat := 118140960795 + 4174645 * 2 ^ 59
def prefixEnd_4174645 : Nat := 4983230072969 + 3 ^ 40 * 4174645 * 2
def baseEnd_4174645 : Nat := 2143599446888924415938663

theorem tailTrace_4174645 : CollatzResearch.WordTrace tailWord_4174645 prefixEnd_4174645 2143599446888924415938663 := by
  unfold tailWord_4174645
  simp only [CollatzResearch.WordTrace]
  refine ⟨152261811960981612448461389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101507874640654408298974259 152261811960981612448461389)
  ·
    refine ⟨57098179485368104668173021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152261811960981612448461389 57098179485368104668173021)
    ·
      refine ⟨21411817307013039250564883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57098179485368104668173021 21411817307013039250564883)
      ·
        refine ⟨32117725960519558875847325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21411817307013039250564883 32117725960519558875847325)
        ·
          refine ⟨12044147235194834578442747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32117725960519558875847325 12044147235194834578442747)
          ·
            refine ⟨18066220852792251867664121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044147235194834578442747 18066220852792251867664121)
            ·
              refine ⟨13549665639594188900748091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18066220852792251867664121 13549665639594188900748091)
              ·
                refine ⟨20324498459391283351122137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549665639594188900748091 20324498459391283351122137)
                ·
                  refine ⟨15243373844543462513341603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20324498459391283351122137 15243373844543462513341603)
                  ·
                    refine ⟨22865060766815193770012405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15243373844543462513341603 22865060766815193770012405)
                    ·
                      refine ⟨2143599446888924415938663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22865060766815193770012405 2143599446888924415938663)
                      ·
                        rfl

theorem cell23_4174645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4174645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174645 prefixEnd_4174645 := by exact prefixLift 4174645
  have htrace : WordTrace (prefixWord ++ tailWord_4174645) baseStart_4174645 baseEnd_4174645 := by
    simpa [prefixWord, tailWord_4174645, baseEnd_4174645] using wordTrace_append hprefix tailTrace_4174645
  have hstable : (prefixWord ++ tailWord_4174645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174645).length < 2 ^ (prefixWord ++ tailWord_4174645).sum := by decide
  have hdescent : baseEnd_4174645 < baseStart_4174645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174659 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 2, 2, 2]
def baseStart_4174659 : Nat := 118140960795 + 4174659 * 2 ^ 59
def prefixEnd_4174659 : Nat := 4983230072969 + 3 ^ 40 * 4174659 * 2
def baseEnd_4174659 : Nat := 2143606635618087361163599

theorem tailTrace_4174659 : CollatzResearch.WordTrace tailWord_4174659 prefixEnd_4174659 2143606635618087361163599 := by
  unfold tailWord_4174659
  simp only [CollatzResearch.WordTrace]
  refine ⟨152262322582930892839471031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101508215055287261892980687 152262322582930892839471031)
  ·
    refine ⟨228393483874396339259206547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152262322582930892839471031 228393483874396339259206547)
    ·
      refine ⟨342590225811594508888809821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228393483874396339259206547 342590225811594508888809821)
      ·
        refine ⟨128471334679347940833303683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342590225811594508888809821 128471334679347940833303683)
        ·
          refine ⟨192707002019021911249955525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128471334679347940833303683 192707002019021911249955525)
          ·
            refine ⟨36132562878566608359366661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192707002019021911249955525 36132562878566608359366661)
            ·
              refine ⟨6774855539731239067381249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36132562878566608359366661 6774855539731239067381249)
              ·
                refine ⟨5081141654798429300535937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6774855539731239067381249 5081141654798429300535937)
                ·
                  refine ⟨3810856241098821975401953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081141654798429300535937 3810856241098821975401953)
                  ·
                    refine ⟨2858142180824116481551465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810856241098821975401953 2858142180824116481551465)
                    ·
                      refine ⟨2143606635618087361163599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858142180824116481551465 2143606635618087361163599)
                      ·
                        rfl

theorem cell23_4174659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_4174659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174659 prefixEnd_4174659 := by exact prefixLift 4174659
  have htrace : WordTrace (prefixWord ++ tailWord_4174659) baseStart_4174659 baseEnd_4174659 := by
    simpa [prefixWord, tailWord_4174659, baseEnd_4174659] using wordTrace_append hprefix tailTrace_4174659
  have hstable : (prefixWord ++ tailWord_4174659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174659).length < 2 ^ (prefixWord ++ tailWord_4174659).sum := by decide
  have hdescent : baseEnd_4174659 < baseStart_4174659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174695 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 7]
def baseStart_4174695 : Nat := 118140960795 + 4174695 * 2 ^ 59
def prefixEnd_4174695 : Nat := 4983230072969 + 3 ^ 40 * 4174695 * 2
def baseEnd_4174695 : Nat := 714541706973883073437811

theorem tailTrace_4174695 : CollatzResearch.WordTrace tailWord_4174695 prefixEnd_4174695 714541706973883073437811 := by
  unfold tailWord_4174695
  simp only [CollatzResearch.WordTrace]
  refine ⟨152263635610800470987781539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101509090407200313991854359 152263635610800470987781539)
  ·
    refine ⟨228395453416200706481672309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152263635610800470987781539 228395453416200706481672309)
    ·
      refine ⟨21412073757768816232656779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228395453416200706481672309 21412073757768816232656779)
      ·
        refine ⟨32118110636653224348985169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21412073757768816232656779 32118110636653224348985169)
        ·
          refine ⟨24088582977489918261738877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32118110636653224348985169 24088582977489918261738877)
          ·
            refine ⟨9033218616558719348152079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24088582977489918261738877 9033218616558719348152079)
            ·
              refine ⟨13549827924838079022228119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033218616558719348152079 13549827924838079022228119)
              ·
                refine ⟨20324741887257118533342179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549827924838079022228119 20324741887257118533342179)
                ·
                  refine ⟨30487112830885677800013269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20324741887257118533342179 30487112830885677800013269)
                  ·
                    refine ⟨714541706973883073437811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30487112830885677800013269 714541706973883073437811)
                    ·
                      rfl

theorem cell23_4174695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_4174695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174695 prefixEnd_4174695 := by exact prefixLift 4174695
  have htrace : WordTrace (prefixWord ++ tailWord_4174695) baseStart_4174695 baseEnd_4174695 := by
    simpa [prefixWord, tailWord_4174695, baseEnd_4174695] using wordTrace_append hprefix tailTrace_4174695
  have hstable : (prefixWord ++ tailWord_4174695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174695).length < 2 ^ (prefixWord ++ tailWord_4174695).sum := by decide
  have hdescent : baseEnd_4174695 < baseStart_4174695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174715 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4]
def baseStart_4174715 : Nat := 118140960795 + 4174715 * 2 ^ 59
def prefixEnd_4174715 : Nat := 4983230072969 + 3 ^ 40 * 4174715 * 2
def baseEnd_4174715 : Nat := 2143635390534739142063341

theorem tailTrace_4174715 : CollatzResearch.WordTrace tailWord_4174715 prefixEnd_4174715 2143635390534739142063341 := by
  unfold tailWord_4174715
  simp only [CollatzResearch.WordTrace]
  refine ⟨152264365070728014403509599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101509576713818676269006399 152264365070728014403509599)
  ·
    refine ⟨228396547606092021605264399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152264365070728014403509599 228396547606092021605264399)
    ·
      refine ⟨342594821409138032407896599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228396547606092021605264399 342594821409138032407896599)
      ·
        refine ⟨513892232113707048611844899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342594821409138032407896599 513892232113707048611844899)
        ·
          refine ⟨770838348170560572917767349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513892232113707048611844899 770838348170560572917767349)
          ·
            refine ⟨72266095140990053711040689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 770838348170560572917767349 72266095140990053711040689)
            ·
              refine ⟨54199571355742540283280517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72266095140990053711040689 54199571355742540283280517)
              ·
                refine ⟨10162419629201726303115097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54199571355742540283280517 10162419629201726303115097)
                ·
                  refine ⟨7621814721901294727336323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10162419629201726303115097 7621814721901294727336323)
                  ·
                    refine ⟨11432722082851942091004485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621814721901294727336323 11432722082851942091004485)
                    ·
                      refine ⟨2143635390534739142063341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11432722082851942091004485 2143635390534739142063341)
                      ·
                        rfl

theorem cell23_4174715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4].length) (baseStart_4174715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174715 prefixEnd_4174715 := by exact prefixLift 4174715
  have htrace : WordTrace (prefixWord ++ tailWord_4174715) baseStart_4174715 baseEnd_4174715 := by
    simpa [prefixWord, tailWord_4174715, baseEnd_4174715] using wordTrace_append hprefix tailTrace_4174715
  have hstable : (prefixWord ++ tailWord_4174715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174715).length < 2 ^ (prefixWord ++ tailWord_4174715).sum := by decide
  have hdescent : baseEnd_4174715 < baseStart_4174715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174732 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_4174732 : Nat := 118140960795 + 4174732 * 2 ^ 59
def prefixEnd_4174732 : Nat := 4983230072969 + 3 ^ 40 * 4174732 * 2
def baseEnd_4174732 : Nat := 2143644119705865575550763

theorem tailTrace_4174732 : CollatzResearch.WordTrace tailWord_4174732 prefixEnd_4174732 2143644119705865575550763 := by
  unfold tailWord_4174732
  simp only [CollatzResearch.WordTrace]
  refine ⟨76132492555833213153439225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101509990074444284204585633 76132492555833213153439225)
  ·
    refine ⟨57099369416874909865079419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76132492555833213153439225 57099369416874909865079419)
    ·
      refine ⟨85649054125312364797619129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57099369416874909865079419 85649054125312364797619129)
      ·
        refine ⟨64236790593984273598214347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85649054125312364797619129 64236790593984273598214347)
        ·
          refine ⟨96355185890976410397321521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64236790593984273598214347 96355185890976410397321521)
          ·
            refine ⟨72266389418232307797991141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96355185890976410397321521 72266389418232307797991141)
            ·
              refine ⟨13549948015918557712123339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72266389418232307797991141 13549948015918557712123339)
              ·
                refine ⟨20324922023877836568185009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549948015918557712123339 20324922023877836568185009)
                ·
                  refine ⟨15243691517908377426138757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20324922023877836568185009 15243691517908377426138757)
                  ·
                    refine ⟨2858192159607820767401017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15243691517908377426138757 2858192159607820767401017)
                    ·
                      refine ⟨2143644119705865575550763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858192159607820767401017 2143644119705865575550763)
                      ·
                        rfl

theorem cell23_4174732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_4174732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174732 prefixEnd_4174732 := by exact prefixLift 4174732
  have htrace : WordTrace (prefixWord ++ tailWord_4174732) baseStart_4174732 baseEnd_4174732 := by
    simpa [prefixWord, tailWord_4174732, baseEnd_4174732] using wordTrace_append hprefix tailTrace_4174732
  have hstable : (prefixWord ++ tailWord_4174732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174732).length < 2 ^ (prefixWord ++ tailWord_4174732).sum := by decide
  have hdescent : baseEnd_4174732 < baseStart_4174732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174769 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4174769 : Nat := 118140960795 + 4174769 * 2 ^ 59
def prefixEnd_4174769 : Nat := 4983230072969 + 3 ^ 40 * 4174769 * 2
def baseEnd_4174769 : Nat := 2143663118490081930788093

theorem tailTrace_4174769 : CollatzResearch.WordTrace tailWord_4174769 prefixEnd_4174769 2143663118490081930788093 := by
  unfold tailWord_4174769
  simp only [CollatzResearch.WordTrace]
  refine ⟨152266334612532381625975361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101510889741688254417316907 152266334612532381625975361)
  ·
    refine ⟨114199750959399286219481521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152266334612532381625975361 114199750959399286219481521)
    ·
      refine ⟨85649813219549464664611141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114199750959399286219481521 85649813219549464664611141)
      ·
        refine ⟨16059339978665524624614589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85649813219549464664611141 16059339978665524624614589)
        ·
          refine ⟨6022252491999571734230471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16059339978665524624614589 6022252491999571734230471)
          ·
            refine ⟨9033378737999357601345707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022252491999571734230471 9033378737999357601345707)
            ·
              refine ⟨13550068106999036402018561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033378737999357601345707 13550068106999036402018561)
              ·
                refine ⟨10162551080249277301513921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13550068106999036402018561 10162551080249277301513921)
                ·
                  refine ⟨7621913310186957976135441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10162551080249277301513921 7621913310186957976135441)
                  ·
                    refine ⟨5716434982640218482101581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7621913310186957976135441 5716434982640218482101581)
                    ·
                      refine ⟨2143663118490081930788093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5716434982640218482101581 2143663118490081930788093)
                      ·
                        rfl

theorem cell23_4174769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4174769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174769 prefixEnd_4174769 := by exact prefixLift 4174769
  have htrace : WordTrace (prefixWord ++ tailWord_4174769) baseStart_4174769 baseEnd_4174769 := by
    simpa [prefixWord, tailWord_4174769, baseEnd_4174769] using wordTrace_append hprefix tailTrace_4174769
  have hstable : (prefixWord ++ tailWord_4174769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174769).length < 2 ^ (prefixWord ++ tailWord_4174769).sum := by decide
  have hdescent : baseEnd_4174769 < baseStart_4174769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174776 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 1, 4]
def baseStart_4174776 : Nat := 118140960795 + 4174776 * 2 ^ 59
def prefixEnd_4174776 : Nat := 4983230072969 + 3 ^ 40 * 4174776 * 2
def baseEnd_4174776 : Nat := 714555570951554467800187

theorem tailTrace_4174776 : CollatzResearch.WordTrace tailWord_4174776 prefixEnd_4174776 714555570951554467800187 := by
  unfold tailWord_4174776
  simp only [CollatzResearch.WordTrace]
  refine ⟨76133294961753510910740091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101511059949004681214320121 76133294961753510910740091)
  ·
    refine ⟨114199942442630266366110137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76133294961753510910740091 114199942442630266366110137)
    ·
      refine ⟨85649956831972699774582603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114199942442630266366110137 85649956831972699774582603)
      ·
        refine ⟨128474935247959049661873905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85649956831972699774582603 128474935247959049661873905)
        ·
          refine ⟨96356201435969287246405429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128474935247959049661873905 96356201435969287246405429)
          ·
            refine ⟨9033393884622120679350509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96356201435969287246405429 9033393884622120679350509)
            ·
              refine ⟨3387522706733295254756441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9033393884622120679350509 3387522706733295254756441)
              ·
                refine ⟨2540642030049971441067331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387522706733295254756441 2540642030049971441067331)
                ·
                  refine ⟨3810963045074957161600997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540642030049971441067331 3810963045074957161600997)
                  ·
                    refine ⟨714555570951554467800187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3810963045074957161600997 714555570951554467800187)
                    ·
                      rfl

theorem cell23_4174776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_4174776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174776 prefixEnd_4174776 := by exact prefixLift 4174776
  have htrace : WordTrace (prefixWord ++ tailWord_4174776) baseStart_4174776 baseEnd_4174776 := by
    simpa [prefixWord, tailWord_4174776, baseEnd_4174776] using wordTrace_append hprefix tailTrace_4174776
  have hstable : (prefixWord ++ tailWord_4174776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174776).length < 2 ^ (prefixWord ++ tailWord_4174776).sum := by decide
  have hdescent : baseEnd_4174776 < baseStart_4174776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174809 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 2, 3, 2]
def baseStart_4174809 : Nat := 118140960795 + 4174809 * 2 ^ 59
def prefixEnd_4174809 : Nat := 4983230072969 + 3 ^ 40 * 4174809 * 2
def baseEnd_4174809 : Nat := 2143683657716261774287909

theorem tailTrace_4174809 : CollatzResearch.WordTrace tailWord_4174809 prefixEnd_4174809 2143683657716261774287909 := by
  unfold tailWord_4174809
  simp only [CollatzResearch.WordTrace]
  refine ⟨152267793532387468457431481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101511862354924978971620987 152267793532387468457431481)
  ·
    refine ⟨114200845149290601343073611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152267793532387468457431481 114200845149290601343073611)
    ·
      refine ⟨171301267723935902014610417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114200845149290601343073611 171301267723935902014610417)
      ·
        refine ⟨128475950792951926510957813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171301267723935902014610417 128475950792951926510957813)
        ·
          refine ⟨12044620386839243110402295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128475950792951926510957813 12044620386839243110402295)
          ·
            refine ⟨18066930580258864665603443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044620386839243110402295 18066930580258864665603443)
            ·
              refine ⟨27100395870388296998405165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066930580258864665603443 27100395870388296998405165)
              ·
                refine ⟨10162648451395611374401937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27100395870388296998405165 10162648451395611374401937)
                ·
                  refine ⟨7621986338546708530801453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10162648451395611374401937 7621986338546708530801453)
                  ·
                    refine ⟨2858244876955015699050545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7621986338546708530801453 2858244876955015699050545)
                    ·
                      refine ⟨2143683657716261774287909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858244876955015699050545 2143683657716261774287909)
                      ·
                        rfl

theorem cell23_4174809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_4174809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174809 prefixEnd_4174809 := by exact prefixLift 4174809
  have htrace : WordTrace (prefixWord ++ tailWord_4174809) baseStart_4174809 baseEnd_4174809 := by
    simpa [prefixWord, tailWord_4174809, baseEnd_4174809] using wordTrace_append hprefix tailTrace_4174809
  have hstable : (prefixWord ++ tailWord_4174809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174809).length < 2 ^ (prefixWord ++ tailWord_4174809).sum := by decide
  have hdescent : baseEnd_4174809 < baseStart_4174809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174819 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 1, 5]
def baseStart_4174819 : Nat := 118140960795 + 4174819 * 2 ^ 59
def prefixEnd_4174819 : Nat := 4983230072969 + 3 ^ 40 * 4174819 * 2
def baseEnd_4174819 : Nat := 714562930840935578387621

theorem tailTrace_4174819 : CollatzResearch.WordTrace tailWord_4174819 prefixEnd_4174819 714562930840935578387621 := by
  unfold tailWord_4174819
  simp only [CollatzResearch.WordTrace]
  refine ⟨152268158262351240165295511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101512105508234160110197007 152268158262351240165295511)
  ·
    refine ⟨228402237393526860247943267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152268158262351240165295511 228402237393526860247943267)
    ·
      refine ⟨342603356090290290371914901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228402237393526860247943267 342603356090290290371914901)
      ·
        refine ⟨16059532316732357361183511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342603356090290290371914901 16059532316732357361183511)
        ·
          refine ⟨24089298475098536041775267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16059532316732357361183511 24089298475098536041775267)
          ·
            refine ⟨36133947712647804062662901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24089298475098536041775267 36133947712647804062662901)
            ·
              refine ⟨3387557598060731630874647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36133947712647804062662901 3387557598060731630874647)
              ·
                refine ⟨5081336397091097446311971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387557598060731630874647 5081336397091097446311971)
                ·
                  refine ⟨7622004595636646169467957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081336397091097446311971 7622004595636646169467957)
                  ·
                    refine ⟨714562930840935578387621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7622004595636646169467957 714562930840935578387621)
                    ·
                      rfl

theorem cell23_4174819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 5].length) (baseStart_4174819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174819 prefixEnd_4174819 := by exact prefixLift 4174819
  have htrace : WordTrace (prefixWord ++ tailWord_4174819) baseStart_4174819 baseEnd_4174819 := by
    simpa [prefixWord, tailWord_4174819, baseEnd_4174819] using wordTrace_append hprefix tailTrace_4174819
  have hstable : (prefixWord ++ tailWord_4174819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174819).length < 2 ^ (prefixWord ++ tailWord_4174819).sum := by decide
  have hdescent : baseEnd_4174819 < baseStart_4174819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174833 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 1, 1, 3]
def baseStart_4174833 : Nat := 118140960795 + 4174833 * 2 ^ 59
def prefixEnd_4174833 : Nat := 4983230072969 + 3 ^ 40 * 4174833 * 2
def baseEnd_4174833 : Nat := 2143695981251969680387799

theorem tailTrace_4174833 : CollatzResearch.WordTrace tailWord_4174833 prefixEnd_4174833 2143695981251969680387799 := by
  unfold tailWord_4174833
  simp only [CollatzResearch.WordTrace]
  refine ⟨152268668884300520556305153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101512445922867013704203435 152268668884300520556305153)
  ·
    refine ⟨114201501663225390417228865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152268668884300520556305153 114201501663225390417228865)
    ·
      refine ⟨85651126247419042812921649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114201501663225390417228865 85651126247419042812921649)
      ·
        refine ⟨64238344685564282109691237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85651126247419042812921649 64238344685564282109691237)
        ·
          refine ⟨12044689628543302895567107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64238344685564282109691237 12044689628543302895567107)
          ·
            refine ⟨18067034442814954343350661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044689628543302895567107 18067034442814954343350661)
            ·
              refine ⟨3387568958027803939378249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18067034442814954343350661 3387568958027803939378249)
              ·
                refine ⟨2540676718520852954533687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387568958027803939378249 2540676718520852954533687)
                ·
                  refine ⟨3811015077781279431800531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540676718520852954533687 3811015077781279431800531)
                  ·
                    refine ⟨5716522616671919147700797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3811015077781279431800531 5716522616671919147700797)
                    ·
                      refine ⟨2143695981251969680387799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5716522616671919147700797 2143695981251969680387799)
                      ·
                        rfl

theorem cell23_4174833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_4174833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174833 prefixEnd_4174833 := by exact prefixLift 4174833
  have htrace : WordTrace (prefixWord ++ tailWord_4174833) baseStart_4174833 baseEnd_4174833 := by
    simpa [prefixWord, tailWord_4174833, baseEnd_4174833] using wordTrace_append hprefix tailTrace_4174833
  have hstable : (prefixWord ++ tailWord_4174833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174833).length < 2 ^ (prefixWord ++ tailWord_4174833).sum := by decide
  have hdescent : baseEnd_4174833 < baseStart_4174833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174849 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4174849 : Nat := 118140960795 + 4174849 * 2 ^ 59
def prefixEnd_4174849 : Nat := 4983230072969 + 3 ^ 40 * 4174849 * 2
def baseEnd_4174849 : Nat := 714568065647480539262575

theorem tailTrace_4174849 : CollatzResearch.WordTrace tailWord_4174849 prefixEnd_4174849 714568065647480539262575 := by
  unfold tailWord_4174849
  simp only [CollatzResearch.WordTrace]
  refine ⟨152269252452242555288887601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101512834968161703525925067 152269252452242555288887601)
  ·
    refine ⟨114201939339181916466665701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152269252452242555288887601 114201939339181916466665701)
    ·
      refine ⟨21412863626096609337499819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114201939339181916466665701 21412863626096609337499819)
      ·
        refine ⟨32119295439144914006249729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21412863626096609337499819 32119295439144914006249729)
        ·
          refine ⟨24089471579358685504687297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32119295439144914006249729 24089471579358685504687297)
          ·
            refine ⟨18067103684519014128515473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24089471579358685504687297 18067103684519014128515473)
            ·
              refine ⟨13550327763389260596386605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18067103684519014128515473 13550327763389260596386605)
              ·
                refine ⟨5081372911270972723644977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13550327763389260596386605 5081372911270972723644977)
                ·
                  refine ⟨3811029683453229542733733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081372911270972723644977 3811029683453229542733733)
                  ·
                    refine ⟨714568065647480539262575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811029683453229542733733 714568065647480539262575)
                    ·
                      rfl

theorem cell23_4174849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4174849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174849 prefixEnd_4174849 := by exact prefixLift 4174849
  have htrace : WordTrace (prefixWord ++ tailWord_4174849) baseStart_4174849 baseEnd_4174849 := by
    simpa [prefixWord, tailWord_4174849, baseEnd_4174849] using wordTrace_append hprefix tailTrace_4174849
  have hstable : (prefixWord ++ tailWord_4174849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174849).length < 2 ^ (prefixWord ++ tailWord_4174849).sum := by decide
  have hdescent : baseEnd_4174849 < baseStart_4174849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174856 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_4174856 : Nat := 118140960795 + 4174856 * 2 ^ 59
def prefixEnd_4174856 : Nat := 4983230072969 + 3 ^ 40 * 4174856 * 2
def baseEnd_4174856 : Nat := 2143707791307023090400193

theorem tailTrace_4174856 : CollatzResearch.WordTrace tailWord_4174856 prefixEnd_4174856 2143707791307023090400193 := by
  unfold tailWord_4174856
  simp only [CollatzResearch.WordTrace]
  refine ⟨76134753881608597742196211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101513005175478130322928281 76134753881608597742196211)
  ·
    refine ⟨114202130822412896613294317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76134753881608597742196211 114202130822412896613294317)
    ·
      refine ⟨42825799058404836229985369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114202130822412896613294317 42825799058404836229985369)
      ·
        refine ⟨32119349293803627172489027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42825799058404836229985369 32119349293803627172489027)
        ·
          refine ⟨48179023940705440758733541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32119349293803627172489027 48179023940705440758733541)
          ·
            refine ⟨9033566988882270142262539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48179023940705440758733541 9033566988882270142262539)
            ·
              refine ⟨13550350483323405213393809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033566988882270142262539 13550350483323405213393809)
              ·
                refine ⟨10162762862492553910045357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13550350483323405213393809 10162762862492553910045357)
                ·
                  refine ⟨3811036073434707716267009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10162762862492553910045357 3811036073434707716267009)
                  ·
                    refine ⟨2858277055076030787200257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3811036073434707716267009 2858277055076030787200257)
                    ·
                      refine ⟨2143707791307023090400193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858277055076030787200257 2143707791307023090400193)
                      ·
                        rfl

theorem cell23_4174856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_4174856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174856 prefixEnd_4174856 := by exact prefixLift 4174856
  have htrace : WordTrace (prefixWord ++ tailWord_4174856) baseStart_4174856 baseEnd_4174856 := by
    simpa [prefixWord, tailWord_4174856, baseEnd_4174856] using wordTrace_append hprefix tailTrace_4174856
  have hstable : (prefixWord ++ tailWord_4174856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174856).length < 2 ^ (prefixWord ++ tailWord_4174856).sum := by decide
  have hdescent : baseEnd_4174856 < baseStart_4174856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174876 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4174876 : Nat := 118140960795 + 4174876 * 2 ^ 59
def prefixEnd_4174876 : Nat := 4983230072969 + 3 ^ 40 * 4174876 * 2
def baseEnd_4174876 : Nat := 2143718060920113012150101

theorem tailTrace_4174876 : CollatzResearch.WordTrace tailWord_4174876 prefixEnd_4174876 2143718060920113012150101 := by
  unfold tailWord_4174876
  simp only [CollatzResearch.WordTrace]
  refine ⟨76135118611572369450060241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101513491482096492600080321 76135118611572369450060241)
  ·
    refine ⟨57101338958679277087545181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76135118611572369450060241 57101338958679277087545181)
    ·
      refine ⟨21413002109504728907829443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57101338958679277087545181 21413002109504728907829443)
      ·
        refine ⟨32119503164257093361744165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413002109504728907829443 32119503164257093361744165)
        ·
          refine ⟨6022406843298205005327031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32119503164257093361744165 6022406843298205005327031)
          ·
            refine ⟨9033610264947307507990547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022406843298205005327031 9033610264947307507990547)
            ·
              refine ⟨13550415397420961261985821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033610264947307507990547 13550415397420961261985821)
              ·
                refine ⟨5081405774032860473244683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13550415397420961261985821 5081405774032860473244683)
                ·
                  refine ⟨7622108661049290709867025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081405774032860473244683 7622108661049290709867025)
                  ·
                    refine ⟨5716581495786968032400269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622108661049290709867025 5716581495786968032400269)
                    ·
                      refine ⟨2143718060920113012150101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5716581495786968032400269 2143718060920113012150101)
                      ·
                        rfl

theorem cell23_4174876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4174876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174876 prefixEnd_4174876 := by exact prefixLift 4174876
  have htrace : WordTrace (prefixWord ++ tailWord_4174876) baseStart_4174876 baseEnd_4174876 := by
    simpa [prefixWord, tailWord_4174876, baseEnd_4174876] using wordTrace_append hprefix tailTrace_4174876
  have hstable : (prefixWord ++ tailWord_4174876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174876).length < 2 ^ (prefixWord ++ tailWord_4174876).sum := by decide
  have hdescent : baseEnd_4174876 < baseStart_4174876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174929 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_4174929 : Nat := 118140960795 + 4174929 * 2 ^ 59
def prefixEnd_4174929 : Nat := 4983230072969 + 3 ^ 40 * 4174929 * 2
def baseEnd_4174929 : Nat := 2143745275394801304787357

theorem tailTrace_4174929 : CollatzResearch.WordTrace tailWord_4174929 prefixEnd_4174929 2143745275394801304787357 := by
  unfold tailWord_4174929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152272170291952728951799841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101514780194635152634533227 152272170291952728951799841)
  ·
    refine ⟨114204127718964546713849881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152272170291952728951799841 114204127718964546713849881)
    ·
      refine ⟨85653095789223410035387411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114204127718964546713849881 85653095789223410035387411)
      ·
        refine ⟨128479643683835115053081117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85653095789223410035387411 128479643683835115053081117)
        ·
          refine ⟨48179866381438168144905419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128479643683835115053081117 48179866381438168144905419)
          ·
            refine ⟨72269799572157252217358129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48179866381438168144905419 72269799572157252217358129)
            ·
              refine ⟨54202349679117939163018597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72269799572157252217358129 54202349679117939163018597)
              ·
                refine ⟨10162940564834613593065987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54202349679117939163018597 10162940564834613593065987)
                ·
                  refine ⟨15244410847251920389598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162940564834613593065987 15244410847251920389598981)
                  ·
                    refine ⟨2858327033859735073049809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15244410847251920389598981 2858327033859735073049809)
                    ·
                      refine ⟨2143745275394801304787357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858327033859735073049809 2143745275394801304787357)
                      ·
                        rfl

theorem cell23_4174929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_4174929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174929 prefixEnd_4174929 := by exact prefixLift 4174929
  have htrace : WordTrace (prefixWord ++ tailWord_4174929) baseStart_4174929 baseEnd_4174929 := by
    simpa [prefixWord, tailWord_4174929, baseEnd_4174929] using wordTrace_append hprefix tailTrace_4174929
  have hstable : (prefixWord ++ tailWord_4174929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174929).length < 2 ^ (prefixWord ++ tailWord_4174929).sum := by decide
  have hdescent : baseEnd_4174929 < baseStart_4174929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174932 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4174932 : Nat := 118140960795 + 4174932 * 2 ^ 59
def prefixEnd_4174932 : Nat := 4983230072969 + 3 ^ 40 * 4174932 * 2
def baseEnd_4174932 : Nat := 2143746815836764793049843

theorem tailTrace_4174932 : CollatzResearch.WordTrace tailWord_4174932 prefixEnd_4174932 2143746815836764793049843 := by
  unfold tailWord_4174932
  simp only [CollatzResearch.WordTrace]
  refine ⟨76136139855470930232079525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101514853140627906976106033 76136139855470930232079525)
  ·
    refine ⟨14275526222900799418514911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76136139855470930232079525 14275526222900799418514911)
    ·
      refine ⟨21413289334351199127772367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275526222900799418514911 21413289334351199127772367)
      ·
        refine ⟨32119934001526798691658551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413289334351199127772367 32119934001526798691658551)
        ·
          refine ⟨48179901002290198037487827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32119934001526798691658551 48179901002290198037487827)
          ·
            refine ⟨72269851503435297056231741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48179901002290198037487827 72269851503435297056231741)
            ·
              refine ⟨27101194313788236396086903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72269851503435297056231741 27101194313788236396086903)
              ·
                refine ⟨40651791470682354594130355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27101194313788236396086903 40651791470682354594130355)
                ·
                  refine ⟨60977687206023531891195533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40651791470682354594130355 60977687206023531891195533)
                  ·
                    refine ⟨22866632702258824459198325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60977687206023531891195533 22866632702258824459198325)
                    ·
                      refine ⟨2143746815836764793049843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22866632702258824459198325 2143746815836764793049843)
                      ·
                        rfl

theorem cell23_4174932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4174932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174932 prefixEnd_4174932 := by exact prefixLift 4174932
  have htrace : WordTrace (prefixWord ++ tailWord_4174932) baseStart_4174932 baseEnd_4174932 := by
    simpa [prefixWord, tailWord_4174932, baseEnd_4174932] using wordTrace_append hprefix tailTrace_4174932
  have hstable : (prefixWord ++ tailWord_4174932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174932).length < 2 ^ (prefixWord ++ tailWord_4174932).sum := by decide
  have hdescent : baseEnd_4174932 < baseStart_4174932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174999 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 2, 5]
def baseStart_4174999 : Nat := 118140960795 + 4174999 * 2 ^ 59
def prefixEnd_4174999 : Nat := 4983230072969 + 3 ^ 40 * 4174999 * 2
def baseEnd_4174999 : Nat := 714593739680205343637345

theorem tailTrace_4174999 : CollatzResearch.WordTrace tailWord_4174999 prefixEnd_4174999 714593739680205343637345 := by
  unfold tailWord_4174999
  simp only [CollatzResearch.WordTrace]
  refine ⟨152274723401699130906848051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101516482267799420604565367 152274723401699130906848051)
  ·
    refine ⟨228412085102548696360272077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152274723401699130906848051 228412085102548696360272077)
    ·
      refine ⟨85654531913455761135102029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228412085102548696360272077 85654531913455761135102029)
      ·
        refine ⟨32120449467545910425663261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85654531913455761135102029 32120449467545910425663261)
        ·
          refine ⟨12045168550329716409623723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32120449467545910425663261 12045168550329716409623723)
          ·
            refine ⟨18067752825494574614435585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045168550329716409623723 18067752825494574614435585)
            ·
              refine ⟨13550814619120930960826689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18067752825494574614435585 13550814619120930960826689)
              ·
                refine ⟨10163110964340698220620017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13550814619120930960826689 10163110964340698220620017)
                ·
                  refine ⟨7622333223255523665465013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163110964340698220620017 7622333223255523665465013)
                  ·
                    refine ⟨714593739680205343637345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7622333223255523665465013 714593739680205343637345)
                    ·
                      rfl

theorem cell23_4174999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_4174999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4174999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4174999 prefixEnd_4174999 := by exact prefixLift 4174999
  have htrace : WordTrace (prefixWord ++ tailWord_4174999) baseStart_4174999 baseEnd_4174999 := by
    simpa [prefixWord, tailWord_4174999, baseEnd_4174999] using wordTrace_append hprefix tailTrace_4174999
  have hstable : (prefixWord ++ tailWord_4174999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174999).length < 2 ^ (prefixWord ++ tailWord_4174999).sum := by decide
  have hdescent : baseEnd_4174999 < baseStart_4174999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175032 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_4175032 : Nat := 118140960795 + 4175032 * 2 ^ 59
def prefixEnd_4175032 : Nat := 4983230072969 + 3 ^ 40 * 4175032 * 2
def baseEnd_4175032 : Nat := 2143798163902214401799383

theorem tailTrace_4175032 : CollatzResearch.WordTrace tailWord_4175032 prefixEnd_4175032 2143798163902214401799383 := by
  unfold tailWord_4175032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137963505289788771399675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101517284673719718361866233 76137963505289788771399675)
  ·
    refine ⟨114206945257934683157099513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76137963505289788771399675 114206945257934683157099513)
    ·
      refine ⟨85655208943451012367824635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114206945257934683157099513 85655208943451012367824635)
      ·
        refine ⟨128482813415176518551736953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85655208943451012367824635 128482813415176518551736953)
        ·
          refine ⟨96362110061382388913802715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128482813415176518551736953 96362110061382388913802715)
          ·
            refine ⟨144543165092073583370704073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96362110061382388913802715 144543165092073583370704073)
            ·
              refine ⟨108407373819055187528028055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144543165092073583370704073 108407373819055187528028055)
              ·
                refine ⟨162611060728582781292042083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108407373819055187528028055 162611060728582781292042083)
                ·
                  refine ⟨243916591092874171938063125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162611060728582781292042083 243916591092874171938063125)
                  ·
                    refine ⟨11433590207478476809596709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243916591092874171938063125 11433590207478476809596709)
                    ·
                      refine ⟨2143798163902214401799383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11433590207478476809596709 2143798163902214401799383)
                      ·
                        rfl

theorem cell23_4175032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_4175032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175032 prefixEnd_4175032 := by exact prefixLift 4175032
  have htrace : WordTrace (prefixWord ++ tailWord_4175032) baseStart_4175032 baseEnd_4175032 := by
    simpa [prefixWord, tailWord_4175032, baseEnd_4175032] using wordTrace_append hprefix tailTrace_4175032
  have hstable : (prefixWord ++ tailWord_4175032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175032).length < 2 ^ (prefixWord ++ tailWord_4175032).sum := by decide
  have hdescent : baseEnd_4175032 < baseStart_4175032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175036 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4175036 : Nat := 118140960795 + 4175036 * 2 ^ 59
def prefixEnd_4175036 : Nat := 4983230072969 + 3 ^ 40 * 4175036 * 2
def baseEnd_4175036 : Nat := 2143800217824832386149365

theorem tailTrace_4175036 : CollatzResearch.WordTrace tailWord_4175036 prefixEnd_4175036 2143800217824832386149365 := by
  unfold tailWord_4175036
  simp only [CollatzResearch.WordTrace]
  refine ⟨76138036451282543112972481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101517381935043390817296641 76138036451282543112972481)
  ·
    refine ⟨57103527338461907334729361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76138036451282543112972481 57103527338461907334729361)
    ·
      refine ⟨42827645503846430501047021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57103527338461907334729361 42827645503846430501047021)
      ·
        refine ⟨16060367063942411437892633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42827645503846430501047021 16060367063942411437892633)
        ·
          refine ⟨12045275297956808578419475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16060367063942411437892633 12045275297956808578419475)
          ·
            refine ⟨18067912946935212867629213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045275297956808578419475 18067912946935212867629213)
            ·
              refine ⟨6775467355100704825360955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18067912946935212867629213 6775467355100704825360955)
              ·
                refine ⟨10163201032651057238041433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775467355100704825360955 10163201032651057238041433)
                ·
                  refine ⟨7622400774488292928531075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163201032651057238041433 7622400774488292928531075)
                  ·
                    refine ⟨11433601161732439392796613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622400774488292928531075 11433601161732439392796613)
                    ·
                      refine ⟨2143800217824832386149365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11433601161732439392796613 2143800217824832386149365)
                      ·
                        rfl

theorem cell23_4175036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4175036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175036 prefixEnd_4175036 := by exact prefixLift 4175036
  have htrace : WordTrace (prefixWord ++ tailWord_4175036) baseStart_4175036 baseEnd_4175036 := by
    simpa [prefixWord, tailWord_4175036, baseEnd_4175036] using wordTrace_append hprefix tailTrace_4175036
  have hstable : (prefixWord ++ tailWord_4175036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175036).length < 2 ^ (prefixWord ++ tailWord_4175036).sum := by decide
  have hdescent : baseEnd_4175036 < baseStart_4175036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175139 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_4175139 : Nat := 118140960795 + 4175139 * 2 ^ 59
def prefixEnd_4175139 : Nat := 4983230072969 + 3 ^ 40 * 4175139 * 2
def baseEnd_4175139 : Nat := 2143853106332245483161391

theorem tailTrace_4175139 : CollatzResearch.WordTrace tailWord_4175139 prefixEnd_4175139 2143853106332245483161391 := by
  unfold tailWord_4175139
  simp only [CollatzResearch.WordTrace]
  refine ⟨152279829621191934816944471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101519886414127956544629647 152279829621191934816944471)
  ·
    refine ⟨228419744431787902225416707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152279829621191934816944471 228419744431787902225416707)
    ·
      refine ⟨342629616647681853338125061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228419744431787902225416707 342629616647681853338125061)
      ·
        refine ⟨64243053121440347500898449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342629616647681853338125061 64243053121440347500898449)
        ·
          refine ⟨48182289841080260625673837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64243053121440347500898449 48182289841080260625673837)
          ·
            refine ⟨18068358690405097734627689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48182289841080260625673837 18068358690405097734627689)
            ·
              refine ⟨13551269017803823300970767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18068358690405097734627689 13551269017803823300970767)
              ·
                refine ⟨20326903526705734951456151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551269017803823300970767 20326903526705734951456151)
                ·
                  refine ⟨30490355290058602427184227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20326903526705734951456151 30490355290058602427184227)
                  ·
                    refine ⟨45735532935087903640776341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30490355290058602427184227 45735532935087903640776341)
                    ·
                      refine ⟨2143853106332245483161391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45735532935087903640776341 2143853106332245483161391)
                      ·
                        rfl

theorem cell23_4175139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_4175139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175139 prefixEnd_4175139 := by exact prefixLift 4175139
  have htrace : WordTrace (prefixWord ++ tailWord_4175139) baseStart_4175139 baseEnd_4175139 := by
    simpa [prefixWord, tailWord_4175139, baseEnd_4175139] using wordTrace_append hprefix tailTrace_4175139
  have hstable : (prefixWord ++ tailWord_4175139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175139).length < 2 ^ (prefixWord ++ tailWord_4175139).sum := by decide
  have hdescent : baseEnd_4175139 < baseStart_4175139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175160 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 1, 2, 2]
def baseStart_4175160 : Nat := 118140960795 + 4175160 * 2 ^ 59
def prefixEnd_4175160 : Nat := 4983230072969 + 3 ^ 40 * 4175160 * 2
def baseEnd_4175160 : Nat := 2143863889425989900998795

theorem tailTrace_4175160 : CollatzResearch.WordTrace tailWord_4175160 prefixEnd_4175160 2143863889425989900998795 := by
  unfold tailWord_4175160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76140297777057927701729467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101520397036077236935639289 76140297777057927701729467)
  ·
    refine ⟨114210446665586891552594201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76140297777057927701729467 114210446665586891552594201)
    ·
      refine ⟨85657834999190168664445651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114210446665586891552594201 85657834999190168664445651)
      ·
        refine ⟨128486752498785252996668477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85657834999190168664445651 128486752498785252996668477)
        ·
          refine ⟨48182532187044469873750679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128486752498785252996668477 48182532187044469873750679)
          ·
            refine ⟨72273798280566704810626019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48182532187044469873750679 72273798280566704810626019)
            ·
              refine ⟨108410697420850057215939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72273798280566704810626019 108410697420850057215939029)
              ·
                refine ⟨2540875720801173215998571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108410697420850057215939029 2540875720801173215998571)
                ·
                  refine ⟨3811313581201759823997857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540875720801173215998571 3811313581201759823997857)
                  ·
                    refine ⟨2858485185901319867998393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3811313581201759823997857 2858485185901319867998393)
                    ·
                      refine ⟨2143863889425989900998795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858485185901319867998393 2143863889425989900998795)
                      ·
                        rfl

theorem cell23_4175160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_4175160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175160 prefixEnd_4175160 := by exact prefixLift 4175160
  have htrace : WordTrace (prefixWord ++ tailWord_4175160) baseStart_4175160 baseEnd_4175160 := by
    simpa [prefixWord, tailWord_4175160, baseEnd_4175160] using wordTrace_append hprefix tailTrace_4175160
  have hstable : (prefixWord ++ tailWord_4175160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175160).length < 2 ^ (prefixWord ++ tailWord_4175160).sum := by decide
  have hdescent : baseEnd_4175160 < baseStart_4175160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175177 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 1, 2, 2]
def baseStart_4175177 : Nat := 118140960795 + 4175177 * 2 ^ 59
def prefixEnd_4175177 : Nat := 4983230072969 + 3 ^ 40 * 4175177 * 2
def baseEnd_4175177 : Nat := 2143872618597116334486217

theorem tailTrace_4175177 : CollatzResearch.WordTrace tailWord_4175177 prefixEnd_4175177 2143872618597116334486217 := by
  unfold tailWord_4175177
  simp only [CollatzResearch.WordTrace]
  refine ⟨152281215595054267306827785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101520810396702844871218523 152281215595054267306827785)
  ·
    refine ⟨114210911696290700480120839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152281215595054267306827785 114210911696290700480120839)
    ·
      refine ⟨171316367544436050720181259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114210911696290700480120839 171316367544436050720181259)
      ·
        refine ⟨256974551316654076080271889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171316367544436050720181259 256974551316654076080271889)
        ·
          refine ⟨192730913487490557060203917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256974551316654076080271889 192730913487490557060203917)
          ·
            refine ⟨72274092557808958897576469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192730913487490557060203917 72274092557808958897576469)
            ·
              refine ⟨3387848088647294948323897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72274092557808958897576469 3387848088647294948323897)
              ·
                refine ⟨2540886066485471211242923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387848088647294948323897 2540886066485471211242923)
                ·
                  refine ⟨3811329099728206816864385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540886066485471211242923 3811329099728206816864385)
                  ·
                    refine ⟨2858496824796155112648289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3811329099728206816864385 2858496824796155112648289)
                    ·
                      refine ⟨2143872618597116334486217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858496824796155112648289 2143872618597116334486217)
                      ·
                        rfl

theorem cell23_4175177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 2, 2].length) (baseStart_4175177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175177 prefixEnd_4175177 := by exact prefixLift 4175177
  have htrace : WordTrace (prefixWord ++ tailWord_4175177) baseStart_4175177 baseEnd_4175177 := by
    simpa [prefixWord, tailWord_4175177, baseEnd_4175177] using wordTrace_append hprefix tailTrace_4175177
  have hstable : (prefixWord ++ tailWord_4175177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175177).length < 2 ^ (prefixWord ++ tailWord_4175177).sum := by decide
  have hdescent : baseEnd_4175177 < baseStart_4175177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175193 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 3]
def baseStart_4175193 : Nat := 118140960795 + 4175193 * 2 ^ 59
def prefixEnd_4175193 : Nat := 4983230072969 + 3 ^ 40 * 4175193 * 2
def baseEnd_4175193 : Nat := 2143880834287588271886143

theorem tailTrace_4175193 : CollatzResearch.WordTrace tailWord_4175193 prefixEnd_4175193 2143880834287588271886143 := by
  unfold tailWord_4175193
  simp only [CollatzResearch.WordTrace]
  refine ⟨152281799162996302039410233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101521199441997534692940155 152281799162996302039410233)
  ·
    refine ⟨114211349372247226529557675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152281799162996302039410233 114211349372247226529557675)
    ·
      refine ⟨171317024058370839794336513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114211349372247226529557675 171317024058370839794336513)
      ·
        refine ⟨128487768043778129845752385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171317024058370839794336513 128487768043778129845752385)
        ·
          refine ⟨96365826032833597384314289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128487768043778129845752385 96365826032833597384314289)
          ·
            refine ⟨72274369524625198038235717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96365826032833597384314289 72274369524625198038235717)
            ·
              refine ⟨13551444285867224632169197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72274369524625198038235717 13551444285867224632169197)
              ·
                refine ⟨5081791607200209237063449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13551444285867224632169197 5081791607200209237063449)
                ·
                  refine ⟨3811343705400156927797587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081791607200209237063449 3811343705400156927797587)
                  ·
                    refine ⟨5717015558100235391696381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3811343705400156927797587 5717015558100235391696381)
                    ·
                      refine ⟨2143880834287588271886143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5717015558100235391696381 2143880834287588271886143)
                      ·
                        rfl

theorem cell23_4175193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_4175193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175193 prefixEnd_4175193 := by exact prefixLift 4175193
  have htrace : WordTrace (prefixWord ++ tailWord_4175193) baseStart_4175193 baseEnd_4175193 := by
    simpa [prefixWord, tailWord_4175193, baseEnd_4175193] using wordTrace_append hprefix tailTrace_4175193
  have hstable : (prefixWord ++ tailWord_4175193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175193).length < 2 ^ (prefixWord ++ tailWord_4175193).sum := by decide
  have hdescent : baseEnd_4175193 < baseStart_4175193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175199 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4175199 : Nat := 118140960795 + 4175199 * 2 ^ 59
def prefixEnd_4175199 : Nat := 4983230072969 + 3 ^ 40 * 4175199 * 2
def baseEnd_4175199 : Nat := 2143883915171515248411115

theorem tailTrace_4175199 : CollatzResearch.WordTrace tailWord_4175199 prefixEnd_4175199 2143883915171515248411115 := by
  unfold tailWord_4175199
  simp only [CollatzResearch.WordTrace]
  refine ⟨152282018000974565064128651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101521345333983043376085767 152282018000974565064128651)
  ·
    refine ⟨228423027001461847596192977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152282018000974565064128651 228423027001461847596192977)
    ·
      refine ⟨171317270251096385697144733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228423027001461847596192977 171317270251096385697144733)
      ·
        refine ⟨64243976344161144636429275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171317270251096385697144733 64243976344161144636429275)
        ·
          refine ⟨96365964516241716954643913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64243976344161144636429275 96365964516241716954643913)
          ·
            refine ⟨72274473387181287715982935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96365964516241716954643913 72274473387181287715982935)
            ·
              refine ⟨108411710080771931573974403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72274473387181287715982935 108411710080771931573974403)
              ·
                refine ⟨162617565121157897360961605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108411710080771931573974403 162617565121157897360961605)
                ·
                  refine ⟨30490793460217105755180301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162617565121157897360961605 30490793460217105755180301)
                  ·
                    refine ⟨11434047547581414658192613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30490793460217105755180301 11434047547581414658192613)
                    ·
                      refine ⟨2143883915171515248411115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11434047547581414658192613 2143883915171515248411115)
                      ·
                        rfl

theorem cell23_4175199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4175199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175199 prefixEnd_4175199 := by exact prefixLift 4175199
  have htrace : WordTrace (prefixWord ++ tailWord_4175199) baseStart_4175199 baseEnd_4175199 := by
    simpa [prefixWord, tailWord_4175199, baseEnd_4175199] using wordTrace_append hprefix tailTrace_4175199
  have hstable : (prefixWord ++ tailWord_4175199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175199).length < 2 ^ (prefixWord ++ tailWord_4175199).sum := by decide
  have hdescent : baseEnd_4175199 < baseStart_4175199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175203 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 3, 3, 2]
def baseStart_4175203 : Nat := 118140960795 + 4175203 * 2 ^ 59
def prefixEnd_4175203 : Nat := 4983230072969 + 3 ^ 40 * 4175203 * 2
def baseEnd_4175203 : Nat := 2143885969094133232761097

theorem tailTrace_4175203 : CollatzResearch.WordTrace tailWord_4175203 prefixEnd_4175203 2143885969094133232761097 := by
  unfold tailWord_4175203
  simp only [CollatzResearch.WordTrace]
  refine ⟨152282163892960073747274263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101521442595306715831516175 152282163892960073747274263)
  ·
    refine ⟨228423245839440110620911395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152282163892960073747274263 228423245839440110620911395)
    ·
      refine ⟨342634868759160165931367093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228423245839440110620911395 342634868759160165931367093)
      ·
        refine ⟨32122018946171265556065665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342634868759160165931367093 32122018946171265556065665)
        ·
          refine ⟨24091514209628449167049249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32122018946171265556065665 24091514209628449167049249)
          ·
            refine ⟨18068635657221336875286937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24091514209628449167049249 18068635657221336875286937)
            ·
              refine ⟨13551476742916002656465203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18068635657221336875286937 13551476742916002656465203)
              ·
                refine ⟨20327215114374003984697805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551476742916002656465203 20327215114374003984697805)
                ·
                  refine ⟨7622705667890251494261677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20327215114374003984697805 7622705667890251494261677)
                  ·
                    refine ⟨2858514625458844310348129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7622705667890251494261677 2858514625458844310348129)
                    ·
                      refine ⟨2143885969094133232761097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858514625458844310348129 2143885969094133232761097)
                      ·
                        rfl

theorem cell23_4175203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_4175203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175203 prefixEnd_4175203 := by exact prefixLift 4175203
  have htrace : WordTrace (prefixWord ++ tailWord_4175203) baseStart_4175203 baseEnd_4175203 := by
    simpa [prefixWord, tailWord_4175203, baseEnd_4175203] using wordTrace_append hprefix tailTrace_4175203
  have hstable : (prefixWord ++ tailWord_4175203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175203).length < 2 ^ (prefixWord ++ tailWord_4175203).sum := by decide
  have hdescent : baseEnd_4175203 < baseStart_4175203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175214 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4175214 : Nat := 118140960795 + 4175214 * 2 ^ 59
def prefixEnd_4175214 : Nat := 4983230072969 + 3 ^ 40 * 4175214 * 2
def baseEnd_4175214 : Nat := 2143891617381332689723547

theorem tailTrace_4175214 : CollatzResearch.WordTrace tailWord_4175214 prefixEnd_4175214 2143891617381332689723547 := by
  unfold tailWord_4175214
  simp only [CollatzResearch.WordTrace]
  refine ⟨19035320636990027828240587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101521710063946815083949797 19035320636990027828240587)
  ·
    refine ⟨28552980955485041742360881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19035320636990027828240587 28552980955485041742360881)
    ·
      refine ⟨21414735716613781306770661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28552980955485041742360881 21414735716613781306770661)
      ·
        refine ⟨4015262946865083995019499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21414735716613781306770661 4015262946865083995019499)
        ·
          refine ⟨6022894420297625992529249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015262946865083995019499 6022894420297625992529249)
          ·
            refine ⟨4517170815223219494396937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6022894420297625992529249 4517170815223219494396937)
            ·
              refine ⟨3387878111417414620797703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517170815223219494396937 3387878111417414620797703)
              ·
                refine ⟨5081817167126121931196555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387878111417414620797703 5081817167126121931196555)
                ·
                  refine ⟨7622725750689182896794833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081817167126121931196555 7622725750689182896794833)
                  ·
                    refine ⟨5717044313016887172596125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622725750689182896794833 5717044313016887172596125)
                    ·
                      refine ⟨2143891617381332689723547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5717044313016887172596125 2143891617381332689723547)
                      ·
                        rfl

theorem cell23_4175214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4175214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175214 prefixEnd_4175214 := by exact prefixLift 4175214
  have htrace : WordTrace (prefixWord ++ tailWord_4175214) baseStart_4175214 baseEnd_4175214 := by
    simpa [prefixWord, tailWord_4175214, baseEnd_4175214] using wordTrace_append hprefix tailTrace_4175214
  have hstable : (prefixWord ++ tailWord_4175214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175214).length < 2 ^ (prefixWord ++ tailWord_4175214).sum := by decide
  have hdescent : baseEnd_4175214 < baseStart_4175214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175279 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_4175279 : Nat := 118140960795 + 4175279 * 2 ^ 59
def prefixEnd_4175279 : Nat := 4983230072969 + 3 ^ 40 * 4175279 * 2
def baseEnd_4175279 : Nat := 2143924993623874935410747

theorem tailTrace_4175279 : CollatzResearch.WordTrace tailWord_4175279 prefixEnd_4175279 2143924993623874935410747 := by
  unfold tailWord_4175279
  simp only [CollatzResearch.WordTrace]
  refine ⟨152284935840684738727040891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101523290560456492484693927 152284935840684738727040891)
  ·
    refine ⟨228427403761027108090561337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152284935840684738727040891 228427403761027108090561337)
    ·
      refine ⟨171320552820770331067921003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228427403761027108090561337 171320552820770331067921003)
      ·
        refine ⟨256980829231155496601881505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171320552820770331067921003 256980829231155496601881505)
        ·
          refine ⟨192735621923366622451411129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256980829231155496601881505 192735621923366622451411129)
          ·
            refine ⟨144551716442524966838558347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192735621923366622451411129 144551716442524966838558347)
            ·
              refine ⟨216827574663787450257837521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144551716442524966838558347 216827574663787450257837521)
              ·
                refine ⟨162620680997840587693378141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216827574663787450257837521 162620680997840587693378141)
                ·
                  refine ⟨60982755374190220385016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162620680997840587693378141 60982755374190220385016803)
                  ·
                    refine ⟨91474133061285330577525205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60982755374190220385016803 91474133061285330577525205)
                    ·
                      refine ⟨2143924993623874935410747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91474133061285330577525205 2143924993623874935410747)
                      ·
                        rfl

theorem cell23_4175279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_4175279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175279 prefixEnd_4175279 := by exact prefixLift 4175279
  have htrace : WordTrace (prefixWord ++ tailWord_4175279) baseStart_4175279 baseEnd_4175279 := by
    simpa [prefixWord, tailWord_4175279, baseEnd_4175279] using wordTrace_append hprefix tailTrace_4175279
  have hstable : (prefixWord ++ tailWord_4175279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175279).length < 2 ^ (prefixWord ++ tailWord_4175279).sum := by decide
  have hdescent : baseEnd_4175279 < baseStart_4175279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175293 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_4175293 : Nat := 118140960795 + 4175293 * 2 ^ 59
def prefixEnd_4175293 : Nat := 4983230072969 + 3 ^ 40 * 4175293 * 2
def baseEnd_4175293 : Nat := 2143932182353037880635683

theorem tailTrace_4175293 : CollatzResearch.WordTrace tailWord_4175293 prefixEnd_4175293 2143932182353037880635683 := by
  unfold tailWord_4175293
  simp only [CollatzResearch.WordTrace]
  refine ⟨152285446462634019118050533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101523630975089346078700355 152285446462634019118050533)
  ·
    refine ⟨28553521211743878584634475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152285446462634019118050533 28553521211743878584634475)
    ·
      refine ⟨42830281817615817876951713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28553521211743878584634475 42830281817615817876951713)
      ·
        refine ⟨32122711363211863407713785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42830281817615817876951713 32122711363211863407713785)
        ·
          refine ⟨24092033522408897555785339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32122711363211863407713785 24092033522408897555785339)
          ·
            refine ⟨36138050283613346333678009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24092033522408897555785339 36138050283613346333678009)
            ·
              refine ⟨27103537712710009750258507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36138050283613346333678009 27103537712710009750258507)
              ·
                refine ⟨40655306569065014625387761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27103537712710009750258507 40655306569065014625387761)
                ·
                  refine ⟨30491479926798760969040821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40655306569065014625387761 30491479926798760969040821)
                  ·
                    refine ⟨2858576243137383840847577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30491479926798760969040821 2858576243137383840847577)
                    ·
                      refine ⟨2143932182353037880635683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858576243137383840847577 2143932182353037880635683)
                      ·
                        rfl

theorem cell23_4175293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_4175293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175293 prefixEnd_4175293 := by exact prefixLift 4175293
  have htrace : WordTrace (prefixWord ++ tailWord_4175293) baseStart_4175293 baseEnd_4175293 := by
    simpa [prefixWord, tailWord_4175293, baseEnd_4175293] using wordTrace_append hprefix tailTrace_4175293
  have hstable : (prefixWord ++ tailWord_4175293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175293).length < 2 ^ (prefixWord ++ tailWord_4175293).sum := by decide
  have hdescent : baseEnd_4175293 < baseStart_4175293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175336 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4175336 : Nat := 118140960795 + 4175336 * 2 ^ 59
def prefixEnd_4175336 : Nat := 4983230072969 + 3 ^ 40 * 4175336 * 2
def baseEnd_4175336 : Nat := 2143954262021181212397985

theorem tailTrace_4175336 : CollatzResearch.WordTrace tailWord_4175336 prefixEnd_4175336 2143954262021181212397985 := by
  unfold tailWord_4175336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76143507400739118730932931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101524676534318824974577241 76143507400739118730932931)
  ·
    refine ⟨114215261101108678096399397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76143507400739118730932931 114215261101108678096399397)
    ·
      refine ⟨21415361456457877143074887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114215261101108678096399397 21415361456457877143074887)
      ·
        refine ⟨32123042184686815714612331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21415361456457877143074887 32123042184686815714612331)
        ·
          refine ⟨48184563277030223571918497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32123042184686815714612331 48184563277030223571918497)
          ·
            refine ⟨36138422457772667678938873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48184563277030223571918497 36138422457772667678938873)
            ·
              refine ⟨27103816843329500759204155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36138422457772667678938873 27103816843329500759204155)
              ·
                refine ⟨40655725264994251138806233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27103816843329500759204155 40655725264994251138806233)
                ·
                  refine ⟨30491793948745688354104675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40655725264994251138806233 30491793948745688354104675)
                  ·
                    refine ⟨45737690923118532531157013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30491793948745688354104675 45737690923118532531157013)
                    ·
                      refine ⟨2143954262021181212397985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45737690923118532531157013 2143954262021181212397985)
                      ·
                        rfl

theorem cell23_4175336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4175336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175336 prefixEnd_4175336 := by exact prefixLift 4175336
  have htrace : WordTrace (prefixWord ++ tailWord_4175336) baseStart_4175336 baseEnd_4175336 := by
    simpa [prefixWord, tailWord_4175336, baseEnd_4175336] using wordTrace_append hprefix tailTrace_4175336
  have hstable : (prefixWord ++ tailWord_4175336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175336).length < 2 ^ (prefixWord ++ tailWord_4175336).sum := by decide
  have hdescent : baseEnd_4175336 < baseStart_4175336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175343 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_4175343 : Nat := 118140960795 + 4175343 * 2 ^ 59
def prefixEnd_4175343 : Nat := 4983230072969 + 3 ^ 40 * 4175343 * 2
def baseEnd_4175343 : Nat := 2143957856385762685010453

theorem tailTrace_4175343 : CollatzResearch.WordTrace tailWord_4175343 prefixEnd_4175343 2143957856385762685010453 := by
  unfold tailWord_4175343
  simp only [CollatzResearch.WordTrace]
  refine ⟨152287270112452877657370683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101524846741635251771580455 152287270112452877657370683)
  ·
    refine ⟨228430905168679316486056025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152287270112452877657370683 228430905168679316486056025)
    ·
      refine ⟨171323178876509487364542019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228430905168679316486056025 171323178876509487364542019)
      ·
        refine ⟨256984768314764231046813029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171323178876509487364542019 256984768314764231046813029)
        ·
          refine ⟨48184644059018293321277443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256984768314764231046813029 48184644059018293321277443)
          ·
            refine ⟨72276966088527439981916165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48184644059018293321277443 72276966088527439981916165)
            ·
              refine ⟨13551931141598894996609281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72276966088527439981916165 13551931141598894996609281)
              ·
                refine ⟨10163948356199171247456961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13551931141598894996609281 10163948356199171247456961)
                ·
                  refine ⟨7622961267149378435592721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163948356199171247456961 7622961267149378435592721)
                  ·
                    refine ⟨5717220950362033826694541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622961267149378435592721 5717220950362033826694541)
                    ·
                      refine ⟨2143957856385762685010453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5717220950362033826694541 2143957856385762685010453)
                      ·
                        rfl

theorem cell23_4175343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_4175343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175343 prefixEnd_4175343 := by exact prefixLift 4175343
  have htrace : WordTrace (prefixWord ++ tailWord_4175343) baseStart_4175343 baseEnd_4175343 := by
    simpa [prefixWord, tailWord_4175343, baseEnd_4175343] using wordTrace_append hprefix tailTrace_4175343
  have hstable : (prefixWord ++ tailWord_4175343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175343).length < 2 ^ (prefixWord ++ tailWord_4175343).sum := by decide
  have hdescent : baseEnd_4175343 < baseStart_4175343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175386 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4175386 : Nat := 118140960795 + 4175386 * 2 ^ 59
def prefixEnd_4175386 : Nat := 4983230072969 + 3 ^ 40 * 4175386 * 2
def baseEnd_4175386 : Nat := 2143979936053906016772755

theorem tailTrace_4175386 : CollatzResearch.WordTrace tailWord_4175386 prefixEnd_4175386 2143979936053906016772755 := by
  unfold tailWord_4175386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38072209612824274000296503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101525892300864730667457341 38072209612824274000296503)
  ·
    refine ⟨57108314419236411000444755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38072209612824274000296503 57108314419236411000444755)
    ·
      refine ⟨85662471628854616500667133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57108314419236411000444755 85662471628854616500667133)
      ·
        refine ⟨32123426860820481187750175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85662471628854616500667133 32123426860820481187750175)
        ·
          refine ⟨48185140291230721781625263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32123426860820481187750175 48185140291230721781625263)
          ·
            refine ⟨72277710436846082672437895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48185140291230721781625263 72277710436846082672437895)
            ·
              refine ⟨108416565655269124008656843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72277710436846082672437895 108416565655269124008656843)
              ·
                refine ⟨162624848482903686012985265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108416565655269124008656843 162624848482903686012985265)
                ·
                  refine ⟨121968636362177764509738949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162624848482903686012985265 121968636362177764509738949)
                  ·
                    refine ⟨22869119317908330845576053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121968636362177764509738949 22869119317908330845576053)
                    ·
                      refine ⟨2143979936053906016772755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22869119317908330845576053 2143979936053906016772755)
                      ·
                        rfl

theorem cell23_4175386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4175386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175386 prefixEnd_4175386 := by exact prefixLift 4175386
  have htrace : WordTrace (prefixWord ++ tailWord_4175386) baseStart_4175386 baseEnd_4175386 := by
    simpa [prefixWord, tailWord_4175386, baseEnd_4175386] using wordTrace_append hprefix tailTrace_4175386
  have hstable : (prefixWord ++ tailWord_4175386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175386).length < 2 ^ (prefixWord ++ tailWord_4175386).sum := by decide
  have hdescent : baseEnd_4175386 < baseStart_4175386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175423 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 1, 6]
def baseStart_4175423 : Nat := 118140960795 + 4175423 * 2 ^ 59
def prefixEnd_4175423 : Nat := 4983230072969 + 3 ^ 40 * 4175423 * 2
def baseEnd_4175423 : Nat := 714666311612707457336695

theorem tailTrace_4175423 : CollatzResearch.WordTrace tailWord_4175423 prefixEnd_4175423 714666311612707457336695 := by
  unfold tailWord_4175423
  simp only [CollatzResearch.WordTrace]
  refine ⟨152290187952163051320282923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101526791968108700880188615 152290187952163051320282923)
  ·
    refine ⟨228435281928244576980424385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152290187952163051320282923 228435281928244576980424385)
    ·
      refine ⟨171326461446183432735318289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228435281928244576980424385 171326461446183432735318289)
      ·
        refine ⟨128494846084637574551488717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171326461446183432735318289 128494846084637574551488717)
        ·
          refine ⟨48185567281739090456808269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128494846084637574551488717 48185567281739090456808269)
          ·
            refine ⟨18069587730652158921303101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48185567281739090456808269 18069587730652158921303101)
            ·
              refine ⟨6776095398994559595488663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18069587730652158921303101 6776095398994559595488663)
              ·
                refine ⟨10164143098491839393232995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776095398994559595488663 10164143098491839393232995)
                ·
                  refine ⟨15246214647737759089849493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164143098491839393232995 15246214647737759089849493)
                  ·
                    refine ⟨714666311612707457336695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15246214647737759089849493 714666311612707457336695)
                    ·
                      rfl

theorem cell23_4175423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_4175423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175423 prefixEnd_4175423 := by exact prefixLift 4175423
  have htrace : WordTrace (prefixWord ++ tailWord_4175423) baseStart_4175423 baseEnd_4175423 := by
    simpa [prefixWord, tailWord_4175423, baseEnd_4175423] using wordTrace_append hprefix tailTrace_4175423
  have hstable : (prefixWord ++ tailWord_4175423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175423).length < 2 ^ (prefixWord ++ tailWord_4175423).sum := by decide
  have hdescent : baseEnd_4175423 < baseStart_4175423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175433 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_4175433 : Nat := 118140960795 + 4175433 * 2 ^ 59
def prefixEnd_4175433 : Nat := 4983230072969 + 3 ^ 40 * 4175433 * 2
def baseEnd_4175433 : Nat := 2144004069644667332885039

theorem tailTrace_4175433 : CollatzResearch.WordTrace tailWord_4175433 prefixEnd_4175433 2144004069644667332885039 := by
  unfold tailWord_4175433
  simp only [CollatzResearch.WordTrace]
  refine ⟨152290552682126823028146953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101527035121417882018764635 152290552682126823028146953)
  ·
    refine ⟨114217914511595117271110215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152290552682126823028146953 114217914511595117271110215)
    ·
      refine ⟨171326871767392675906665323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114217914511595117271110215 171326871767392675906665323)
      ·
        refine ⟨256990307651089013859997985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171326871767392675906665323 256990307651089013859997985)
        ·
          refine ⟨192742730738316760394998489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256990307651089013859997985 192742730738316760394998489)
          ·
            refine ⟨144557048053737570296248867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192742730738316760394998489 144557048053737570296248867)
            ·
              refine ⟨216835572080606355444373301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144557048053737570296248867 216835572080606355444373301)
              ·
                refine ⟨20328334882556845822909997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216835572080606355444373301 20328334882556845822909997)
                ·
                  refine ⟨7623125580958817183591249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20328334882556845822909997 7623125580958817183591249)
                  ·
                    refine ⟨5717344185719112887693437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7623125580958817183591249 5717344185719112887693437)
                    ·
                      refine ⟨2144004069644667332885039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5717344185719112887693437 2144004069644667332885039)
                      ·
                        rfl

theorem cell23_4175433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_4175433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175433 prefixEnd_4175433 := by exact prefixLift 4175433
  have htrace : WordTrace (prefixWord ++ tailWord_4175433) baseStart_4175433 baseEnd_4175433 := by
    simpa [prefixWord, tailWord_4175433, baseEnd_4175433] using wordTrace_append hprefix tailTrace_4175433
  have hstable : (prefixWord ++ tailWord_4175433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175433).length < 2 ^ (prefixWord ++ tailWord_4175433).sum := by decide
  have hdescent : baseEnd_4175433 < baseStart_4175433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175464 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4175464 : Nat := 118140960795 + 4175464 * 2 ^ 59
def prefixEnd_4175464 : Nat := 4983230072969 + 3 ^ 40 * 4175464 * 2
def baseEnd_4175464 : Nat := 2144019987544956711597397

theorem tailTrace_4175464 : CollatzResearch.WordTrace tailWord_4175464 prefixEnd_4175464 2144019987544956711597397 := by
  unfold tailWord_4175464
  simp only [CollatzResearch.WordTrace]
  refine ⟨76145841672507257661262723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101527788896676343548350297 76145841672507257661262723)
  ·
    refine ⟨114218762508760886491894085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76145841672507257661262723 114218762508760886491894085)
    ·
      refine ⟨21416017970392666217230141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114218762508760886491894085 21416017970392666217230141)
      ·
        refine ⟨8031006738897249831461303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21416017970392666217230141 8031006738897249831461303)
        ·
          refine ⟨12046510108345874747191955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031006738897249831461303 12046510108345874747191955)
          ·
            refine ⟨18069765162518812120787933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12046510108345874747191955 18069765162518812120787933)
            ·
              refine ⟨6776161935944554545295475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18069765162518812120787933 6776161935944554545295475)
              ·
                refine ⟨10164242903916831817943213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776161935944554545295475 10164242903916831817943213)
                ·
                  refine ⟨3811591088968811931728705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10164242903916831817943213 3811591088968811931728705)
                  ·
                    refine ⟨2858693316726608948796529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3811591088968811931728705 2858693316726608948796529)
                    ·
                      refine ⟨2144019987544956711597397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858693316726608948796529 2144019987544956711597397)
                      ·
                        rfl

theorem cell23_4175464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4175464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175464 prefixEnd_4175464 := by exact prefixLift 4175464
  have htrace : WordTrace (prefixWord ++ tailWord_4175464) baseStart_4175464 baseEnd_4175464 := by
    simpa [prefixWord, tailWord_4175464, baseEnd_4175464] using wordTrace_append hprefix tailTrace_4175464
  have hstable : (prefixWord ++ tailWord_4175464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175464).length < 2 ^ (prefixWord ++ tailWord_4175464).sum := by decide
  have hdescent : baseEnd_4175464 < baseStart_4175464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175470 : List Nat := [4, 1, 2, 2, 3, 1, 2, 8]
def baseStart_4175470 : Nat := 118140960795 + 4175470 * 2 ^ 59
def prefixEnd_4175470 : Nat := 4983230072969 + 3 ^ 40 * 4175470 * 2
def baseEnd_4175470 : Nat := 79408261793662358819347

theorem tailTrace_4175470 : CollatzResearch.WordTrace tailWord_4175470 prefixEnd_4175470 79408261793662358819347 := by
  unfold tailWord_4175470
  simp only [CollatzResearch.WordTrace]
  refine ⟨19036487772874097293405483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101527934788661852231495909 19036487772874097293405483)
  ·
    refine ⟨28554731659311145940108225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19036487772874097293405483 28554731659311145940108225)
    ·
      refine ⟨21416048744483359455081169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28554731659311145940108225 21416048744483359455081169)
      ·
        refine ⟨16062036558362519591310877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21416048744483359455081169 16062036558362519591310877)
        ·
          refine ⟨6023263709385944846741579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16062036558362519591310877 6023263709385944846741579)
          ·
            refine ⟨9034895564078917270112369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023263709385944846741579 9034895564078917270112369)
            ·
              refine ⟨6776171673059187952584277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9034895564078917270112369 6776171673059187952584277)
              ·
                refine ⟨79408261793662358819347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6776171673059187952584277 79408261793662358819347)
                ·
                  rfl

theorem cell23_4175470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_4175470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175470 prefixEnd_4175470 := by exact prefixLift 4175470
  have htrace : WordTrace (prefixWord ++ tailWord_4175470) baseStart_4175470 baseEnd_4175470 := by
    simpa [prefixWord, tailWord_4175470, baseEnd_4175470] using wordTrace_append hprefix tailTrace_4175470
  have hstable : (prefixWord ++ tailWord_4175470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175470).length < 2 ^ (prefixWord ++ tailWord_4175470).sum := by decide
  have hdescent : baseEnd_4175470 < baseStart_4175470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175474 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_4175474 : Nat := 118140960795 + 4175474 * 2 ^ 59
def prefixEnd_4175474 : Nat := 4983230072969 + 3 ^ 40 * 4175474 * 2
def baseEnd_4175474 : Nat := 714675040783833890824117

theorem tailTrace_4175474 : CollatzResearch.WordTrace tailWord_4175474 prefixEnd_4175474 714675040783833890824117 := by
  unfold tailWord_4175474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38073012018744571757597369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101528032049985524686926317 38073012018744571757597369)
  ·
    refine ⟨28554759014058428818198027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38073012018744571757597369 28554759014058428818198027)
    ·
      refine ⟨42832138521087643227297041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28554759014058428818198027 42832138521087643227297041)
      ·
        refine ⟨32124103890815732420472781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42832138521087643227297041 32124103890815732420472781)
        ·
          refine ⟨12046538959055899657677293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32124103890815732420472781 12046538959055899657677293)
          ·
            refine ⟨4517452109645962371628985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12046538959055899657677293 4517452109645962371628985)
            ·
              refine ⟨3388089082234471778721739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517452109645962371628985 3388089082234471778721739)
              ·
                refine ⟨5082133623351707668082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388089082234471778721739 5082133623351707668082609)
                ·
                  refine ⟨3811600217513780751061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082133623351707668082609 3811600217513780751061957)
                  ·
                    refine ⟨714675040783833890824117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811600217513780751061957 714675040783833890824117)
                    ·
                      rfl

theorem cell23_4175474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_4175474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175474 prefixEnd_4175474 := by exact prefixLift 4175474
  have htrace : WordTrace (prefixWord ++ tailWord_4175474) baseStart_4175474 baseEnd_4175474 := by
    simpa [prefixWord, tailWord_4175474, baseEnd_4175474] using wordTrace_append hprefix tailTrace_4175474
  have hstable : (prefixWord ++ tailWord_4175474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175474).length < 2 ^ (prefixWord ++ tailWord_4175474).sum := by decide
  have hdescent : baseEnd_4175474 < baseStart_4175474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175523 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3]
def baseStart_4175523 : Nat := 118140960795 + 4175523 * 2 ^ 59
def prefixEnd_4175523 : Nat := 4983230072969 + 3 ^ 40 * 4175523 * 2
def baseEnd_4175523 : Nat := 2144050282903571980759625

theorem tailTrace_4175523 : CollatzResearch.WordTrace tailWord_4175523 prefixEnd_4175523 2144050282903571980759625 := by
  unfold tailWord_4175523
  simp only [CollatzResearch.WordTrace]
  refine ⟨152293835251800768398923223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101529223501200512265948815 152293835251800768398923223)
  ·
    refine ⟨228440752877701152598384835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152293835251800768398923223 228440752877701152598384835)
    ·
      refine ⟨342661129316551728897577253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228440752877701152598384835 342661129316551728897577253)
      ·
        refine ⟨64248961746853449168295735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342661129316551728897577253 64248961746853449168295735)
        ·
          refine ⟨96373442620280173752443603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64248961746853449168295735 96373442620280173752443603)
          ·
            refine ⟨144560163930420260628665405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96373442620280173752443603 144560163930420260628665405)
            ·
              refine ⟨54210061473907597735749527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144560163930420260628665405 54210061473907597735749527)
              ·
                refine ⟨81315092210861396603624291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54210061473907597735749527 81315092210861396603624291)
                ·
                  refine ⟨121972638316292094905436437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81315092210861396603624291 121972638316292094905436437)
                  ·
                    refine ⟨5717467421076191948692333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121972638316292094905436437 5717467421076191948692333)
                    ·
                      refine ⟨2144050282903571980759625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5717467421076191948692333 2144050282903571980759625)
                      ·
                        rfl

theorem cell23_4175523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_4175523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175523 prefixEnd_4175523 := by exact prefixLift 4175523
  have htrace : WordTrace (prefixWord ++ tailWord_4175523) baseStart_4175523 baseEnd_4175523 := by
    simpa [prefixWord, tailWord_4175523, baseEnd_4175523] using wordTrace_append hprefix tailTrace_4175523
  have hstable : (prefixWord ++ tailWord_4175523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175523).length < 2 ^ (prefixWord ++ tailWord_4175523).sum := by decide
  have hdescent : baseEnd_4175523 < baseStart_4175523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175543 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 9]
def baseStart_4175543 : Nat := 118140960795 + 4175543 * 2 ^ 59
def prefixEnd_4175543 : Nat := 4983230072969 + 3 ^ 40 * 4175543 * 2
def baseEnd_4175543 : Nat := 238228950279629100278837

theorem tailTrace_4175543 : CollatzResearch.WordTrace tailWord_4175543 prefixEnd_4175543 238228950279629100278837 := by
  unfold tailWord_4175543
  simp only [CollatzResearch.WordTrace]
  refine ⟨152294564711728311814651283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101529709807818874543100855 152294564711728311814651283)
  ·
    refine ⟨228441847067592467721976925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152294564711728311814651283 228441847067592467721976925)
    ·
      refine ⟨85665692650347175395741347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228441847067592467721976925 85665692650347175395741347)
      ·
        refine ⟨128498538975520763093612021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85665692650347175395741347 128498538975520763093612021)
        ·
          refine ⟨12046738028955071540026127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128498538975520763093612021 12046738028955071540026127)
          ·
            refine ⟨18070107043432607310039191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12046738028955071540026127 18070107043432607310039191)
            ·
              refine ⟨27105160565148910965058787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18070107043432607310039191 27105160565148910965058787)
              ·
                refine ⟨40657740847723366447588181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27105160565148910965058787 40657740847723366447588181)
                ·
                  refine ⟨238228950279629100278837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40657740847723366447588181 238228950279629100278837)
                  ·
                    rfl

theorem cell23_4175543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 9].length) (baseStart_4175543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175543 prefixEnd_4175543 := by exact prefixLift 4175543
  have htrace : WordTrace (prefixWord ++ tailWord_4175543) baseStart_4175543 baseEnd_4175543 := by
    simpa [prefixWord, tailWord_4175543, baseEnd_4175543] using wordTrace_append hprefix tailTrace_4175543
  have hstable : (prefixWord ++ tailWord_4175543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175543).length < 2 ^ (prefixWord ++ tailWord_4175543).sum := by decide
  have hdescent : baseEnd_4175543 < baseStart_4175543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175558 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4175558 : Nat := 118140960795 + 4175558 * 2 ^ 59
def prefixEnd_4175558 : Nat := 4983230072969 + 3 ^ 40 * 4175558 * 2
def baseEnd_4175558 : Nat := 2144068254726479343821965

theorem tailTrace_4175558 : CollatzResearch.WordTrace tailWord_4175558 prefixEnd_4175558 2144068254726479343821965 := by
  unfold tailWord_4175558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759222243958561543013979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101530074537782646250964885 4759222243958561543013979)
  ·
    refine ⟨7138833365937842314520969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4759222243958561543013979 7138833365937842314520969)
    ·
      refine ⟨5354125024453381735890727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7138833365937842314520969 5354125024453381735890727)
      ·
        refine ⟨8031187536680072603836091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354125024453381735890727 8031187536680072603836091)
        ·
          refine ⟨12046781305020108905754137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031187536680072603836091 12046781305020108905754137)
          ·
            refine ⟨9035085978765081679315603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12046781305020108905754137 9035085978765081679315603)
            ·
              refine ⟨13552628968147622518973405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035085978765081679315603 13552628968147622518973405)
              ·
                refine ⟨5082235863055358444615027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13552628968147622518973405 5082235863055358444615027)
                ·
                  refine ⟨7623353794583037666922541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082235863055358444615027 7623353794583037666922541)
                  ·
                    refine ⟨2858757672968639125095953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7623353794583037666922541 2858757672968639125095953)
                    ·
                      refine ⟨2144068254726479343821965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858757672968639125095953 2144068254726479343821965)
                      ·
                        rfl

theorem cell23_4175558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4175558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175558 prefixEnd_4175558 := by exact prefixLift 4175558
  have htrace : WordTrace (prefixWord ++ tailWord_4175558) baseStart_4175558 baseEnd_4175558 := by
    simpa [prefixWord, tailWord_4175558, baseEnd_4175558] using wordTrace_append hprefix tailTrace_4175558
  have hstable : (prefixWord ++ tailWord_4175558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175558).length < 2 ^ (prefixWord ++ tailWord_4175558).sum := by decide
  have hdescent : baseEnd_4175558 < baseStart_4175558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175583 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4175583 : Nat := 118140960795 + 4175583 * 2 ^ 59
def prefixEnd_4175583 : Nat := 4983230072969 + 3 ^ 40 * 4175583 * 2
def baseEnd_4175583 : Nat := 2144081091742841746009349

theorem tailTrace_4175583 : CollatzResearch.WordTrace tailWord_4175583 prefixEnd_4175583 2144081091742841746009349 := by
  unfold tailWord_4175583
  simp only [CollatzResearch.WordTrace]
  refine ⟨152296023631583398646107403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101530682421055599097404935 152296023631583398646107403)
  ·
    refine ⟨228444035447375097969161105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152296023631583398646107403 228444035447375097969161105)
    ·
      refine ⟨171333026585531323476870829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228444035447375097969161105 171333026585531323476870829)
      ·
        refine ⟨64249884969574246303826561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171333026585531323476870829 64249884969574246303826561)
        ·
          refine ⟨48187413727180684727869921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64249884969574246303826561 48187413727180684727869921)
          ·
            refine ⟨36140560295385513545902441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48187413727180684727869921 36140560295385513545902441)
            ·
              refine ⟨27105420221539135159426831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36140560295385513545902441 27105420221539135159426831)
              ·
                refine ⟨40658130332308702739140247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27105420221539135159426831 40658130332308702739140247)
                ·
                  refine ⟨60987195498463054108710371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40658130332308702739140247 60987195498463054108710371)
                  ·
                    refine ⟨91480793247694581163065557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60987195498463054108710371 91480793247694581163065557)
                    ·
                      refine ⟨2144081091742841746009349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91480793247694581163065557 2144081091742841746009349)
                      ·
                        rfl

theorem cell23_4175583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4175583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175583 prefixEnd_4175583 := by exact prefixLift 4175583
  have htrace : WordTrace (prefixWord ++ tailWord_4175583) baseStart_4175583 baseEnd_4175583 := by
    simpa [prefixWord, tailWord_4175583, baseEnd_4175583] using wordTrace_append hprefix tailTrace_4175583
  have hstable : (prefixWord ++ tailWord_4175583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175583).length < 2 ^ (prefixWord ++ tailWord_4175583).sum := by decide
  have hdescent : baseEnd_4175583 < baseStart_4175583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175610 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_4175610 : Nat := 118140960795 + 4175610 * 2 ^ 59
def prefixEnd_4175610 : Nat := 4983230072969 + 3 ^ 40 * 4175610 * 2
def baseEnd_4175610 : Nat := 2144094955720513140371725

theorem tailTrace_4175610 : CollatzResearch.WordTrace tailWord_4175610 prefixEnd_4175610 2144094955720513140371725 := by
  unfold tailWord_4175610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38074252100621395564335071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101531338934990388171560189 38074252100621395564335071)
  ·
    refine ⟨57111378150932093346502607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38074252100621395564335071 57111378150932093346502607)
    ·
      refine ⟨85667067226398140019753911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57111378150932093346502607 85667067226398140019753911)
      ·
        refine ⟨128500600839597210029630867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85667067226398140019753911 128500600839597210029630867)
        ·
          refine ⟨192750901259395815044446301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128500600839597210029630867 192750901259395815044446301)
          ·
            refine ⟨72281587972273430641667363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192750901259395815044446301 72281587972273430641667363)
            ·
              refine ⟨108422381958410145962501045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72281587972273430641667363 108422381958410145962501045)
              ·
                refine ⟨10164598308600951183984473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108422381958410145962501045 10164598308600951183984473)
                ·
                  refine ⟨7623448731450713387988355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10164598308600951183984473 7623448731450713387988355)
                  ·
                    refine ⟨11435173097176070081982533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7623448731450713387988355 11435173097176070081982533)
                    ·
                      refine ⟨2144094955720513140371725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11435173097176070081982533 2144094955720513140371725)
                      ·
                        rfl

theorem cell23_4175610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_4175610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175610 prefixEnd_4175610 := by exact prefixLift 4175610
  have htrace : WordTrace (prefixWord ++ tailWord_4175610) baseStart_4175610 baseEnd_4175610 := by
    simpa [prefixWord, tailWord_4175610, baseEnd_4175610] using wordTrace_append hprefix tailTrace_4175610
  have hstable : (prefixWord ++ tailWord_4175610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175610).length < 2 ^ (prefixWord ++ tailWord_4175610).sum := by decide
  have hdescent : baseEnd_4175610 < baseStart_4175610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175637 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_4175637 : Nat := 118140960795 + 4175637 * 2 ^ 59
def prefixEnd_4175637 : Nat := 4983230072969 + 3 ^ 40 * 4175637 * 2
def baseEnd_4175637 : Nat := 714702939899394844911367

theorem tailTrace_4175637 : CollatzResearch.WordTrace tailWord_4175637 prefixEnd_4175637 714702939899394844911367 := by
  unfold tailWord_4175637
  simp only [CollatzResearch.WordTrace]
  refine ⟨152297993173387765868573165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101531995448925177245715443 152297993173387765868573165)
  ·
    refine ⟨57111747440020412200714937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152297993173387765868573165 57111747440020412200714937)
    ·
      refine ⟨42833810580015309150536203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57111747440020412200714937 42833810580015309150536203)
      ·
        refine ⟨64250715870022963725804305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42833810580015309150536203 64250715870022963725804305)
        ·
          refine ⟨48188036902517222794353229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64250715870022963725804305 48188036902517222794353229)
          ·
            refine ⟨18070513838443958547882461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48188036902517222794353229 18070513838443958547882461)
            ·
              refine ⟨6776442689416484455455923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18070513838443958547882461 6776442689416484455455923)
              ·
                refine ⟨10164664034124726683183885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776442689416484455455923 10164664034124726683183885)
                ·
                  refine ⟨3811749012796772506193957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10164664034124726683183885 3811749012796772506193957)
                  ·
                    refine ⟨714702939899394844911367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3811749012796772506193957 714702939899394844911367)
                    ·
                      rfl

theorem cell23_4175637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_4175637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175637 prefixEnd_4175637 := by exact prefixLift 4175637
  have htrace : WordTrace (prefixWord ++ tailWord_4175637) baseStart_4175637 baseEnd_4175637 := by
    simpa [prefixWord, tailWord_4175637, baseEnd_4175637] using wordTrace_append hprefix tailTrace_4175637
  have hstable : (prefixWord ++ tailWord_4175637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175637).length < 2 ^ (prefixWord ++ tailWord_4175637).sum := by decide
  have hdescent : baseEnd_4175637 < baseStart_4175637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175663 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 9]
def baseStart_4175663 : Nat := 118140960795 + 4175663 * 2 ^ 59
def prefixEnd_4175663 : Nat := 4983230072969 + 3 ^ 40 * 4175663 * 2
def baseEnd_4175663 : Nat := 714707390065067144336327

theorem tailTrace_4175663 : CollatzResearch.WordTrace tailWord_4175663 prefixEnd_4175663 714707390065067144336327 := by
  unfold tailWord_4175663
  simp only [CollatzResearch.WordTrace]
  refine ⟨152298941471293572309019643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101532627647529048206013095 152298941471293572309019643)
  ·
    refine ⟨228448412206940358463529465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152298941471293572309019643 228448412206940358463529465)
    ·
      refine ⟨171336309155205268847647099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228448412206940358463529465 171336309155205268847647099)
      ·
        refine ⟨257004463732807903271470649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171336309155205268847647099 257004463732807903271470649)
        ·
          refine ⟨192753347799605927453602987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257004463732807903271470649 192753347799605927453602987)
          ·
            refine ⟨289130021699408891180404481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192753347799605927453602987 289130021699408891180404481)
            ·
              refine ⟨216847516274556668385303361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289130021699408891180404481 216847516274556668385303361)
              ·
                refine ⟨162635637205917501288977521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216847516274556668385303361 162635637205917501288977521)
                ·
                  refine ⟨121976727904438125966733141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162635637205917501288977521 121976727904438125966733141)
                  ·
                    refine ⟨714707390065067144336327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121976727904438125966733141 714707390065067144336327)
                    ·
                      rfl

theorem cell23_4175663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_4175663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175663 prefixEnd_4175663 := by exact prefixLift 4175663
  have htrace : WordTrace (prefixWord ++ tailWord_4175663) baseStart_4175663 baseEnd_4175663 := by
    simpa [prefixWord, tailWord_4175663, baseEnd_4175663] using wordTrace_append hprefix tailTrace_4175663
  have hstable : (prefixWord ++ tailWord_4175663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175663).length < 2 ^ (prefixWord ++ tailWord_4175663).sum := by decide
  have hdescent : baseEnd_4175663 < baseStart_4175663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175717 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_4175717 : Nat := 118140960795 + 4175717 * 2 ^ 59
def prefixEnd_4175717 : Nat := 4983230072969 + 3 ^ 40 * 4175717 * 2
def baseEnd_4175717 : Nat := 2144149898150544221733733

theorem tailTrace_4175717 : CollatzResearch.WordTrace tailWord_4175717 prefixEnd_4175717 2144149898150544221733733 := by
  unfold tailWord_4175717
  simp only [CollatzResearch.WordTrace]
  refine ⟨152300911013097939531485405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101533940675398626354323603 152300911013097939531485405)
  ·
    refine ⟨57112841629911727324307027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152300911013097939531485405 57112841629911727324307027)
    ·
      refine ⟨85669262444867590986460541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57112841629911727324307027 85669262444867590986460541)
      ·
        refine ⟨32125973416825346619922703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85669262444867590986460541 32125973416825346619922703)
        ·
          refine ⟨48188960125238019929884055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32125973416825346619922703 48188960125238019929884055)
          ·
            refine ⟨72283440187857029894826083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48188960125238019929884055 72283440187857029894826083)
            ·
              refine ⟨108425160281785544842239125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72283440187857029894826083 108425160281785544842239125)
              ·
                refine ⟨5082429388208697414479959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108425160281785544842239125 5082429388208697414479959)
                ·
                  refine ⟨7623644082313046121719939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082429388208697414479959 7623644082313046121719939)
                  ·
                    refine ⟨11435466123469569182579909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7623644082313046121719939 11435466123469569182579909)
                    ·
                      refine ⟨2144149898150544221733733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11435466123469569182579909 2144149898150544221733733)
                      ·
                        rfl

theorem cell23_4175717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_4175717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175717 prefixEnd_4175717 := by exact prefixLift 4175717
  have htrace : WordTrace (prefixWord ++ tailWord_4175717) baseStart_4175717 baseEnd_4175717 := by
    simpa [prefixWord, tailWord_4175717, baseEnd_4175717] using wordTrace_append hprefix tailTrace_4175717
  have hstable : (prefixWord ++ tailWord_4175717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175717).length < 2 ^ (prefixWord ++ tailWord_4175717).sum := by decide
  have hdescent : baseEnd_4175717 < baseStart_4175717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175730 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4175730 : Nat := 118140960795 + 4175730 * 2 ^ 59
def prefixEnd_4175730 : Nat := 4983230072969 + 3 ^ 40 * 4175730 * 2
def baseEnd_4175730 : Nat := 2144156573399052670871173

theorem tailTrace_4175730 : CollatzResearch.WordTrace tailWord_4175730 prefixEnd_4175730 2144156573399052670871173 := by
  unfold tailWord_4175730
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075346290512710687927161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101534256774700561834472429 38075346290512710687927161)
  ·
    refine ⟨28556509717884533015945371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38075346290512710687927161 28556509717884533015945371)
    ·
      refine ⟨42834764576826799523918057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28556509717884533015945371 42834764576826799523918057)
      ·
        refine ⟨32126073432620099642938543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42834764576826799523918057 32126073432620099642938543)
        ·
          refine ⟨48189110148930149464407815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32126073432620099642938543 48189110148930149464407815)
          ·
            refine ⟨72283665223395224196611723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48189110148930149464407815 72283665223395224196611723)
            ·
              refine ⟨108425497835092836294917585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72283665223395224196611723 108425497835092836294917585)
              ·
                refine ⟨81319123376319627221188189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108425497835092836294917585 81319123376319627221188189)
                ·
                  refine ⟨30494671266119860207945571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81319123376319627221188189 30494671266119860207945571)
                  ·
                    refine ⟨45742006899179790311918357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30494671266119860207945571 45742006899179790311918357)
                    ·
                      refine ⟨2144156573399052670871173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45742006899179790311918357 2144156573399052670871173)
                      ·
                        rfl

theorem cell23_4175730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4175730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175730 prefixEnd_4175730 := by exact prefixLift 4175730
  have htrace : WordTrace (prefixWord ++ tailWord_4175730) baseStart_4175730 baseEnd_4175730 := by
    simpa [prefixWord, tailWord_4175730, baseEnd_4175730] using wordTrace_append hprefix tailTrace_4175730
  have hstable : (prefixWord ++ tailWord_4175730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175730).length < 2 ^ (prefixWord ++ tailWord_4175730).sum := by decide
  have hdescent : baseEnd_4175730 < baseStart_4175730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175754 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4175754 : Nat := 118140960795 + 4175754 * 2 ^ 59
def prefixEnd_4175754 : Nat := 4983230072969 + 3 ^ 40 * 4175754 * 2
def baseEnd_4175754 : Nat := 2144168896934760576971063

theorem tailTrace_4175754 : CollatzResearch.WordTrace tailWord_4175754 prefixEnd_4175754 2144168896934760576971063 := by
  unfold tailWord_4175754
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075565128490973712645579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101534840342642596567054877 38075565128490973712645579)
  ·
    refine ⟨57113347692736460568968369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38075565128490973712645579 57113347692736460568968369)
    ·
      refine ⟨42835010769552345426726277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57113347692736460568968369 42835010769552345426726277)
      ·
        refine ⟨8031564519291064767511177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42835010769552345426726277 8031564519291064767511177)
        ·
          refine ⟨6023673389468298575633383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8031564519291064767511177 6023673389468298575633383)
          ·
            refine ⟨9035510084202447863450075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023673389468298575633383 9035510084202447863450075)
            ·
              refine ⟨13553265126303671795175113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035510084202447863450075 13553265126303671795175113)
              ·
                refine ⟨10164948844727753846381335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13553265126303671795175113 10164948844727753846381335)
                ·
                  refine ⟨15247423267091630769572003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164948844727753846381335 15247423267091630769572003)
                  ·
                    refine ⟨22871134900637446154358005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15247423267091630769572003 22871134900637446154358005)
                    ·
                      refine ⟨2144168896934760576971063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22871134900637446154358005 2144168896934760576971063)
                      ·
                        rfl

theorem cell23_4175754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4175754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175754 prefixEnd_4175754 := by exact prefixLift 4175754
  have htrace : WordTrace (prefixWord ++ tailWord_4175754) baseStart_4175754 baseEnd_4175754 := by
    simpa [prefixWord, tailWord_4175754, baseEnd_4175754] using wordTrace_append hprefix tailTrace_4175754
  have hstable : (prefixWord ++ tailWord_4175754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175754).length < 2 ^ (prefixWord ++ tailWord_4175754).sum := by decide
  have hdescent : baseEnd_4175754 < baseStart_4175754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175764 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4175764 : Nat := 118140960795 + 4175764 * 2 ^ 59
def prefixEnd_4175764 : Nat := 4983230072969 + 3 ^ 40 * 4175764 * 2
def baseEnd_4175764 : Nat := 2144174031741305537846017

theorem tailTrace_4175764 : CollatzResearch.WordTrace tailWord_4175764 prefixEnd_4175764 2144174031741305537846017 := by
  unfold tailWord_4175764
  simp only [CollatzResearch.WordTrace]
  refine ⟨76151312621963833279223173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101535083495951777705630897 76151312621963833279223173)
  ·
    refine ⟨14278371116618218739854345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76151312621963833279223173 14278371116618218739854345)
    ·
      refine ⟨10708778337463664054890759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14278371116618218739854345 10708778337463664054890759)
      ·
        refine ⟨16063167506195496082336139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708778337463664054890759 16063167506195496082336139)
        ·
          refine ⟨24094751259293244123504209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16063167506195496082336139 24094751259293244123504209)
          ·
            refine ⟨18071063444469933092628157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24094751259293244123504209 18071063444469933092628157)
            ·
              refine ⟨6776648791676224909735559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18071063444469933092628157 6776648791676224909735559)
              ·
                refine ⟨10164973187514337364603339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776648791676224909735559 10164973187514337364603339)
                ·
                  refine ⟨15247459781271506046905009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164973187514337364603339 15247459781271506046905009)
                  ·
                    refine ⟨11435594835953629535178757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15247459781271506046905009 11435594835953629535178757)
                    ·
                      refine ⟨2144174031741305537846017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11435594835953629535178757 2144174031741305537846017)
                      ·
                        rfl

theorem cell23_4175764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4175764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175764 prefixEnd_4175764 := by exact prefixLift 4175764
  have htrace : WordTrace (prefixWord ++ tailWord_4175764) baseStart_4175764 baseEnd_4175764 := by
    simpa [prefixWord, tailWord_4175764, baseEnd_4175764] using wordTrace_append hprefix tailTrace_4175764
  have hstable : (prefixWord ++ tailWord_4175764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175764).length < 2 ^ (prefixWord ++ tailWord_4175764).sum := by decide
  have hdescent : baseEnd_4175764 < baseStart_4175764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175884 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_4175884 : Nat := 118140960795 + 4175884 * 2 ^ 59
def prefixEnd_4175884 : Nat := 4983230072969 + 3 ^ 40 * 4175884 * 2
def baseEnd_4175884 : Nat := 2144235649419845068345465

theorem tailTrace_4175884 : CollatzResearch.WordTrace tailWord_4175884 prefixEnd_4175884 2144235649419845068345465 := by
  unfold tailWord_4175884
  simp only [CollatzResearch.WordTrace]
  refine ⟨76153501001746463526407353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101538001335661951368543137 76153501001746463526407353)
  ·
    refine ⟨57115125751309847644805515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76153501001746463526407353 57115125751309847644805515)
    ·
      refine ⟨85672688626964771467208273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57115125751309847644805515 85672688626964771467208273)
      ·
        refine ⟨64254516470223578600406205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85672688626964771467208273 64254516470223578600406205)
        ·
          refine ⟨24095443676333841975152327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64254516470223578600406205 24095443676333841975152327)
          ·
            refine ⟨36143165514500762962728491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24095443676333841975152327 36143165514500762962728491)
            ·
              refine ⟨54214748271751144444092737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36143165514500762962728491 54214748271751144444092737)
              ·
                refine ⟨40661061203813358333069553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54214748271751144444092737 40661061203813358333069553)
                ·
                  refine ⟨30495795902860018749802165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40661061203813358333069553 30495795902860018749802165)
                  ·
                    refine ⟨2858980865893126757793953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30495795902860018749802165 2858980865893126757793953)
                    ·
                      refine ⟨2144235649419845068345465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2858980865893126757793953 2144235649419845068345465)
                      ·
                        rfl

theorem cell23_4175884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_4175884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4175884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4175884 prefixEnd_4175884 := by exact prefixLift 4175884
  have htrace : WordTrace (prefixWord ++ tailWord_4175884) baseStart_4175884 baseEnd_4175884 := by
    simpa [prefixWord, tailWord_4175884, baseEnd_4175884] using wordTrace_append hprefix tailTrace_4175884
  have hstable : (prefixWord ++ tailWord_4175884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175884).length < 2 ^ (prefixWord ++ tailWord_4175884).sum := by decide
  have hdescent : baseEnd_4175884 < baseStart_4175884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176001 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4176001 : Nat := 118140960795 + 4176001 * 2 ^ 59
def prefixEnd_4176001 : Nat := 4983230072969 + 3 ^ 40 * 4176001 * 2
def baseEnd_4176001 : Nat := 714765242218807036860809

theorem tailTrace_4176001 : CollatzResearch.WordTrace tailWord_4176001 prefixEnd_4176001 714765242218807036860809 := by
  unfold tailWord_4176001
  simp only [CollatzResearch.WordTrace]
  refine ⟨152311269344069056034823857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101540846229379370689882571 152311269344069056034823857)
  ·
    refine ⟨114233452008051792026117893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152311269344069056034823857 114233452008051792026117893)
    ·
      refine ⟨21418772251509711004897105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114233452008051792026117893 21418772251509711004897105)
      ·
        refine ⟨16064079188632283253672829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21418772251509711004897105 16064079188632283253672829)
        ·
          refine ⟨6024029695737106220127311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16064079188632283253672829 6024029695737106220127311)
          ·
            refine ⟨9036044543605659330190967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024029695737106220127311 9036044543605659330190967)
            ·
              refine ⟨13554066815408488995286451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036044543605659330190967 13554066815408488995286451)
              ·
                refine ⟨20331100223112733492929677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554066815408488995286451 20331100223112733492929677)
                ·
                  refine ⟨7624162583667275059848629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20331100223112733492929677 7624162583667275059848629)
                  ·
                    refine ⟨714765242218807036860809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7624162583667275059848629 714765242218807036860809)
                    ·
                      rfl

theorem cell23_4176001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4176001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176001 prefixEnd_4176001 := by exact prefixLift 4176001
  have htrace : WordTrace (prefixWord ++ tailWord_4176001) baseStart_4176001 baseEnd_4176001 := by
    simpa [prefixWord, tailWord_4176001, baseEnd_4176001] using wordTrace_append hprefix tailTrace_4176001
  have hstable : (prefixWord ++ tailWord_4176001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176001).length < 2 ^ (prefixWord ++ tailWord_4176001).sum := by decide
  have hdescent : baseEnd_4176001 < baseStart_4176001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176008 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4176008 : Nat := 118140960795 + 4176008 * 2 ^ 59
def prefixEnd_4176008 : Nat := 4983230072969 + 3 ^ 40 * 4176008 * 2
def baseEnd_4176008 : Nat := 2144299321021002583194895

theorem tailTrace_4176008 : CollatzResearch.WordTrace tailWord_4176008 prefixEnd_4176008 2144299321021002583194895 := by
  unfold tailWord_4176008
  simp only [CollatzResearch.WordTrace]
  refine ⟨76155762327521848115164339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101541016436695797486885785 76155762327521848115164339)
  ·
    refine ⟨114233643491282772172746509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76155762327521848115164339 114233643491282772172746509)
    ·
      refine ⟨42837616309231039564779941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114233643491282772172746509 42837616309231039564779941)
      ·
        refine ⟨8032053057980819918396239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42837616309231039564779941 8032053057980819918396239)
        ·
          refine ⟨12048079586971229877594359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032053057980819918396239 12048079586971229877594359)
          ·
            refine ⟨18072119380456844816391539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048079586971229877594359 18072119380456844816391539)
            ·
              refine ⟨27108179070685267224587309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18072119380456844816391539 27108179070685267224587309)
              ·
                refine ⟨10165567151506975209220241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27108179070685267224587309 10165567151506975209220241)
                ·
                  refine ⟨7624175363630231406915181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10165567151506975209220241 7624175363630231406915181)
                  ·
                    refine ⟨2859065761361336777593193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7624175363630231406915181 2859065761361336777593193)
                    ·
                      refine ⟨2144299321021002583194895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859065761361336777593193 2144299321021002583194895)
                      ·
                        rfl

theorem cell23_4176008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4176008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176008 prefixEnd_4176008 := by exact prefixLift 4176008
  have htrace : WordTrace (prefixWord ++ tailWord_4176008) baseStart_4176008 baseEnd_4176008 := by
    simpa [prefixWord, tailWord_4176008, baseEnd_4176008] using wordTrace_append hprefix tailTrace_4176008
  have hstable : (prefixWord ++ tailWord_4176008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176008).length < 2 ^ (prefixWord ++ tailWord_4176008).sum := by decide
  have hdescent : baseEnd_4176008 < baseStart_4176008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176017 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_4176017 : Nat := 118140960795 + 4176017 * 2 ^ 59
def prefixEnd_4176017 : Nat := 4983230072969 + 3 ^ 40 * 4176017 * 2
def baseEnd_4176017 : Nat := 2144303942346893047982353

theorem tailTrace_4176017 : CollatzResearch.WordTrace tailWord_4176017 prefixEnd_4176017 2144303942346893047982353 := by
  unfold tailWord_4176017
  simp only [CollatzResearch.WordTrace]
  refine ⟨152311852912011090767406305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101541235274674060511604203 152311852912011090767406305)
  ·
    refine ⟨114233889684008318075554729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152311852912011090767406305 114233889684008318075554729)
    ·
      refine ⟨85675417263006238556666047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114233889684008318075554729 85675417263006238556666047)
      ·
        refine ⟨128513125894509357834999071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85675417263006238556666047 128513125894509357834999071)
        ·
          refine ⟨192769688841764036752498607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128513125894509357834999071 192769688841764036752498607)
          ·
            refine ⟨289154533262646055128747911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192769688841764036752498607 289154533262646055128747911)
            ·
              refine ⟨433731799893969082693121867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289154533262646055128747911 433731799893969082693121867)
              ·
                refine ⟨650597699840953624039682801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433731799893969082693121867 650597699840953624039682801)
                ·
                  refine ⟨487948274880715218029762101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650597699840953624039682801 487948274880715218029762101)
                  ·
                    refine ⟨45745150770067051690290197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 487948274880715218029762101 45745150770067051690290197)
                    ·
                      refine ⟨2144303942346893047982353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45745150770067051690290197 2144303942346893047982353)
                      ·
                        rfl

theorem cell23_4176017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_4176017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176017 prefixEnd_4176017 := by exact prefixLift 4176017
  have htrace : WordTrace (prefixWord ++ tailWord_4176017) baseStart_4176017 baseEnd_4176017 := by
    simpa [prefixWord, tailWord_4176017, baseEnd_4176017] using wordTrace_append hprefix tailTrace_4176017
  have hstable : (prefixWord ++ tailWord_4176017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176017).length < 2 ^ (prefixWord ++ tailWord_4176017).sum := by decide
  have hdescent : baseEnd_4176017 < baseStart_4176017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176018 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4176018 : Nat := 118140960795 + 4176018 * 2 ^ 59
def prefixEnd_4176018 : Nat := 4983230072969 + 3 ^ 40 * 4176018 * 2
def baseEnd_4176018 : Nat := 714768151942515848023283

theorem tailTrace_4176018 : CollatzResearch.WordTrace tailWord_4176018 prefixEnd_4176018 714768151942515848023283 := by
  unfold tailWord_4176018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38077972346251866984548177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101541259590004978625461805 38077972346251866984548177)
  ·
    refine ⟨28558479259688900238411133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38077972346251866984548177 28558479259688900238411133)
    ·
      refine ⟨10709429722383337589404175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28558479259688900238411133 10709429722383337589404175)
      ·
        refine ⟨16064144583575006384106263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10709429722383337589404175 16064144583575006384106263)
        ·
          refine ⟨24096216875362509576159395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16064144583575006384106263 24096216875362509576159395)
          ·
            refine ⟨36144325313043764364239093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24096216875362509576159395 36144325313043764364239093)
            ·
              refine ⟨3388530498097852909147415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36144325313043764364239093 3388530498097852909147415)
              ·
                refine ⟨5082795747146779363721123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388530498097852909147415 5082795747146779363721123)
                ·
                  refine ⟨7624193620720169045581685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082795747146779363721123 7624193620720169045581685)
                  ·
                    refine ⟨714768151942515848023283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7624193620720169045581685 714768151942515848023283)
                    ·
                      rfl

theorem cell23_4176018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4176018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176018 prefixEnd_4176018 := by exact prefixLift 4176018
  have htrace : WordTrace (prefixWord ++ tailWord_4176018) baseStart_4176018 baseEnd_4176018 := by
    simpa [prefixWord, tailWord_4176018, baseEnd_4176018] using wordTrace_append hprefix tailTrace_4176018
  have hstable : (prefixWord ++ tailWord_4176018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176018).length < 2 ^ (prefixWord ++ tailWord_4176018).sum := by decide
  have hdescent : baseEnd_4176018 < baseStart_4176018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176032 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 1, 1, 3]
def baseStart_4176032 : Nat := 118140960795 + 4176032 * 2 ^ 59
def prefixEnd_4176032 : Nat := 4983230072969 + 3 ^ 40 * 4176032 * 2
def baseEnd_4176032 : Nat := 2144311644556710489294785

theorem tailTrace_4176032 : CollatzResearch.WordTrace tailWord_4176032 prefixEnd_4176032 2144311644556710489294785 := by
  unfold tailWord_4176032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76156200003478374164601175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101541600004637832219468233 76156200003478374164601175)
  ·
    refine ⟨114234300005217561246901763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76156200003478374164601175 114234300005217561246901763)
    ·
      refine ⟨171351450007826341870352645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114234300005217561246901763 171351450007826341870352645)
      ·
        refine ⟨32128396876467439100691121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171351450007826341870352645 32128396876467439100691121)
        ·
          refine ⟨24096297657350579325518341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32128396876467439100691121 24096297657350579325518341)
          ·
            refine ⟨4518055810753233623534689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24096297657350579325518341 4518055810753233623534689)
            ·
              refine ⟨3388541858064925217651017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518055810753233623534689 3388541858064925217651017)
              ·
                refine ⟨2541406393548693913238263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388541858064925217651017 2541406393548693913238263)
                ·
                  refine ⟨3812109590323040869857395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541406393548693913238263 3812109590323040869857395)
                  ·
                    refine ⟨5718164385484561304786093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3812109590323040869857395 5718164385484561304786093)
                    ·
                      refine ⟨2144311644556710489294785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5718164385484561304786093 2144311644556710489294785)
                      ·
                        rfl

theorem cell23_4176032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_4176032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176032 prefixEnd_4176032 := by exact prefixLift 4176032
  have htrace : WordTrace (prefixWord ++ tailWord_4176032) baseStart_4176032 baseEnd_4176032 := by
    simpa [prefixWord, tailWord_4176032, baseEnd_4176032] using wordTrace_append hprefix tailTrace_4176032
  have hstable : (prefixWord ++ tailWord_4176032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176032).length < 2 ^ (prefixWord ++ tailWord_4176032).sum := by decide
  have hdescent : baseEnd_4176032 < baseStart_4176032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176088 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_4176088 : Nat := 118140960795 + 4176088 * 2 ^ 59
def prefixEnd_4176088 : Nat := 4983230072969 + 3 ^ 40 * 4176088 * 2
def baseEnd_4176088 : Nat := 2144340399473362270194527

theorem tailTrace_4176088 : CollatzResearch.WordTrace tailWord_4176088 prefixEnd_4176088 2144340399473362270194527 := by
  unfold tailWord_4176088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76157221247376934946620459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101542961663169246595493945 76157221247376934946620459)
  ·
    refine ⟨114235831871065402419930689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76157221247376934946620459 114235831871065402419930689)
    ·
      refine ⟨85676873903299051814948017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114235831871065402419930689 85676873903299051814948017)
      ·
        refine ⟨64257655427474288861211013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85676873903299051814948017 64257655427474288861211013)
        ·
          refine ⟨12048310392651429161477065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64257655427474288861211013 12048310392651429161477065)
          ·
            refine ⟨9036232794488571871107799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12048310392651429161477065 9036232794488571871107799)
            ·
              refine ⟨13554349191732857806661699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036232794488571871107799 13554349191732857806661699)
              ·
                refine ⟨20331523787599286709992549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554349191732857806661699 20331523787599286709992549)
                ·
                  refine ⟨3812160710174866258123603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20331523787599286709992549 3812160710174866258123603)
                  ·
                    refine ⟨5718241065262299387185405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3812160710174866258123603 5718241065262299387185405)
                    ·
                      refine ⟨2144340399473362270194527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5718241065262299387185405 2144340399473362270194527)
                      ·
                        rfl

theorem cell23_4176088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_4176088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176088 prefixEnd_4176088 := by exact prefixLift 4176088
  have htrace : WordTrace (prefixWord ++ tailWord_4176088) baseStart_4176088 baseEnd_4176088 := by
    simpa [prefixWord, tailWord_4176088, baseEnd_4176088] using wordTrace_append hprefix tailTrace_4176088
  have hstable : (prefixWord ++ tailWord_4176088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176088).length < 2 ^ (prefixWord ++ tailWord_4176088).sum := by decide
  have hdescent : baseEnd_4176088 < baseStart_4176088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176128 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2]
def baseStart_4176128 : Nat := 118140960795 + 4176128 * 2 ^ 59
def prefixEnd_4176128 : Nat := 4983230072969 + 3 ^ 40 * 4176128 * 2
def baseEnd_4176128 : Nat := 2144360938699542113694343

theorem tailTrace_4176128 : CollatzResearch.WordTrace tailWord_4176128 prefixEnd_4176128 2144360938699542113694343 := by
  unfold tailWord_4176128
  simp only [CollatzResearch.WordTrace]
  refine ⟨76157950707304478362348519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101543934276405971149798025 76157950707304478362348519)
  ·
    refine ⟨114236926060956717543522779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76157950707304478362348519 114236926060956717543522779)
    ·
      refine ⟨171355389091435076315284169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114236926060956717543522779 171355389091435076315284169)
      ·
        refine ⟨128516541818576307236463127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171355389091435076315284169 128516541818576307236463127)
        ·
          refine ⟨192774812727864460854694691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128516541818576307236463127 192774812727864460854694691)
          ·
            refine ⟨289162219091796691282042037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192774812727864460854694691 289162219091796691282042037)
            ·
              refine ⟨27108958039855939807691441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289162219091796691282042037 27108958039855939807691441)
              ·
                refine ⟨20331718529891954855768581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27108958039855939807691441 20331718529891954855768581)
                ·
                  refine ⟨3812197224354741535456609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20331718529891954855768581 3812197224354741535456609)
                  ·
                    refine ⟨2859147918266056151592457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812197224354741535456609 2859147918266056151592457)
                    ·
                      refine ⟨2144360938699542113694343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859147918266056151592457 2144360938699542113694343)
                      ·
                        rfl

theorem cell23_4176128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_4176128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176128 prefixEnd_4176128 := by exact prefixLift 4176128
  have htrace : WordTrace (prefixWord ++ tailWord_4176128) baseStart_4176128 baseEnd_4176128 := by
    simpa [prefixWord, tailWord_4176128, baseEnd_4176128] using wordTrace_append hprefix tailTrace_4176128
  have hstable : (prefixWord ++ tailWord_4176128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176128).length < 2 ^ (prefixWord ++ tailWord_4176128).sum := by decide
  have hdescent : baseEnd_4176128 < baseStart_4176128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176151 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 7]
def baseStart_4176151 : Nat := 118140960795 + 4176151 * 2 ^ 59
def prefixEnd_4176151 : Nat := 4983230072969 + 3 ^ 40 * 4176151 * 2
def baseEnd_4176151 : Nat := 238263638750510613745193

theorem tailTrace_4176151 : CollatzResearch.WordTrace tailWord_4176151 prefixEnd_4176151 238263638750510613745193 := by
  unfold tailWord_4176151
  simp only [CollatzResearch.WordTrace]
  refine ⟨152316740293525631652784307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101544493529017087768522871 152316740293525631652784307)
  ·
    refine ⟨228475110440288447479176461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152316740293525631652784307 228475110440288447479176461)
    ·
      refine ⟨85678166415108167804691173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228475110440288447479176461 85678166415108167804691173)
      ·
        refine ⟨16064656202832781463379595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85678166415108167804691173 16064656202832781463379595)
        ·
          refine ⟨24096984304249172195069393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16064656202832781463379595 24096984304249172195069393)
          ·
            refine ⟨18072738228186879146302045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24096984304249172195069393 18072738228186879146302045)
            ·
              refine ⟨6777276835570079679863267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18072738228186879146302045 6777276835570079679863267)
              ·
                refine ⟨10165915253355119519794901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777276835570079679863267 10165915253355119519794901)
                ·
                  refine ⟨238263638750510613745193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10165915253355119519794901 238263638750510613745193)
                  ·
                    rfl

theorem cell23_4176151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 7].length) (baseStart_4176151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176151 prefixEnd_4176151 := by exact prefixLift 4176151
  have htrace : WordTrace (prefixWord ++ tailWord_4176151) baseStart_4176151 baseEnd_4176151 := by
    simpa [prefixWord, tailWord_4176151, baseEnd_4176151] using wordTrace_append hprefix tailTrace_4176151
  have hstable : (prefixWord ++ tailWord_4176151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176151).length < 2 ^ (prefixWord ++ tailWord_4176151).sum := by decide
  have hdescent : baseEnd_4176151 < baseStart_4176151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176161 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4176161 : Nat := 118140960795 + 4176161 * 2 ^ 59
def prefixEnd_4176161 : Nat := 4983230072969 + 3 ^ 40 * 4176161 * 2
def baseEnd_4176161 : Nat := 2144377883561140484581691

theorem tailTrace_4176161 : CollatzResearch.WordTrace tailWord_4176161 prefixEnd_4176161 2144377883561140484581691 := by
  unfold tailWord_4176161
  simp only [CollatzResearch.WordTrace]
  refine ⟨152317105023489403360648337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101544736682326268907098891 152317105023489403360648337)
  ·
    refine ⟨114237828767617052520486253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152317105023489403360648337 114237828767617052520486253)
    ·
      refine ⟨42839185787856394695182345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114237828767617052520486253 42839185787856394695182345)
      ·
        refine ⟨32129389340892296021386759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42839185787856394695182345 32129389340892296021386759)
        ·
          refine ⟨48194084011338444032080139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32129389340892296021386759 48194084011338444032080139)
          ·
            refine ⟨72291126017007666048120209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48194084011338444032080139 72291126017007666048120209)
            ·
              refine ⟨54218344512755749536090157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72291126017007666048120209 54218344512755749536090157)
              ·
                refine ⟨20331879192283406076033809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54218344512755749536090157 20331879192283406076033809)
                ·
                  refine ⟨15248909394212554557025357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20331879192283406076033809 15248909394212554557025357)
                  ·
                    refine ⟨5718341022829707958884509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15248909394212554557025357 5718341022829707958884509)
                    ·
                      refine ⟨2144377883561140484581691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5718341022829707958884509 2144377883561140484581691)
                      ·
                        rfl

theorem cell23_4176161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4176161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176161 prefixEnd_4176161 := by exact prefixLift 4176161
  have htrace : WordTrace (prefixWord ++ tailWord_4176161) baseStart_4176161 baseEnd_4176161 := by
    simpa [prefixWord, tailWord_4176161, baseEnd_4176161] using wordTrace_append hprefix tailTrace_4176161
  have hstable : (prefixWord ++ tailWord_4176161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176161).length < 2 ^ (prefixWord ++ tailWord_4176161).sum := by decide
  have hdescent : baseEnd_4176161 < baseStart_4176161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176162 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_4176162 : Nat := 118140960795 + 4176162 * 2 ^ 59
def prefixEnd_4176162 : Nat := 4983230072969 + 3 ^ 40 * 4176162 * 2
def baseEnd_4176162 : Nat := 2144378397041794980669187

theorem tailTrace_4176162 : CollatzResearch.WordTrace tailWord_4176162 prefixEnd_4176162 2144378397041794980669187 := by
  unfold tailWord_4176162
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079285374121445132858685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101544760997657187020956493 38079285374121445132858685)
  ·
    refine ⟨14279732015295541924822007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38079285374121445132858685 14279732015295541924822007)
    ·
      refine ⟨21419598022943312887233011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279732015295541924822007 21419598022943312887233011)
      ·
        refine ⟨32129397034414969330849517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419598022943312887233011 32129397034414969330849517)
        ·
          refine ⟨12048523887905613499068569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32129397034414969330849517 12048523887905613499068569)
          ·
            refine ⟨9036392915929210124301427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12048523887905613499068569 9036392915929210124301427)
            ·
              refine ⟨13554589373893815186452141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036392915929210124301427 13554589373893815186452141)
              ·
                refine ⟨5082971015210180694919553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13554589373893815186452141 5082971015210180694919553)
                ·
                  refine ⟨3812228261407635521189665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082971015210180694919553 3812228261407635521189665)
                  ·
                    refine ⟨2859171196055726640892249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812228261407635521189665 2859171196055726640892249)
                    ·
                      refine ⟨2144378397041794980669187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859171196055726640892249 2144378397041794980669187)
                      ·
                        rfl

theorem cell23_4176162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_4176162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176162 prefixEnd_4176162 := by exact prefixLift 4176162
  have htrace : WordTrace (prefixWord ++ tailWord_4176162) baseStart_4176162 baseEnd_4176162 := by
    simpa [prefixWord, tailWord_4176162, baseEnd_4176162] using wordTrace_append hprefix tailTrace_4176162
  have hstable : (prefixWord ++ tailWord_4176162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176162).length < 2 ^ (prefixWord ++ tailWord_4176162).sum := by decide
  have hdescent : baseEnd_4176162 < baseStart_4176162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176228 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_4176228 : Nat := 118140960795 + 4176228 * 2 ^ 59
def prefixEnd_4176228 : Nat := 4983230072969 + 3 ^ 40 * 4176228 * 2
def baseEnd_4176228 : Nat := 714804095588330574147961

theorem tailTrace_4176228 : CollatzResearch.WordTrace tailWord_4176228 prefixEnd_4176228 714804095588330574147961 := by
  unfold tailWord_4176228
  simp only [CollatzResearch.WordTrace]
  refine ⟨76159774357123336901668669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101546365809497782535558225 76159774357123336901668669)
  ·
    refine ⟨28559915383921251338125751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76159774357123336901668669 28559915383921251338125751)
    ·
      refine ⟨42839873075881877007188627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28559915383921251338125751 42839873075881877007188627)
      ·
        refine ⟨64259809613822815510782941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42839873075881877007188627 64259809613822815510782941)
        ·
          refine ⟨24097428605183555816543603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64259809613822815510782941 24097428605183555816543603)
          ·
            refine ⟨36146142907775333724815405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24097428605183555816543603 36146142907775333724815405)
            ·
              refine ⟨13554803590415750146805777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36146142907775333724815405 13554803590415750146805777)
              ·
                refine ⟨10166102692811812610104333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13554803590415750146805777 10166102692811812610104333)
                ·
                  refine ⟨3812288509804429728789125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10166102692811812610104333 3812288509804429728789125)
                  ·
                    refine ⟨714804095588330574147961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3812288509804429728789125 714804095588330574147961)
                    ·
                      rfl

theorem cell23_4176228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_4176228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176228 prefixEnd_4176228 := by exact prefixLift 4176228
  have htrace : WordTrace (prefixWord ++ tailWord_4176228) baseStart_4176228 baseEnd_4176228 := by
    simpa [prefixWord, tailWord_4176228, baseEnd_4176228] using wordTrace_append hprefix tailTrace_4176228
  have hstable : (prefixWord ++ tailWord_4176228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176228).length < 2 ^ (prefixWord ++ tailWord_4176228).sum := by decide
  have hdescent : baseEnd_4176228 < baseStart_4176228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176288 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_4176288 : Nat := 118140960795 + 4176288 * 2 ^ 59
def prefixEnd_4176288 : Nat := 4983230072969 + 3 ^ 40 * 4176288 * 2
def baseEnd_4176288 : Nat := 714814365201420495897869

theorem tailTrace_4176288 : CollatzResearch.WordTrace tailWord_4176288 prefixEnd_4176288 714814365201420495897869 := by
  unfold tailWord_4176288
  simp only [CollatzResearch.WordTrace]
  refine ⟨76160868547014652025260759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101547824729352869367014345 76160868547014652025260759)
  ·
    refine ⟨114241302820521978037891139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76160868547014652025260759 114241302820521978037891139)
    ·
      refine ⟨171361954230782967056836709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114241302820521978037891139 171361954230782967056836709)
      ·
        refine ⟨32130366418271806323156883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171361954230782967056836709 32130366418271806323156883)
        ·
          refine ⟨48195549627407709484735325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32130366418271806323156883 48195549627407709484735325)
          ·
            refine ⟨18073331110277891056775747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48195549627407709484735325 18073331110277891056775747)
            ·
              refine ⟨27109996665416836585163621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18073331110277891056775747 27109996665416836585163621)
              ·
                refine ⟨5083124374765656859718179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27109996665416836585163621 5083124374765656859718179)
                ·
                  refine ⟨7624686562148485289577269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083124374765656859718179 7624686562148485289577269)
                  ·
                    refine ⟨714814365201420495897869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7624686562148485289577269 714814365201420495897869)
                    ·
                      rfl

theorem cell23_4176288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_4176288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176288 prefixEnd_4176288 := by exact prefixLift 4176288
  have htrace : WordTrace (prefixWord ++ tailWord_4176288) baseStart_4176288 baseEnd_4176288 := by
    simpa [prefixWord, tailWord_4176288, baseEnd_4176288] using wordTrace_append hprefix tailTrace_4176288
  have hstable : (prefixWord ++ tailWord_4176288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176288).length < 2 ^ (prefixWord ++ tailWord_4176288).sum := by decide
  have hdescent : baseEnd_4176288 < baseStart_4176288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176295 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_4176295 : Nat := 118140960795 + 4176295 * 2 ^ 59
def prefixEnd_4176295 : Nat := 4983230072969 + 3 ^ 40 * 4176295 * 2
def baseEnd_4176295 : Nat := 2144446689968842960306075

theorem tailTrace_4176295 : CollatzResearch.WordTrace tailWord_4176295 prefixEnd_4176295 2144446689968842960306075 := by
  unfold tailWord_4176295
  simp only [CollatzResearch.WordTrace]
  refine ⟨152321992405003944246026339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101547994936669296164017559 152321992405003944246026339)
  ·
    refine ⟨228482988607505916369039509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152321992405003944246026339 228482988607505916369039509)
    ·
      refine ⟨10710140090976839829798727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228482988607505916369039509 10710140090976839829798727)
      ·
        refine ⟨16065210136465259744698091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710140090976839829798727 16065210136465259744698091)
        ·
          refine ⟨24097815204697889617047137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065210136465259744698091 24097815204697889617047137)
          ·
            refine ⟨18073361403523417212785353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24097815204697889617047137 18073361403523417212785353)
            ·
              refine ⟨13555021052642562909589015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073361403523417212785353 13555021052642562909589015)
              ·
                refine ⟨20332531578963844364383523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555021052642562909589015 20332531578963844364383523)
                ·
                  refine ⟨30498797368445766546575285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20332531578963844364383523 30498797368445766546575285)
                  ·
                    refine ⟨2859262253291790613741433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30498797368445766546575285 2859262253291790613741433)
                    ·
                      refine ⟨2144446689968842960306075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859262253291790613741433 2144446689968842960306075)
                      ·
                        rfl

theorem cell23_4176295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_4176295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176295 prefixEnd_4176295 := by exact prefixLift 4176295
  have htrace : WordTrace (prefixWord ++ tailWord_4176295) baseStart_4176295 baseEnd_4176295 := by
    simpa [prefixWord, tailWord_4176295, baseEnd_4176295] using wordTrace_append hprefix tailTrace_4176295
  have hstable : (prefixWord ++ tailWord_4176295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176295).length < 2 ^ (prefixWord ++ tailWord_4176295).sum := by decide
  have hdescent : baseEnd_4176295 < baseStart_4176295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176328 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_4176328 : Nat := 118140960795 + 4176328 * 2 ^ 59
def prefixEnd_4176328 : Nat := 4983230072969 + 3 ^ 40 * 4176328 * 2
def baseEnd_4176328 : Nat := 2144463634830441331193423

theorem tailTrace_4176328 : CollatzResearch.WordTrace tailWord_4176328 prefixEnd_4176328 2144463634830441331193423 := by
  unfold tailWord_4176328
  simp only [CollatzResearch.WordTrace]
  refine ⟨76161598006942195440988819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101548797342589593921318425 76161598006942195440988819)
  ·
    refine ⟨114242397010413293161483229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76161598006942195440988819 114242397010413293161483229)
    ·
      refine ⟨42840898878904984935556211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114242397010413293161483229 42840898878904984935556211)
      ·
        refine ⟨64261348318357477403334317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42840898878904984935556211 64261348318357477403334317)
        ·
          refine ⟨24098005619384054026250369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64261348318357477403334317 24098005619384054026250369)
          ·
            refine ⟨18073504214538040519687777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24098005619384054026250369 18073504214538040519687777)
            ·
              refine ⟨13555128160903530389765833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073504214538040519687777 13555128160903530389765833)
              ·
                refine ⟨10166346120677647792324375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13555128160903530389765833 10166346120677647792324375)
                ·
                  refine ⟨15249519181016471688486563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166346120677647792324375 15249519181016471688486563)
                  ·
                    refine ⟨22874278771524707532729845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15249519181016471688486563 22874278771524707532729845)
                    ·
                      refine ⟨2144463634830441331193423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22874278771524707532729845 2144463634830441331193423)
                      ·
                        rfl

theorem cell23_4176328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_4176328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176328 prefixEnd_4176328 := by exact prefixLift 4176328
  have htrace : WordTrace (prefixWord ++ tailWord_4176328) baseStart_4176328 baseEnd_4176328 := by
    simpa [prefixWord, tailWord_4176328, baseEnd_4176328] using wordTrace_append hprefix tailTrace_4176328
  have hstable : (prefixWord ++ tailWord_4176328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176328).length < 2 ^ (prefixWord ++ tailWord_4176328).sum := by decide
  have hdescent : baseEnd_4176328 < baseStart_4176328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176355 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4176355 : Nat := 118140960795 + 4176355 * 2 ^ 59
def prefixEnd_4176355 : Nat := 4983230072969 + 3 ^ 40 * 4176355 * 2
def baseEnd_4176355 : Nat := 2144477498808112725555799

theorem tailTrace_4176355 : CollatzResearch.WordTrace tailWord_4176355 prefixEnd_4176355 2144477498808112725555799 := by
  unfold tailWord_4176355
  simp only [CollatzResearch.WordTrace]
  refine ⟨152324180784786574493210519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101549453856524382995473679 152324180784786574493210519)
  ·
    refine ⟨228486271177179861739815779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152324180784786574493210519 228486271177179861739815779)
    ·
      refine ⟨342729406765769792609723669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228486271177179861739815779 342729406765769792609723669)
      ·
        refine ⟨16065440942145459028580797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342729406765769792609723669 16065440942145459028580797)
        ·
          refine ⟨6024540353304547135717799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16065440942145459028580797 6024540353304547135717799)
          ·
            refine ⟨9036810529956820703576699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024540353304547135717799 9036810529956820703576699)
            ·
              refine ⟨13555215794935231055365049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036810529956820703576699 13555215794935231055365049)
              ·
                refine ⟨10166411846201423291523787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13555215794935231055365049 10166411846201423291523787)
                ·
                  refine ⟨15249617769302134937285681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166411846201423291523787 15249617769302134937285681)
                  ·
                    refine ⟨11437213326976601202964261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15249617769302134937285681 11437213326976601202964261)
                    ·
                      refine ⟨2144477498808112725555799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11437213326976601202964261 2144477498808112725555799)
                      ·
                        rfl

theorem cell23_4176355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4176355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176355 prefixEnd_4176355 := by exact prefixLift 4176355
  have htrace : WordTrace (prefixWord ++ tailWord_4176355) baseStart_4176355 baseEnd_4176355 := by
    simpa [prefixWord, tailWord_4176355, baseEnd_4176355] using wordTrace_append hprefix tailTrace_4176355
  have hstable : (prefixWord ++ tailWord_4176355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176355).length < 2 ^ (prefixWord ++ tailWord_4176355).sum := by decide
  have hdescent : baseEnd_4176355 < baseStart_4176355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176359 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4176359 : Nat := 118140960795 + 4176359 * 2 ^ 59
def prefixEnd_4176359 : Nat := 4983230072969 + 3 ^ 40 * 4176359 * 2
def baseEnd_4176359 : Nat := 2144479552730730709905781

theorem tailTrace_4176359 : CollatzResearch.WordTrace tailWord_4176359 prefixEnd_4176359 2144479552730730709905781 := by
  unfold tailWord_4176359
  simp only [CollatzResearch.WordTrace]
  refine ⟨152324326676772083176356131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101549551117848055450904087 152324326676772083176356131)
  ·
    refine ⟨228486490015158124764534197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152324326676772083176356131 228486490015158124764534197)
    ·
      refine ⟨21420608438921074196675081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228486490015158124764534197 21420608438921074196675081)
      ·
        refine ⟨16065456329190805647506311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21420608438921074196675081 16065456329190805647506311)
        ·
          refine ⟨24098184493786208471259467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065456329190805647506311 24098184493786208471259467)
          ·
            refine ⟨36147276740679312706889201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24098184493786208471259467 36147276740679312706889201)
            ·
              refine ⟨27110457555509484530166901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36147276740679312706889201 27110457555509484530166901)
              ·
                refine ⟨2541605395829014174703147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27110457555509484530166901 2541605395829014174703147)
                ·
                  refine ⟨3812408093743521262054721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541605395829014174703147 3812408093743521262054721)
                  ·
                    refine ⟨2859306070307640946541041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812408093743521262054721 2859306070307640946541041)
                    ·
                      refine ⟨2144479552730730709905781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859306070307640946541041 2144479552730730709905781)
                      ·
                        rfl

theorem cell23_4176359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4176359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176359 prefixEnd_4176359 := by exact prefixLift 4176359
  have htrace : WordTrace (prefixWord ++ tailWord_4176359) baseStart_4176359 baseEnd_4176359 := by
    simpa [prefixWord, tailWord_4176359, baseEnd_4176359] using wordTrace_append hprefix tailTrace_4176359
  have hstable : (prefixWord ++ tailWord_4176359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176359).length < 2 ^ (prefixWord ++ tailWord_4176359).sum := by decide
  have hdescent : baseEnd_4176359 < baseStart_4176359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176418 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4176418 : Nat := 118140960795 + 4176418 * 2 ^ 59
def prefixEnd_4176418 : Nat := 4983230072969 + 3 ^ 40 * 4176418 * 2
def baseEnd_4176418 : Nat := 2144509848089345979068009

theorem tailTrace_4176418 : CollatzResearch.WordTrace tailWord_4176418 prefixEnd_4176418 2144509848089345979068009 := by
  unfold tailWord_4176418
  simp only [CollatzResearch.WordTrace]
  refine ⟨38081619645889584063188477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101550985722372224168502605 38081619645889584063188477)
  ·
    refine ⟨14280607367208594023695679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38081619645889584063188477 14280607367208594023695679)
    ·
      refine ⟨21420911050812891035543519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14280607367208594023695679 21420911050812891035543519)
      ·
        refine ⟨32131366576219336553315279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21420911050812891035543519 32131366576219336553315279)
        ·
          refine ⟨48197049864329004829972919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32131366576219336553315279 48197049864329004829972919)
          ·
            refine ⟨72295574796493507244959379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48197049864329004829972919 72295574796493507244959379)
            ·
              refine ⟨108443362194740260867439069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72295574796493507244959379 108443362194740260867439069)
              ·
                refine ⟨40666260823027597825289651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108443362194740260867439069 40666260823027597825289651)
                ·
                  refine ⟨60999391234541396737934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40666260823027597825289651 60999391234541396737934477)
                  ·
                    refine ⟨22874771712953023776725429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60999391234541396737934477 22874771712953023776725429)
                    ·
                      refine ⟨2144509848089345979068009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22874771712953023776725429 2144509848089345979068009)
                      ·
                        rfl

theorem cell23_4176418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4176418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176418 prefixEnd_4176418 := by exact prefixLift 4176418
  have htrace : WordTrace (prefixWord ++ tailWord_4176418) baseStart_4176418 baseEnd_4176418 := by
    simpa [prefixWord, tailWord_4176418, baseEnd_4176418] using wordTrace_append hprefix tailTrace_4176418
  have hstable : (prefixWord ++ tailWord_4176418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176418).length < 2 ^ (prefixWord ++ tailWord_4176418).sum := by decide
  have hdescent : baseEnd_4176418 < baseStart_4176418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176419 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 1, 3, 2]
def baseStart_4176419 : Nat := 118140960795 + 4176419 * 2 ^ 59
def prefixEnd_4176419 : Nat := 4983230072969 + 3 ^ 40 * 4176419 * 2
def baseEnd_4176419 : Nat := 2144510361570000475155505

theorem tailTrace_4176419 : CollatzResearch.WordTrace tailWord_4176419 prefixEnd_4176419 2144510361570000475155505 := by
  unfold tailWord_4176419
  simp only [CollatzResearch.WordTrace]
  refine ⟨152326515056554713423540311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101551010037703142282360207 152326515056554713423540311)
  ·
    refine ⟨228489772584832070135310467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152326515056554713423540311 228489772584832070135310467)
    ·
      refine ⟨342734658877248105202965701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228489772584832070135310467 342734658877248105202965701)
      ·
        refine ⟨64262748539484019725556069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342734658877248105202965701 64262748539484019725556069)
        ·
          refine ⟨12049265351153253698541763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64262748539484019725556069 12049265351153253698541763)
          ·
            refine ⟨18073898026729880547812645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12049265351153253698541763 18073898026729880547812645)
            ·
              refine ⟨3388855880011852602714871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18073898026729880547812645 3388855880011852602714871)
              ·
                refine ⟨5083283820017778904072307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388855880011852602714871 5083283820017778904072307)
                ·
                  refine ⟨7624925730026668356108461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083283820017778904072307 7624925730026668356108461)
                  ·
                    refine ⟨2859347148760000633540673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7624925730026668356108461 2859347148760000633540673)
                    ·
                      refine ⟨2144510361570000475155505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859347148760000633540673 2144510361570000475155505)
                      ·
                        rfl

theorem cell23_4176419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_4176419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176419 prefixEnd_4176419 := by exact prefixLift 4176419
  have htrace : WordTrace (prefixWord ++ tailWord_4176419) baseStart_4176419 baseEnd_4176419 := by
    simpa [prefixWord, tailWord_4176419, baseEnd_4176419] using wordTrace_append hprefix tailTrace_4176419
  have hstable : (prefixWord ++ tailWord_4176419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176419).length < 2 ^ (prefixWord ++ tailWord_4176419).sum := by decide
  have hdescent : baseEnd_4176419 < baseStart_4176419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176445 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4176445 : Nat := 118140960795 + 4176445 * 2 ^ 59
def prefixEnd_4176445 : Nat := 4983230072969 + 3 ^ 40 * 4176445 * 2
def baseEnd_4176445 : Nat := 2144523712067017373430385

theorem tailTrace_4176445 : CollatzResearch.WordTrace tailWord_4176445 prefixEnd_4176445 2144523712067017373430385 := by
  unfold tailWord_4176445
  simp only [CollatzResearch.WordTrace]
  refine ⟨152327463354460519863986789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101551642236307013242657859 152327463354460519863986789)
  ·
    refine ⟨28561399378961347474497523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152327463354460519863986789 28561399378961347474497523)
    ·
      refine ⟨42842099068442021211746285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28561399378961347474497523 42842099068442021211746285)
      ·
        refine ⟨16065787150665757954404857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42842099068442021211746285 16065787150665757954404857)
        ·
          refine ⟨12049340362999318465803643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16065787150665757954404857 12049340362999318465803643)
          ·
            refine ⟨18074010544498977698705465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12049340362999318465803643 18074010544498977698705465)
            ·
              refine ⟨13555507908374233274029099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18074010544498977698705465 13555507908374233274029099)
              ·
                refine ⟨20333261862561349911043649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555507908374233274029099 20333261862561349911043649)
                ·
                  refine ⟨15249946396921012433282737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20333261862561349911043649 15249946396921012433282737)
                  ·
                    refine ⟨11437459797690759324962053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15249946396921012433282737 11437459797690759324962053)
                    ·
                      refine ⟨2144523712067017373430385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11437459797690759324962053 2144523712067017373430385)
                      ·
                        rfl

theorem cell23_4176445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4176445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176445 prefixEnd_4176445 := by exact prefixLift 4176445
  have htrace : WordTrace (prefixWord ++ tailWord_4176445) baseStart_4176445 baseEnd_4176445 := by
    simpa [prefixWord, tailWord_4176445, baseEnd_4176445] using wordTrace_append hprefix tailTrace_4176445
  have hstable : (prefixWord ++ tailWord_4176445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176445).length < 2 ^ (prefixWord ++ tailWord_4176445).sum := by decide
  have hdescent : baseEnd_4176445 < baseStart_4176445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176449 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4176449 : Nat := 118140960795 + 4176449 * 2 ^ 59
def prefixEnd_4176449 : Nat := 4983230072969 + 3 ^ 40 * 4176449 * 2
def baseEnd_4176449 : Nat := 2144525765989635357780367

theorem tailTrace_4176449 : CollatzResearch.WordTrace tailWord_4176449 prefixEnd_4176449 2144525765989635357780367 := by
  unfold tailWord_4176449
  simp only [CollatzResearch.WordTrace]
  refine ⟨152327609246446028547132401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101551739497630685698088267 152327609246446028547132401)
  ·
    refine ⟨114245706934834521410349301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152327609246446028547132401 114245706934834521410349301)
    ·
      refine ⟨10710535025140736382220247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114245706934834521410349301 10710535025140736382220247)
      ·
        refine ⟨16065802537711104573330371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710535025140736382220247 16065802537711104573330371)
        ·
          refine ⟨24098703806566656859995557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065802537711104573330371 24098703806566656859995557)
          ·
            refine ⟨4518506963731248161249167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24098703806566656859995557 4518506963731248161249167)
            ·
              refine ⟨6777760445596872241873751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518506963731248161249167 6777760445596872241873751)
              ·
                refine ⟨10166640668395308362810627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777760445596872241873751 10166640668395308362810627)
                ·
                  refine ⟨15249961002592962544215941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166640668395308362810627 15249961002592962544215941)
                  ·
                    refine ⟨2859367687986180477040489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15249961002592962544215941 2859367687986180477040489)
                    ·
                      refine ⟨2144525765989635357780367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859367687986180477040489 2144525765989635357780367)
                      ·
                        rfl

theorem cell23_4176449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4176449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176449 prefixEnd_4176449 := by exact prefixLift 4176449
  have htrace : WordTrace (prefixWord ++ tailWord_4176449) baseStart_4176449 baseEnd_4176449 := by
    simpa [prefixWord, tailWord_4176449, baseEnd_4176449] using wordTrace_append hprefix tailTrace_4176449
  have hstable : (prefixWord ++ tailWord_4176449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176449).length < 2 ^ (prefixWord ++ tailWord_4176449).sum := by decide
  have hdescent : baseEnd_4176449 < baseStart_4176449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176515 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 3, 4]
def baseStart_4176515 : Nat := 118140960795 + 4176515 * 2 ^ 59
def prefixEnd_4176515 : Nat := 4983230072969 + 3 ^ 40 * 4176515 * 2
def baseEnd_4176515 : Nat := 714853218570944033185021

theorem tailTrace_4176515 : CollatzResearch.WordTrace tailWord_4176515 prefixEnd_4176515 714853218570944033185021 := by
  unfold tailWord_4176515
  simp only [CollatzResearch.WordTrace]
  refine ⟨152330016464206921819034999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101553344309471281212689999 152330016464206921819034999)
  ·
    refine ⟨228495024696310382728552499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152330016464206921819034999 228495024696310382728552499)
    ·
      refine ⟨342742537044465574092828749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228495024696310382728552499 342742537044465574092828749)
      ·
        refine ⟨128528451391674590284810781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342742537044465574092828749 128528451391674590284810781)
        ·
          refine ⟨48198169271877971356804043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128528451391674590284810781 48198169271877971356804043)
          ·
            refine ⟨72297253907816957035206065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48198169271877971356804043 72297253907816957035206065)
            ·
              refine ⟨54222940430862717776404549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72297253907816957035206065 54222940430862717776404549)
              ·
                refine ⟨10166801330786759583075853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54222940430862717776404549 10166801330786759583075853)
                ·
                  refine ⟨3812550499045034843653445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10166801330786759583075853 3812550499045034843653445)
                  ·
                    refine ⟨714853218570944033185021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3812550499045034843653445 714853218570944033185021)
                    ·
                      rfl

theorem cell23_4176515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 4].length) (baseStart_4176515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176515 prefixEnd_4176515 := by exact prefixLift 4176515
  have htrace : WordTrace (prefixWord ++ tailWord_4176515) baseStart_4176515 baseEnd_4176515 := by
    simpa [prefixWord, tailWord_4176515, baseEnd_4176515] using wordTrace_append hprefix tailTrace_4176515
  have hstable : (prefixWord ++ tailWord_4176515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176515).length < 2 ^ (prefixWord ++ tailWord_4176515).sum := by decide
  have hdescent : baseEnd_4176515 < baseStart_4176515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176566 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4176566 : Nat := 118140960795 + 4176566 * 2 ^ 59
def prefixEnd_4176566 : Nat := 4983230072969 + 3 ^ 40 * 4176566 * 2
def baseEnd_4176566 : Nat := 714861947742070466672443

theorem tailTrace_4176566 : CollatzResearch.WordTrace tailWord_4176566 prefixEnd_4176566 714861947742070466672443 := by
  unfold tailWord_4176566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520742286688884845571347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101554584391348105019427701 9520742286688884845571347)
  ·
    refine ⟨14281113430033327268357021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520742286688884845571347 14281113430033327268357021)
    ·
      refine ⟨5355417536262497725633883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14281113430033327268357021 5355417536262497725633883)
      ·
        refine ⟨8033126304393746588450825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355417536262497725633883 8033126304393746588450825)
        ·
          refine ⟨6024844728295309941338119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8033126304393746588450825 6024844728295309941338119)
          ·
            refine ⟨9037267092442964912007179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024844728295309941338119 9037267092442964912007179)
            ·
              refine ⟨13555900638664447368010769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037267092442964912007179 13555900638664447368010769)
              ·
                refine ⟨10166925478998335526008077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13555900638664447368010769 10166925478998335526008077)
                ·
                  refine ⟨3812597054624375822253029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10166925478998335526008077 3812597054624375822253029)
                  ·
                    refine ⟨714861947742070466672443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3812597054624375822253029 714861947742070466672443)
                    ·
                      rfl

theorem cell23_4176566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4176566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176566 prefixEnd_4176566 := by exact prefixLift 4176566
  have htrace : WordTrace (prefixWord ++ tailWord_4176566) baseStart_4176566 baseEnd_4176566 := by
    simpa [prefixWord, tailWord_4176566, baseEnd_4176566] using wordTrace_append hprefix tailTrace_4176566
  have hstable : (prefixWord ++ tailWord_4176566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176566).length < 2 ^ (prefixWord ++ tailWord_4176566).sum := by decide
  have hdescent : baseEnd_4176566 < baseStart_4176566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176575 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 3, 5]
def baseStart_4176575 : Nat := 118140960795 + 4176575 * 2 ^ 59
def prefixEnd_4176575 : Nat := 4983230072969 + 3 ^ 40 * 4176575 * 2
def baseEnd_4176575 : Nat := 714863488184033954934929

theorem tailTrace_4176575 : CollatzResearch.WordTrace tailWord_4176575 prefixEnd_4176575 714863488184033954934929 := by
  unfold tailWord_4176575
  simp only [CollatzResearch.WordTrace]
  refine ⟨152332204843989552066219179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101554803229326368044146119 152332204843989552066219179)
  ·
    refine ⟨228498307265984328099328769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152332204843989552066219179 228498307265984328099328769)
    ·
      refine ⟨171373730449488246074496577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228498307265984328099328769 171373730449488246074496577)
      ·
        refine ⟨128530297837116184555872433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171373730449488246074496577 128530297837116184555872433)
        ·
          refine ⟨96397723377837138416904325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128530297837116184555872433 96397723377837138416904325)
          ·
            refine ⟨18074573133344463453169561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96397723377837138416904325 18074573133344463453169561)
            ·
              refine ⟨13555929850008347589877171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18074573133344463453169561 13555929850008347589877171)
              ·
                refine ⟨20333894775012521384815757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555929850008347589877171 20333894775012521384815757)
                ·
                  refine ⟨7625210540629695519305909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20333894775012521384815757 7625210540629695519305909)
                  ·
                    refine ⟨714863488184033954934929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7625210540629695519305909 714863488184033954934929)
                    ·
                      rfl

theorem cell23_4176575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_4176575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176575 prefixEnd_4176575 := by exact prefixLift 4176575
  have htrace : WordTrace (prefixWord ++ tailWord_4176575) baseStart_4176575 baseEnd_4176575 := by
    simpa [prefixWord, tailWord_4176575, baseEnd_4176575] using wordTrace_append hprefix tailTrace_4176575
  have hstable : (prefixWord ++ tailWord_4176575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176575).length < 2 ^ (prefixWord ++ tailWord_4176575).sum := by decide
  have hdescent : baseEnd_4176575 < baseStart_4176575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176596 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 6]
def baseStart_4176596 : Nat := 118140960795 + 4176596 * 2 ^ 59
def prefixEnd_4176596 : Nat := 4983230072969 + 3 ^ 40 * 4176596 * 2
def baseEnd_4176596 : Nat := 238289027516205142515799

theorem tailTrace_4176596 : CollatzResearch.WordTrace tailWord_4176596 prefixEnd_4176596 238289027516205142515799 := by
  unfold tailWord_4176596
  simp only [CollatzResearch.WordTrace]
  refine ⟨76166485388456736326366821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101555313851275648435155761 76166485388456736326366821)
  ·
    refine ⟨14281216010335638061193779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76166485388456736326366821 14281216010335638061193779)
    ·
      refine ⟨21421824015503457091790669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14281216010335638061193779 21421824015503457091790669)
      ·
        refine ⟨8033184005813796409421501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21421824015503457091790669 8033184005813796409421501)
        ·
          refine ⟨3012444002180173653533063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8033184005813796409421501 3012444002180173653533063)
          ·
            refine ⟨4518666003270260480299595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012444002180173653533063 4518666003270260480299595)
            ·
              refine ⟨6777999004905390720449393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518666003270260480299595 6777999004905390720449393)
              ·
                refine ⟨5083499253679043040337045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6777999004905390720449393 5083499253679043040337045)
                ·
                  refine ⟨238289027516205142515799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5083499253679043040337045 238289027516205142515799)
                  ·
                    rfl

theorem cell23_4176596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_4176596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176596 prefixEnd_4176596 := by exact prefixLift 4176596
  have htrace : WordTrace (prefixWord ++ tailWord_4176596) baseStart_4176596 baseEnd_4176596 := by
    simpa [prefixWord, tailWord_4176596, baseEnd_4176596] using wordTrace_append hprefix tailTrace_4176596
  have hstable : (prefixWord ++ tailWord_4176596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176596).length < 2 ^ (prefixWord ++ tailWord_4176596).sum := by decide
  have hdescent : baseEnd_4176596 < baseStart_4176596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176622 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_4176622 : Nat := 118140960795 + 4176622 * 2 ^ 59
def prefixEnd_4176622 : Nat := 4983230072969 + 3 ^ 40 * 4176622 * 2
def baseEnd_4176622 : Nat := 714871532714287726972357

theorem tailTrace_4176622 : CollatzResearch.WordTrace tailWord_4176622 prefixEnd_4176622 714871532714287726972357 := by
  unfold tailWord_4176622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19041739884352409886647515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101555946049879519395453413 19041739884352409886647515)
  ·
    refine ⟨28562609826528614829971273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19041739884352409886647515 28562609826528614829971273)
    ·
      refine ⟨21421957369896461122478455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28562609826528614829971273 21421957369896461122478455)
      ·
        refine ⟨32132936054844691683717683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21421957369896461122478455 32132936054844691683717683)
        ·
          refine ⟨48199404082267037525576525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32132936054844691683717683 48199404082267037525576525)
          ·
            refine ⟨18074776530850139072091197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48199404082267037525576525 18074776530850139072091197)
            ·
              refine ⟨6778041199068802152034199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18074776530850139072091197 6778041199068802152034199)
              ·
                refine ⟨10167061798603203228051299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778041199068802152034199 10167061798603203228051299)
                ·
                  refine ⟨15250592697904804842076949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10167061798603203228051299 15250592697904804842076949)
                  ·
                    refine ⟨714871532714287726972357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15250592697904804842076949 714871532714287726972357)
                    ·
                      rfl

theorem cell23_4176622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_4176622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176622 prefixEnd_4176622 := by exact prefixLift 4176622
  have htrace : WordTrace (prefixWord ++ tailWord_4176622) baseStart_4176622 baseEnd_4176622 := by
    simpa [prefixWord, tailWord_4176622, baseEnd_4176622] using wordTrace_append hprefix tailTrace_4176622
  have hstable : (prefixWord ++ tailWord_4176622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176622).length < 2 ^ (prefixWord ++ tailWord_4176622).sum := by decide
  have hdescent : baseEnd_4176622 < baseStart_4176622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176625 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_4176625 : Nat := 118140960795 + 4176625 * 2 ^ 59
def prefixEnd_4176625 : Nat := 4983230072969 + 3 ^ 40 * 4176625 * 2
def baseEnd_4176625 : Nat := 2144616138584826669179557

theorem tailTrace_4176625 : CollatzResearch.WordTrace tailWord_4176625 prefixEnd_4176625 2144616138584826669179557 := by
  unfold tailWord_4176625
  simp only [CollatzResearch.WordTrace]
  refine ⟨152334028493808410605539329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101556018995872273737026219 152334028493808410605539329)
  ·
    refine ⟨114250521370356307954154497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152334028493808410605539329 114250521370356307954154497)
    ·
      refine ⟨85687891027767230965615873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114250521370356307954154497 85687891027767230965615873)
      ·
        refine ⟨64265918270825423224211905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85687891027767230965615873 64265918270825423224211905)
        ·
          refine ⟨48199438703119067418158929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64265918270825423224211905 48199438703119067418158929)
          ·
            refine ⟨36149579027339300563619197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48199438703119067418158929 36149579027339300563619197)
            ·
              refine ⟨13556092135252237711357199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36149579027339300563619197 13556092135252237711357199)
              ·
                refine ⟨20334138202878356567035799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13556092135252237711357199 20334138202878356567035799)
                ·
                  refine ⟨30501207304317534850553699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20334138202878356567035799 30501207304317534850553699)
                  ·
                    refine ⟨45751810956476302275830549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30501207304317534850553699 45751810956476302275830549)
                    ·
                      refine ⟨2144616138584826669179557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45751810956476302275830549 2144616138584826669179557)
                      ·
                        rfl

theorem cell23_4176625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_4176625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176625 prefixEnd_4176625 := by exact prefixLift 4176625
  have htrace : WordTrace (prefixWord ++ tailWord_4176625) baseStart_4176625 baseEnd_4176625 := by
    simpa [prefixWord, tailWord_4176625, baseEnd_4176625] using wordTrace_append hprefix tailTrace_4176625
  have hstable : (prefixWord ++ tailWord_4176625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176625).length < 2 ^ (prefixWord ++ tailWord_4176625).sum := by decide
  have hdescent : baseEnd_4176625 < baseStart_4176625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176663 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_4176663 : Nat := 118140960795 + 4176663 * 2 ^ 59
def prefixEnd_4176663 : Nat := 4983230072969 + 3 ^ 40 * 4176663 * 2
def baseEnd_4176663 : Nat := 2144635650849697520504383

theorem tailTrace_4176663 : CollatzResearch.WordTrace tailWord_4176663 prefixEnd_4176663 2144635650849697520504383 := by
  unfold tailWord_4176663
  simp only [CollatzResearch.WordTrace]
  refine ⟨152335414467670743095422643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101556942978447162063615095 152335414467670743095422643)
  ·
    refine ⟨228503121701506114643133965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152335414467670743095422643 228503121701506114643133965)
    ·
      refine ⟨85688670638064792991175237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228503121701506114643133965 85688670638064792991175237)
      ·
        refine ⟨16066625744637148685845357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85688670638064792991175237 16066625744637148685845357)
        ·
          refine ⟨6024984654238930757192009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16066625744637148685845357 6024984654238930757192009)
          ·
            refine ⟨4518738490679198067894007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6024984654238930757192009 4518738490679198067894007)
            ·
              refine ⟨6778107736018797101841011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518738490679198067894007 6778107736018797101841011)
              ·
                refine ⟨10167161604028195652761517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778107736018797101841011 10167161604028195652761517)
                ·
                  refine ⟨3812685601510573369785569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10167161604028195652761517 3812685601510573369785569)
                  ·
                    refine ⟨2859514201132930027339177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812685601510573369785569 2859514201132930027339177)
                    ·
                      refine ⟨2144635650849697520504383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859514201132930027339177 2144635650849697520504383)
                      ·
                        rfl

theorem cell23_4176663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_4176663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176663 prefixEnd_4176663 := by exact prefixLift 4176663
  have htrace : WordTrace (prefixWord ++ tailWord_4176663) baseStart_4176663 baseEnd_4176663 := by
    simpa [prefixWord, tailWord_4176663, baseEnd_4176663] using wordTrace_append hprefix tailTrace_4176663
  have hstable : (prefixWord ++ tailWord_4176663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176663).length < 2 ^ (prefixWord ++ tailWord_4176663).sum := by decide
  have hdescent : baseEnd_4176663 < baseStart_4176663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176669 : List Nat := [1, 4, 2, 4, 1, 1, 2, 8]
def baseStart_4176669 : Nat := 118140960795 + 4176669 * 2 ^ 59
def prefixEnd_4176669 : Nat := 4983230072969 + 3 ^ 40 * 4176669 * 2
def baseEnd_4176669 : Nat := 79431064138282388778865

theorem tailTrace_4176669 : CollatzResearch.WordTrace tailWord_4176669 prefixEnd_4176669 79431064138282388778865 := by
  unfold tailWord_4176669
  simp only [CollatzResearch.WordTrace]
  refine ⟨152335633305649006120141061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101557088870432670746760707 152335633305649006120141061)
  ·
    refine ⟨28562931244809188647526449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152335633305649006120141061 28562931244809188647526449)
    ·
      refine ⟨21422198433606891485644837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28562931244809188647526449 21422198433606891485644837)
      ·
        refine ⟨4016662206301292153558407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21422198433606891485644837 4016662206301292153558407)
        ·
          refine ⟨6024993309451938230337611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016662206301292153558407 6024993309451938230337611)
          ·
            refine ⟨9037489964177907345506417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024993309451938230337611 9037489964177907345506417)
            ·
              refine ⟨6778117473133430509129813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9037489964177907345506417 6778117473133430509129813)
              ·
                refine ⟨79431064138282388778865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6778117473133430509129813 79431064138282388778865)
                ·
                  rfl

theorem cell23_4176669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 8].length) (baseStart_4176669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176669 prefixEnd_4176669 := by exact prefixLift 4176669
  have htrace : WordTrace (prefixWord ++ tailWord_4176669) baseStart_4176669 baseEnd_4176669 := by
    simpa [prefixWord, tailWord_4176669, baseEnd_4176669] using wordTrace_append hprefix tailTrace_4176669
  have hstable : (prefixWord ++ tailWord_4176669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176669).length < 2 ^ (prefixWord ++ tailWord_4176669).sum := by decide
  have hdescent : baseEnd_4176669 < baseStart_4176669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176689 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_4176689 : Nat := 118140960795 + 4176689 * 2 ^ 59
def prefixEnd_4176689 : Nat := 4983230072969 + 3 ^ 40 * 4176689 * 2
def baseEnd_4176689 : Nat := 2144649001346714418779263

theorem tailTrace_4176689 : CollatzResearch.WordTrace tailWord_4176689 prefixEnd_4176689 2144649001346714418779263 := by
  unfold tailWord_4176689
  simp only [CollatzResearch.WordTrace]
  refine ⟨152336362765576549535869121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101557575177051033023912747 152336362765576549535869121)
  ·
    refine ⟨114252272074182412151901841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152336362765576549535869121 114252272074182412151901841)
    ·
      refine ⟨85689204055636809113926381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114252272074182412151901841 85689204055636809113926381)
      ·
        refine ⟨32133451520863803417722393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85689204055636809113926381 32133451520863803417722393)
        ·
          refine ⟨24100088640647852563291795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32133451520863803417722393 24100088640647852563291795)
          ·
            refine ⟨36150132960971778844937693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24100088640647852563291795 36150132960971778844937693)
            ·
              refine ⟨13556299860364417066851635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36150132960971778844937693 13556299860364417066851635)
              ·
                refine ⟨20334449790546625600277453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13556299860364417066851635 20334449790546625600277453)
                ·
                  refine ⟨7625418671454984600104045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20334449790546625600277453 7625418671454984600104045)
                  ·
                    refine ⟨2859532001795619225039017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7625418671454984600104045 2859532001795619225039017)
                    ·
                      refine ⟨2144649001346714418779263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859532001795619225039017 2144649001346714418779263)
                      ·
                        rfl

theorem cell23_4176689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_4176689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176689 prefixEnd_4176689 := by exact prefixLift 4176689
  have htrace : WordTrace (prefixWord ++ tailWord_4176689) baseStart_4176689 baseEnd_4176689 := by
    simpa [prefixWord, tailWord_4176689, baseEnd_4176689] using wordTrace_append hprefix tailTrace_4176689
  have hstable : (prefixWord ++ tailWord_4176689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176689).length < 2 ^ (prefixWord ++ tailWord_4176689).sum := by decide
  have hdescent : baseEnd_4176689 < baseStart_4176689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176715 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_4176715 : Nat := 118140960795 + 4176715 * 2 ^ 59
def prefixEnd_4176715 : Nat := 4983230072969 + 3 ^ 40 * 4176715 * 2
def baseEnd_4176715 : Nat := 2144662351843731317054143

theorem tailTrace_4176715 : CollatzResearch.WordTrace tailWord_4176715 prefixEnd_4176715 2144662351843731317054143 := by
  unfold tailWord_4176715
  simp only [CollatzResearch.WordTrace]
  refine ⟨152337311063482355976315599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101558207375654903984210399 152337311063482355976315599)
  ·
    refine ⟨228505966595223533964473399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152337311063482355976315599 228505966595223533964473399)
    ·
      refine ⟨342758949892835300946710099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228505966595223533964473399 342758949892835300946710099)
      ·
        refine ⟨514138424839252951420065149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342758949892835300946710099 514138424839252951420065149)
        ·
          refine ⟨192801909314719856782524431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514138424839252951420065149 192801909314719856782524431)
          ·
            refine ⟨289202863972079785173786647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192801909314719856782524431 289202863972079785173786647)
            ·
              refine ⟨433804295958119677760679971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289202863972079785173786647 433804295958119677760679971)
              ·
                refine ⟨650706443937179516641019957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433804295958119677760679971 650706443937179516641019957)
                ·
                  refine ⟨61003729119110579685095621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 650706443937179516641019957 61003729119110579685095621)
                  ·
                    refine ⟨11438199209833233690955429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61003729119110579685095621 11438199209833233690955429)
                    ·
                      refine ⟨2144662351843731317054143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11438199209833233690955429 2144662351843731317054143)
                      ·
                        rfl

theorem cell23_4176715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_4176715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176715 prefixEnd_4176715 := by exact prefixLift 4176715
  have htrace : WordTrace (prefixWord ++ tailWord_4176715) baseStart_4176715 baseEnd_4176715 := by
    simpa [prefixWord, tailWord_4176715, baseEnd_4176715] using wordTrace_append hprefix tailTrace_4176715
  have hstable : (prefixWord ++ tailWord_4176715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176715).length < 2 ^ (prefixWord ++ tailWord_4176715).sum := by decide
  have hdescent : baseEnd_4176715 < baseStart_4176715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176722 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_4176722 : Nat := 118140960795 + 4176722 * 2 ^ 59
def prefixEnd_4176722 : Nat := 4983230072969 + 3 ^ 40 * 4176722 * 2
def baseEnd_4176722 : Nat := 2144665946208312789666611

theorem tailTrace_4176722 : CollatzResearch.WordTrace tailWord_4176722 prefixEnd_4176722 2144665946208312789666611 := by
  unfold tailWord_4176722
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084391593614249042955105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101558377582971330781213613 38084391593614249042955105)
  ·
    refine ⟨28563293695210686782216329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38084391593614249042955105 28563293695210686782216329)
    ·
      refine ⟨21422470271408015086662247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28563293695210686782216329 21422470271408015086662247)
      ·
        refine ⟨32133705407112022629993371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422470271408015086662247 32133705407112022629993371)
        ·
          refine ⟨48200558110668033944990057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32133705407112022629993371 48200558110668033944990057)
          ·
            refine ⟨36150418583001025458742543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48200558110668033944990057 36150418583001025458742543)
            ·
              refine ⟨54225627874501538188113815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36150418583001025458742543 54225627874501538188113815)
              ·
                refine ⟨81338441811752307282170723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54225627874501538188113815 81338441811752307282170723)
                ·
                  refine ⟨122007662717628460923256085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81338441811752307282170723 122007662717628460923256085)
                  ·
                    refine ⟨5719109189888834105777629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122007662717628460923256085 5719109189888834105777629)
                    ·
                      refine ⟨2144665946208312789666611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719109189888834105777629 2144665946208312789666611)
                      ·
                        rfl

theorem cell23_4176722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_4176722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176722 prefixEnd_4176722 := by exact prefixLift 4176722
  have htrace : WordTrace (prefixWord ++ tailWord_4176722) baseStart_4176722 baseEnd_4176722 := by
    simpa [prefixWord, tailWord_4176722, baseEnd_4176722] using wordTrace_append hprefix tailTrace_4176722
  have hstable : (prefixWord ++ tailWord_4176722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176722).length < 2 ^ (prefixWord ++ tailWord_4176722).sum := by decide
  have hdescent : baseEnd_4176722 < baseStart_4176722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176736 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2]
def baseStart_4176736 : Nat := 118140960795 + 4176736 * 2 ^ 59
def prefixEnd_4176736 : Nat := 4983230072969 + 3 ^ 40 * 4176736 * 2
def baseEnd_4176736 : Nat := 2144673134937475734891547

theorem tailTrace_4176736 : CollatzResearch.WordTrace tailWord_4176736 prefixEnd_4176736 2144673134937475734891547 := by
  unfold tailWord_4176736
  simp only [CollatzResearch.WordTrace]
  refine ⟨76169038498203138281415031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101558717997604184375220041 76169038498203138281415031)
  ·
    refine ⟨114253557747304707422122547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76169038498203138281415031 114253557747304707422122547)
    ·
      refine ⟨171380336620957061133183821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114253557747304707422122547 171380336620957061133183821)
      ·
        refine ⟨64267626232858897924943933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171380336620957061133183821 64267626232858897924943933)
        ·
          refine ⟨24100359837322086721853975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64267626232858897924943933 24100359837322086721853975)
          ·
            refine ⟨36150539755983130082780963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24100359837322086721853975 36150539755983130082780963)
            ·
              refine ⟨54225809633974695124171445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36150539755983130082780963 54225809633974695124171445)
              ·
                refine ⟨5083669653185127667891073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54225809633974695124171445 5083669653185127667891073)
                ·
                  refine ⟨3812752239888845750918305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083669653185127667891073 3812752239888845750918305)
                  ·
                    refine ⟨2859564179916634313188729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812752239888845750918305 2859564179916634313188729)
                    ·
                      refine ⟨2144673134937475734891547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859564179916634313188729 2144673134937475734891547)
                      ·
                        rfl

theorem cell23_4176736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_4176736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176736 prefixEnd_4176736 := by exact prefixLift 4176736
  have htrace : WordTrace (prefixWord ++ tailWord_4176736) baseStart_4176736 baseEnd_4176736 := by
    simpa [prefixWord, tailWord_4176736, baseEnd_4176736] using wordTrace_append hprefix tailTrace_4176736
  have hstable : (prefixWord ++ tailWord_4176736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176736).length < 2 ^ (prefixWord ++ tailWord_4176736).sum := by decide
  have hdescent : baseEnd_4176736 < baseStart_4176736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176772 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_4176772 : Nat := 118140960795 + 4176772 * 2 ^ 59
def prefixEnd_4176772 : Nat := 4983230072969 + 3 ^ 40 * 4176772 * 2
def baseEnd_4176772 : Nat := 714897206747012531347127

theorem tailTrace_4176772 : CollatzResearch.WordTrace tailWord_4176772 prefixEnd_4176772 714897206747012531347127 := by
  unfold tailWord_4176772
  simp only [CollatzResearch.WordTrace]
  refine ⟨76169695012137927355570285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101559593349517236474093713 76169695012137927355570285)
  ·
    refine ⟨28563635629551722758338857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76169695012137927355570285 28563635629551722758338857)
    ·
      refine ⟨21422726722163792068754143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28563635629551722758338857 21422726722163792068754143)
      ·
        refine ⟨32134090083245688103131215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422726722163792068754143 32134090083245688103131215)
        ·
          refine ⟨48201135124868532154696823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32134090083245688103131215 48201135124868532154696823)
          ·
            refine ⟨72301702687302798232045235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48201135124868532154696823 72301702687302798232045235)
            ·
              refine ⟨108452554030954197348067853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72301702687302798232045235 108452554030954197348067853)
              ·
                refine ⟨40669707761607824005525445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108452554030954197348067853 40669707761607824005525445)
                ·
                  refine ⟨7625570205301467001036021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40669707761607824005525445 7625570205301467001036021)
                  ·
                    refine ⟨714897206747012531347127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7625570205301467001036021 714897206747012531347127)
                    ·
                      rfl

theorem cell23_4176772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_4176772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176772 prefixEnd_4176772 := by exact prefixLift 4176772
  have htrace : WordTrace (prefixWord ++ tailWord_4176772) baseStart_4176772 baseEnd_4176772 := by
    simpa [prefixWord, tailWord_4176772, baseEnd_4176772] using wordTrace_append hprefix tailTrace_4176772
  have hstable : (prefixWord ++ tailWord_4176772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176772).length < 2 ^ (prefixWord ++ tailWord_4176772).sum := by decide
  have hdescent : baseEnd_4176772 < baseStart_4176772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176832 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 8]
def baseStart_4176832 : Nat := 118140960795 + 4176832 * 2 ^ 59
def prefixEnd_4176832 : Nat := 4983230072969 + 3 ^ 40 * 4176832 * 2
def baseEnd_4176832 : Nat := 238302492120034151032345

theorem tailTrace_4176832 : CollatzResearch.WordTrace tailWord_4176832 prefixEnd_4176832 238302492120034151032345 := by
  unfold tailWord_4176832
  simp only [CollatzResearch.WordTrace]
  refine ⟨76170789202029242479162375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101561052269372323305549833 76170789202029242479162375)
  ·
    refine ⟨114256183803043863718743563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76170789202029242479162375 114256183803043863718743563)
    ·
      refine ⟨171384275704565795578115345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114256183803043863718743563 171384275704565795578115345)
      ·
        refine ⟨128538206778424346683586509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171384275704565795578115345 128538206778424346683586509)
        ·
          refine ⟨48201827541909130006344941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128538206778424346683586509 48201827541909130006344941)
          ·
            refine ⟨18075685328215923752379353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48201827541909130006344941 18075685328215923752379353)
            ·
              refine ⟨13556763996161942814284515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18075685328215923752379353 13556763996161942814284515)
              ·
                refine ⟨20335145994242914221426773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13556763996161942814284515 20335145994242914221426773)
                ·
                  refine ⟨238302492120034151032345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20335145994242914221426773 238302492120034151032345)
                  ·
                    rfl

theorem cell23_4176832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_4176832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176832 prefixEnd_4176832 := by exact prefixLift 4176832
  have htrace : WordTrace (prefixWord ++ tailWord_4176832) baseStart_4176832 baseEnd_4176832 := by
    simpa [prefixWord, tailWord_4176832, baseEnd_4176832] using wordTrace_append hprefix tailTrace_4176832
  have hstable : (prefixWord ++ tailWord_4176832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176832).length < 2 ^ (prefixWord ++ tailWord_4176832).sum := by decide
  have hdescent : baseEnd_4176832 < baseStart_4176832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176838 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4176838 : Nat := 118140960795 + 4176838 * 2 ^ 59
def prefixEnd_4176838 : Nat := 4983230072969 + 3 ^ 40 * 4176838 * 2
def baseEnd_4176838 : Nat := 2144725509964234335816079

theorem tailTrace_4176838 : CollatzResearch.WordTrace tailWord_4176838 prefixEnd_4176838 2144725509964234335816079 := by
  unfold tailWord_4176838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760681163813648374470099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101561198161357831988695445 4760681163813648374470099)
  ·
    refine ⟨7141021745720472561705149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4760681163813648374470099 7141021745720472561705149)
    ·
      refine ⟨2677883154645177210639431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7141021745720472561705149 2677883154645177210639431)
      ·
        refine ⟨4016824731967765815959147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677883154645177210639431 4016824731967765815959147)
        ·
          refine ⟨6025237097951648723938721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016824731967765815959147 6025237097951648723938721)
          ·
            refine ⟨4518927823463736542954041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6025237097951648723938721 4518927823463736542954041)
            ·
              refine ⟨3389195867597802407215531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518927823463736542954041 3389195867597802407215531)
              ·
                refine ⟨5083793801396703610823297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389195867597802407215531 5083793801396703610823297)
                ·
                  refine ⟨3812845351047527708117473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083793801396703610823297 3812845351047527708117473)
                  ·
                    refine ⟨2859634013285645781088105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812845351047527708117473 2859634013285645781088105)
                    ·
                      refine ⟨2144725509964234335816079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859634013285645781088105 2144725509964234335816079)
                      ·
                        rfl

theorem cell23_4176838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4176838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176838 prefixEnd_4176838 := by exact prefixLift 4176838
  have htrace : WordTrace (prefixWord ++ tailWord_4176838) baseStart_4176838 baseEnd_4176838 := by
    simpa [prefixWord, tailWord_4176838, baseEnd_4176838] using wordTrace_append hprefix tailTrace_4176838
  have hstable : (prefixWord ++ tailWord_4176838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176838).length < 2 ^ (prefixWord ++ tailWord_4176838).sum := by decide
  have hdescent : baseEnd_4176838 < baseStart_4176838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176899 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 6, 2]
def baseStart_4176899 : Nat := 118140960795 + 4176899 * 2 ^ 59
def prefixEnd_4176899 : Nat := 4983230072969 + 3 ^ 40 * 4176899 * 2
def baseEnd_4176899 : Nat := 2144756832284158597153297

theorem tailTrace_4176899 : CollatzResearch.WordTrace tailWord_4176899 prefixEnd_4176899 2144756832284158597153297 := by
  unfold tailWord_4176899
  simp only [CollatzResearch.WordTrace]
  refine ⟨152344022094815755401013751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101562681396543836934009167 152344022094815755401013751)
  ·
    refine ⟨228516033142223633101520627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152344022094815755401013751 228516033142223633101520627)
    ·
      refine ⟨342774049713335449652280941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228516033142223633101520627 342774049713335449652280941)
      ·
        refine ⟨128540268642500793619605353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342774049713335449652280941 128540268642500793619605353)
        ·
          refine ⟨96405201481875595214704015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128540268642500793619605353 96405201481875595214704015)
          ·
            refine ⟨144607802222813392822056023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96405201481875595214704015 144607802222813392822056023)
            ·
              refine ⟨216911703334220089233084035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144607802222813392822056023 216911703334220089233084035)
              ·
                refine ⟨325367555001330133849626053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216911703334220089233084035 325367555001330133849626053)
                ·
                  refine ⟨61006416562749400096804885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325367555001330133849626053 61006416562749400096804885)
                  ·
                    refine ⟨2859675776378878129537729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61006416562749400096804885 2859675776378878129537729)
                    ·
                      refine ⟨2144756832284158597153297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859675776378878129537729 2144756832284158597153297)
                      ·
                        rfl

theorem cell23_4176899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_4176899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176899 prefixEnd_4176899 := by exact prefixLift 4176899
  have htrace : WordTrace (prefixWord ++ tailWord_4176899) baseStart_4176899 baseEnd_4176899 := by
    simpa [prefixWord, tailWord_4176899, baseEnd_4176899] using wordTrace_append hprefix tailTrace_4176899
  have hstable : (prefixWord ++ tailWord_4176899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176899).length < 2 ^ (prefixWord ++ tailWord_4176899).sum := by decide
  have hdescent : baseEnd_4176899 < baseStart_4176899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176914 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4176914 : Nat := 118140960795 + 4176914 * 2 ^ 59
def prefixEnd_4176914 : Nat := 4983230072969 + 3 ^ 40 * 4176914 * 2
def baseEnd_4176914 : Nat := 2144764534493976038465729

theorem tailTrace_4176914 : CollatzResearch.WordTrace tailWord_4176914 prefixEnd_4176914 2144764534493976038465729 := by
  unfold tailWord_4176914
  simp only [CollatzResearch.WordTrace]
  refine ⟨38086142297440353240702449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101563046126507608641873197 38086142297440353240702449)
  ·
    refine ⟨28564606723080264930526837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38086142297440353240702449 28564606723080264930526837)
    ·
      refine ⟨2677931880288774837236891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28564606723080264930526837 2677931880288774837236891)
      ·
        refine ⟨4016897820433162255855337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677931880288774837236891 4016897820433162255855337)
        ·
          refine ⟨3012673365324871691891503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016897820433162255855337 3012673365324871691891503)
          ·
            refine ⟨4519010047987307537837255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012673365324871691891503 4519010047987307537837255)
            ·
              refine ⟨6778515071980961306755883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519010047987307537837255 6778515071980961306755883)
              ·
                refine ⟨10167772607971441960133825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778515071980961306755883 10167772607971441960133825)
                ·
                  refine ⟨7625829455978581470100369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10167772607971441960133825 7625829455978581470100369)
                  ·
                    refine ⟨5719372091983936102575277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7625829455978581470100369 5719372091983936102575277)
                    ·
                      refine ⟨2144764534493976038465729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719372091983936102575277 2144764534493976038465729)
                      ·
                        rfl

theorem cell23_4176914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4176914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176914 prefixEnd_4176914 := by exact prefixLift 4176914
  have htrace : WordTrace (prefixWord ++ tailWord_4176914) baseStart_4176914 baseEnd_4176914 := by
    simpa [prefixWord, tailWord_4176914, baseEnd_4176914] using wordTrace_append hprefix tailTrace_4176914
  have hstable : (prefixWord ++ tailWord_4176914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176914).length < 2 ^ (prefixWord ++ tailWord_4176914).sum := by decide
  have hdescent : baseEnd_4176914 < baseStart_4176914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176950 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4176950 : Nat := 118140960795 + 4176950 * 2 ^ 59
def prefixEnd_4176950 : Nat := 4983230072969 + 3 ^ 40 * 4176950 * 2
def baseEnd_4176950 : Nat := 2144783019797537897615563

theorem tailTrace_4176950 : CollatzResearch.WordTrace tailWord_4176950 prefixEnd_4176950 2144783019797537897615563 := by
  unfold tailWord_4176950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9521617638601936944445019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101563921478420660740746869 9521617638601936944445019)
  ·
    refine ⟨14282426457902905416667529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9521617638601936944445019 14282426457902905416667529)
    ·
      refine ⟨10711819843427179062500647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14282426457902905416667529 10711819843427179062500647)
      ·
        refine ⟨16067729765140768593750971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711819843427179062500647 16067729765140768593750971)
        ·
          refine ⟨24101594647711152890626457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067729765140768593750971 24101594647711152890626457)
          ·
            refine ⟨18076195985783364667969843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24101594647711152890626457 18076195985783364667969843)
            ·
              refine ⟨27114293978675047001954765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18076195985783364667969843 27114293978675047001954765)
              ·
                refine ⟨10167860242003142625733037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27114293978675047001954765 10167860242003142625733037)
                ·
                  refine ⟨3812947590751178484649889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10167860242003142625733037 3812947590751178484649889)
                  ·
                    refine ⟨2859710693063383863487417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812947590751178484649889 2859710693063383863487417)
                    ·
                      refine ⟨2144783019797537897615563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859710693063383863487417 2144783019797537897615563)
                      ·
                        rfl

theorem cell23_4176950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4176950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176950 prefixEnd_4176950 := by exact prefixLift 4176950
  have htrace : WordTrace (prefixWord ++ tailWord_4176950) baseStart_4176950 baseEnd_4176950 := by
    simpa [prefixWord, tailWord_4176950, baseEnd_4176950] using wordTrace_append hprefix tailTrace_4176950
  have hstable : (prefixWord ++ tailWord_4176950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176950).length < 2 ^ (prefixWord ++ tailWord_4176950).sum := by decide
  have hdescent : baseEnd_4176950 < baseStart_4176950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176973 : List Nat := [1, 6, 1, 1, 1, 4, 2, 7]
def baseStart_4176973 : Nat := 118140960795 + 4176973 * 2 ^ 59
def prefixEnd_4176973 : Nat := 4983230072969 + 3 ^ 40 * 4176973 * 2
def baseEnd_4176973 : Nat := 79436845550095974356591

theorem tailTrace_4176973 : CollatzResearch.WordTrace tailWord_4176973 prefixEnd_4176973 79436845550095974356591 := by
  unfold tailWord_4176973
  simp only [CollatzResearch.WordTrace]
  refine ⟨152346721096547666039207573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101564480731031777359471715 152346721096547666039207573)
  ·
    refine ⟨7141252551400671845587855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152346721096547666039207573 7141252551400671845587855)
    ·
      refine ⟨10711878827101007768381783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141252551400671845587855 10711878827101007768381783)
      ·
        refine ⟨16067818240651511652572675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711878827101007768381783 16067818240651511652572675)
        ·
          refine ⟨24101727360977267478859013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067818240651511652572675 24101727360977267478859013)
          ·
            refine ⟨4519073880183237652286065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24101727360977267478859013 4519073880183237652286065)
            ·
              refine ⟨3389305410137428239214549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4519073880183237652286065 3389305410137428239214549)
              ·
                refine ⟨79436845550095974356591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3389305410137428239214549 79436845550095974356591)
                ·
                  rfl

theorem cell23_4176973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 7].length) (baseStart_4176973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176973 prefixEnd_4176973 := by exact prefixLift 4176973
  have htrace : WordTrace (prefixWord ++ tailWord_4176973) baseStart_4176973 baseEnd_4176973 := by
    simpa [prefixWord, tailWord_4176973, baseEnd_4176973] using wordTrace_append hprefix tailTrace_4176973
  have hstable : (prefixWord ++ tailWord_4176973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176973).length < 2 ^ (prefixWord ++ tailWord_4176973).sum := by decide
  have hdescent : baseEnd_4176973 < baseStart_4176973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176976 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2]
def baseStart_4176976 : Nat := 118140960795 + 4176976 * 2 ^ 59
def prefixEnd_4176976 : Nat := 4983230072969 + 3 ^ 40 * 4176976 * 2
def baseEnd_4176976 : Nat := 2144796370294554795890443

theorem tailTrace_4176976 : CollatzResearch.WordTrace tailWord_4176976 prefixEnd_4176976 2144796370294554795890443 := by
  unfold tailWord_4176976
  simp only [CollatzResearch.WordTrace]
  refine ⟨76173415257768398775783391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101564553677024531701044521 76173415257768398775783391)
  ·
    refine ⟨114260122886652598163675087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76173415257768398775783391 114260122886652598163675087)
    ·
      refine ⟨171390184329978897245512631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114260122886652598163675087 171390184329978897245512631)
      ·
        refine ⟨257085276494968345868268947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171390184329978897245512631 257085276494968345868268947)
        ·
          refine ⟨385627914742452518802403421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257085276494968345868268947 385627914742452518802403421)
          ·
            refine ⟨144610468028419694550901283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385627914742452518802403421 144610468028419694550901283)
            ·
              refine ⟨216915702042629541826351925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144610468028419694550901283 216915702042629541826351925)
              ·
                refine ⟨20335847066496519546220493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216915702042629541826351925 20335847066496519546220493)
                ·
                  refine ⟨7625942649936194829832685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20335847066496519546220493 7625942649936194829832685)
                  ·
                    refine ⟨2859728493726073061187257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7625942649936194829832685 2859728493726073061187257)
                    ·
                      refine ⟨2144796370294554795890443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859728493726073061187257 2144796370294554795890443)
                      ·
                        rfl

theorem cell23_4176976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2].length) (baseStart_4176976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176976 prefixEnd_4176976 := by exact prefixLift 4176976
  have htrace : WordTrace (prefixWord ++ tailWord_4176976) baseStart_4176976 baseEnd_4176976 := by
    simpa [prefixWord, tailWord_4176976, baseEnd_4176976] using wordTrace_append hprefix tailTrace_4176976
  have hstable : (prefixWord ++ tailWord_4176976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176976).length < 2 ^ (prefixWord ++ tailWord_4176976).sum := by decide
  have hdescent : baseEnd_4176976 < baseStart_4176976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176993 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_4176993 : Nat := 118140960795 + 4176993 * 2 ^ 59
def prefixEnd_4176993 : Nat := 4983230072969 + 3 ^ 40 * 4176993 * 2
def baseEnd_4176993 : Nat := 2144805099465681229377865

theorem tailTrace_4176993 : CollatzResearch.WordTrace tailWord_4176993 prefixEnd_4176993 2144805099465681229377865 := by
  unfold tailWord_4176993
  simp only [CollatzResearch.WordTrace]
  refine ⟨152347450556475209454935633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101564967037650139636623755 152347450556475209454935633)
  ·
    refine ⟨114260587917356407091201725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152347450556475209454935633 114260587917356407091201725)
    ·
      refine ⟨42847720469008652659200647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114260587917356407091201725 42847720469008652659200647)
      ·
        refine ⟨64271580703512978988800971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42847720469008652659200647 64271580703512978988800971)
        ·
          refine ⟨96407371055269468483201457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64271580703512978988800971 96407371055269468483201457)
          ·
            refine ⟨72305528291452101362401093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96407371055269468483201457 72305528291452101362401093)
            ·
              refine ⟨13557286554647269005450205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72305528291452101362401093 13557286554647269005450205)
              ·
                refine ⟨5083982457992725877043827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13557286554647269005450205 5083982457992725877043827)
                ·
                  refine ⟨7625973686989088815565741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083982457992725877043827 7625973686989088815565741)
                  ·
                    refine ⟨2859740132620908305837153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7625973686989088815565741 2859740132620908305837153)
                    ·
                      refine ⟨2144805099465681229377865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859740132620908305837153 2144805099465681229377865)
                      ·
                        rfl

theorem cell23_4176993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_4176993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4176993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4176993 prefixEnd_4176993 := by exact prefixLift 4176993
  have htrace : WordTrace (prefixWord ++ tailWord_4176993) baseStart_4176993 baseEnd_4176993 := by
    simpa [prefixWord, tailWord_4176993, baseEnd_4176993] using wordTrace_append hprefix tailTrace_4176993
  have hstable : (prefixWord ++ tailWord_4176993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176993).length < 2 ^ (prefixWord ++ tailWord_4176993).sum := by decide
  have hdescent : baseEnd_4176993 < baseStart_4176993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177017 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 2, 1, 3]
def baseStart_4177017 : Nat := 118140960795 + 4177017 * 2 ^ 59
def prefixEnd_4177017 : Nat := 4983230072969 + 3 ^ 40 * 4177017 * 2
def baseEnd_4177017 : Nat := 2144817423001389135477755

theorem tailTrace_4177017 : CollatzResearch.WordTrace tailWord_4177017 prefixEnd_4177017 2144817423001389135477755 := by
  unfold tailWord_4177017
  simp only [CollatzResearch.WordTrace]
  refine ⟨152348325908388261553809305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101565550605592174369206203 152348325908388261553809305)
  ·
    refine ⟨114261244431291196165356979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152348325908388261553809305 114261244431291196165356979)
    ·
      refine ⟨171391866646936794248035469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114261244431291196165356979 171391866646936794248035469)
      ·
        refine ⟨64271949992601297843013301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171391866646936794248035469 64271949992601297843013301)
        ·
          refine ⟨6025495311806371672782497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64271949992601297843013301 6025495311806371672782497)
          ·
            refine ⟨4519121483854778754586873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6025495311806371672782497 4519121483854778754586873)
            ·
              refine ⟨3389341112891084065940155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4519121483854778754586873 3389341112891084065940155)
              ·
                refine ⟨5084011669336626098910233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389341112891084065940155 5084011669336626098910233)
                ·
                  refine ⟨3813008752002469574182675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084011669336626098910233 3813008752002469574182675)
                  ·
                    refine ⟨5719513128003704361274013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813008752002469574182675 5719513128003704361274013)
                    ·
                      refine ⟨2144817423001389135477755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719513128003704361274013 2144817423001389135477755)
                      ·
                        rfl

theorem cell23_4177017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_4177017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177017 prefixEnd_4177017 := by exact prefixLift 4177017
  have htrace : WordTrace (prefixWord ++ tailWord_4177017) baseStart_4177017 baseEnd_4177017 := by
    simpa [prefixWord, tailWord_4177017, baseEnd_4177017] using wordTrace_append hprefix tailTrace_4177017
  have hstable : (prefixWord ++ tailWord_4177017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177017).length < 2 ^ (prefixWord ++ tailWord_4177017).sum := by decide
  have hdescent : baseEnd_4177017 < baseStart_4177017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177019 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_4177019 : Nat := 118140960795 + 4177019 * 2 ^ 59
def prefixEnd_4177019 : Nat := 4983230072969 + 3 ^ 40 * 4177019 * 2
def baseEnd_4177019 : Nat := 2144818449962698127652745

theorem tailTrace_4177019 : CollatzResearch.WordTrace tailWord_4177019 prefixEnd_4177019 2144818449962698127652745 := by
  unfold tailWord_4177019
  simp only [CollatzResearch.WordTrace]
  refine ⟨152348398854381015895382111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101565599236254010596921407 152348398854381015895382111)
  ·
    refine ⟨228522598281571523843073167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152348398854381015895382111 228522598281571523843073167)
    ·
      refine ⟨342783897422357285764609751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228522598281571523843073167 342783897422357285764609751)
      ·
        refine ⟨514175846133535928646914627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342783897422357285764609751 514175846133535928646914627)
        ·
          refine ⟨771263769200303892970371941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514175846133535928646914627 771263769200303892970371941)
          ·
            refine ⟨144611956725056979931944739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 771263769200303892970371941 144611956725056979931944739)
            ·
              refine ⟨216917935087585469897917109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144611956725056979931944739 216917935087585469897917109)
              ·
                refine ⟨20336056414461137802929729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216917935087585469897917109 20336056414461137802929729)
                ·
                  refine ⟨15252042310845853352197297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20336056414461137802929729 15252042310845853352197297)
                  ·
                    refine ⟨11439031733134390014147973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15252042310845853352197297 11439031733134390014147973)
                    ·
                      refine ⟨2144818449962698127652745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11439031733134390014147973 2144818449962698127652745)
                      ·
                        rfl

theorem cell23_4177019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_4177019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177019 prefixEnd_4177019 := by exact prefixLift 4177019
  have htrace : WordTrace (prefixWord ++ tailWord_4177019) baseStart_4177019 baseEnd_4177019 := by
    simpa [prefixWord, tailWord_4177019, baseEnd_4177019] using wordTrace_append hprefix tailTrace_4177019
  have hstable : (prefixWord ++ tailWord_4177019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177019).length < 2 ^ (prefixWord ++ tailWord_4177019).sum := by decide
  have hdescent : baseEnd_4177019 < baseStart_4177019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177056 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_4177056 : Nat := 118140960795 + 4177056 * 2 ^ 59
def prefixEnd_4177056 : Nat := 4983230072969 + 3 ^ 40 * 4177056 * 2
def baseEnd_4177056 : Nat := 2144837448746914482890075

theorem tailTrace_4177056 : CollatzResearch.WordTrace tailWord_4177056 prefixEnd_4177056 2144837448746914482890075 := by
  unfold tailWord_4177056
  simp only [CollatzResearch.WordTrace]
  refine ⟨76174874177623485607239511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101566498903497980809652681 76174874177623485607239511)
  ·
    refine ⟨114262311266435228410859267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76174874177623485607239511 114262311266435228410859267)
    ·
      refine ⟨171393466899652842616288901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114262311266435228410859267 171393466899652842616288901)
      ·
        refine ⟨32136275043684907990554169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171393466899652842616288901 32136275043684907990554169)
        ·
          refine ⟨24102206282763680992915627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32136275043684907990554169 24102206282763680992915627)
          ·
            refine ⟨36153309424145521489373441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24102206282763680992915627 36153309424145521489373441)
            ·
              refine ⟨27114982068109141117030081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36153309424145521489373441 27114982068109141117030081)
              ·
                refine ⟨20336236551081855837772561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27114982068109141117030081 20336236551081855837772561)
                ·
                  refine ⟨15252177413311391878329421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20336236551081855837772561 15252177413311391878329421)
                  ·
                    refine ⟨5719566529991771954373533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15252177413311391878329421 5719566529991771954373533)
                    ·
                      refine ⟨2144837448746914482890075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719566529991771954373533 2144837448746914482890075)
                      ·
                        rfl

theorem cell23_4177056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_4177056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177056 prefixEnd_4177056 := by exact prefixLift 4177056
  have htrace : WordTrace (prefixWord ++ tailWord_4177056) baseStart_4177056 baseEnd_4177056 := by
    simpa [prefixWord, tailWord_4177056, baseEnd_4177056] using wordTrace_append hprefix tailTrace_4177056
  have hstable : (prefixWord ++ tailWord_4177056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177056).length < 2 ^ (prefixWord ++ tailWord_4177056).sum := by decide
  have hdescent : baseEnd_4177056 < baseStart_4177056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177073 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4177073 : Nat := 118140960795 + 4177073 * 2 ^ 59
def prefixEnd_4177073 : Nat := 4983230072969 + 3 ^ 40 * 4177073 * 2
def baseEnd_4177073 : Nat := 2144846177918040916377497

theorem tailTrace_4177073 : CollatzResearch.WordTrace tailWord_4177073 prefixEnd_4177073 2144846177918040916377497 := by
  unfold tailWord_4177073
  simp only [CollatzResearch.WordTrace]
  refine ⟨152350368396185383117847873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101566912264123588745231915 152350368396185383117847873)
  ·
    refine ⟨114262776297139037338385905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152350368396185383117847873 114262776297139037338385905)
    ·
      refine ⟨85697082222854278003789429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114262776297139037338385905 85697082222854278003789429)
      ·
        refine ⟨8034101458392588562855259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85697082222854278003789429 8034101458392588562855259)
        ·
          refine ⟨12051152187588882844282889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034101458392588562855259 12051152187588882844282889)
          ·
            refine ⟨9038364140691662133212167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12051152187588882844282889 9038364140691662133212167)
            ·
              refine ⟨13557546211037493199818251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038364140691662133212167 13557546211037493199818251)
              ·
                refine ⟨20336319316556239799727377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557546211037493199818251 20336319316556239799727377)
                ·
                  refine ⟨15252239487417179849795533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20336319316556239799727377 15252239487417179849795533)
                  ·
                    refine ⟨5719589807781442443673325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15252239487417179849795533 5719589807781442443673325)
                    ·
                      refine ⟨2144846177918040916377497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719589807781442443673325 2144846177918040916377497)
                      ·
                        rfl

theorem cell23_4177073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4177073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177073 prefixEnd_4177073 := by exact prefixLift 4177073
  have htrace : WordTrace (prefixWord ++ tailWord_4177073) baseStart_4177073 baseEnd_4177073 := by
    simpa [prefixWord, tailWord_4177073, baseEnd_4177073] using wordTrace_append hprefix tailTrace_4177073
  have hstable : (prefixWord ++ tailWord_4177073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177073).length < 2 ^ (prefixWord ++ tailWord_4177073).sum := by decide
  have hdescent : baseEnd_4177073 < baseStart_4177073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177099 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_4177099 : Nat := 118140960795 + 4177099 * 2 ^ 59
def prefixEnd_4177099 : Nat := 4983230072969 + 3 ^ 40 * 4177099 * 2
def baseEnd_4177099 : Nat := 2144859528415057814652377

theorem tailTrace_4177099 : CollatzResearch.WordTrace tailWord_4177099 prefixEnd_4177099 2144859528415057814652377 := by
  unfold tailWord_4177099
  simp only [CollatzResearch.WordTrace]
  refine ⟨152351316694091189558294351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101567544462727459705529567 152351316694091189558294351)
  ·
    refine ⟨228526975041136784337441527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152351316694091189558294351 228526975041136784337441527)
    ·
      refine ⟨342790462561705176506162291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228526975041136784337441527 342790462561705176506162291)
      ·
        refine ⟨514185693842557764759243437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342790462561705176506162291 514185693842557764759243437)
        ·
          refine ⟨192819635190959161784716289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514185693842557764759243437 192819635190959161784716289)
          ·
            refine ⟨144614726393219371338537217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192819635190959161784716289 144614726393219371338537217)
            ·
              refine ⟨108461044794914528503902913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144614726393219371338537217 108461044794914528503902913)
              ·
                refine ⟨81345783596185896377927185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108461044794914528503902913 81345783596185896377927185)
                ·
                  refine ⟨61009337697139422283445389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81345783596185896377927185 61009337697139422283445389)
                  ·
                    refine ⟨22878501636427283356292021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61009337697139422283445389 22878501636427283356292021)
                    ·
                      refine ⟨2144859528415057814652377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22878501636427283356292021 2144859528415057814652377)
                      ·
                        rfl

theorem cell23_4177099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_4177099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177099 prefixEnd_4177099 := by exact prefixLift 4177099
  have htrace : WordTrace (prefixWord ++ tailWord_4177099) baseStart_4177099 baseEnd_4177099 := by
    simpa [prefixWord, tailWord_4177099, baseEnd_4177099] using wordTrace_append hprefix tailTrace_4177099
  have hstable : (prefixWord ++ tailWord_4177099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177099).length < 2 ^ (prefixWord ++ tailWord_4177099).sum := by decide
  have hdescent : baseEnd_4177099 < baseStart_4177099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177133 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4177133 : Nat := 118140960795 + 4177133 * 2 ^ 59
def prefixEnd_4177133 : Nat := 4983230072969 + 3 ^ 40 * 4177133 * 2
def baseEnd_4177133 : Nat := 2144876986757310681627221

theorem tailTrace_4177133 : CollatzResearch.WordTrace tailWord_4177133 prefixEnd_4177133 2144876986757310681627221 := by
  unfold tailWord_4177133
  simp only [CollatzResearch.WordTrace]
  refine ⟨152352556775968013365032053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101568371183978675576688035 152352556775968013365032053)
  ·
    refine ⟨14283052197747001252971755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152352556775968013365032053 14283052197747001252971755)
    ·
      refine ⟨21424578296620501879457633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14283052197747001252971755 21424578296620501879457633)
      ·
        refine ⟨16068433722465376409593225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21424578296620501879457633 16068433722465376409593225)
        ·
          refine ⟨12051325291849032307194919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16068433722465376409593225 12051325291849032307194919)
          ·
            refine ⟨18076987937773548460792379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12051325291849032307194919 18076987937773548460792379)
            ·
              refine ⟨27115481906660322691188569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18076987937773548460792379 27115481906660322691188569)
              ·
                refine ⟨20336611429995242018391427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27115481906660322691188569 20336611429995242018391427)
                ·
                  refine ⟨30504917144992863027587141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20336611429995242018391427 30504917144992863027587141)
                  ·
                    refine ⟨5719671964686161817672589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30504917144992863027587141 5719671964686161817672589)
                    ·
                      refine ⟨2144876986757310681627221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719671964686161817672589 2144876986757310681627221)
                      ·
                        rfl

theorem cell23_4177133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4177133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177133 prefixEnd_4177133 := by exact prefixLift 4177133
  have htrace : WordTrace (prefixWord ++ tailWord_4177133) baseStart_4177133 baseEnd_4177133 := by
    simpa [prefixWord, tailWord_4177133, baseEnd_4177133] using wordTrace_append hprefix tailTrace_4177133
  have hstable : (prefixWord ++ tailWord_4177133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177133).length < 2 ^ (prefixWord ++ tailWord_4177133).sum := by decide
  have hdescent : baseEnd_4177133 < baseStart_4177133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177146 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_4177146 : Nat := 118140960795 + 4177146 * 2 ^ 59
def prefixEnd_4177146 : Nat := 4983230072969 + 3 ^ 40 * 4177146 * 2
def baseEnd_4177146 : Nat := 2144883662005819130764661

theorem tailTrace_4177146 : CollatzResearch.WordTrace tailWord_4177146 prefixEnd_4177146 2144883662005819130764661 := by
  unfold tailWord_4177146
  simp only [CollatzResearch.WordTrace]
  refine ⟨38088257731230229146313823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101568687283280611056836861 38088257731230229146313823)
  ·
    refine ⟨57132386596845343719470735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38088257731230229146313823 57132386596845343719470735)
    ·
      refine ⟨85698579895268015579206103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57132386596845343719470735 85698579895268015579206103)
      ·
        refine ⟨128547869842902023368809155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85698579895268015579206103 128547869842902023368809155)
        ·
          refine ⟨192821804764353035053213733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128547869842902023368809155 192821804764353035053213733)
          ·
            refine ⟨36154088393316194072477575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192821804764353035053213733 36154088393316194072477575)
            ·
              refine ⟨54231132589974291108716363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36154088393316194072477575 54231132589974291108716363)
              ·
                refine ⟨81346698884961436663074545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54231132589974291108716363 81346698884961436663074545)
                ·
                  refine ⟨61010024163721077497305909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81346698884961436663074545 61010024163721077497305909)
                  ·
                    refine ⟨5719689765348851015372429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61010024163721077497305909 5719689765348851015372429)
                    ·
                      refine ⟨2144883662005819130764661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719689765348851015372429 2144883662005819130764661)
                      ·
                        rfl

theorem cell23_4177146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_4177146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177146 prefixEnd_4177146 := by exact prefixLift 4177146
  have htrace : WordTrace (prefixWord ++ tailWord_4177146) baseStart_4177146 baseEnd_4177146 := by
    simpa [prefixWord, tailWord_4177146, baseEnd_4177146] using wordTrace_append hprefix tailTrace_4177146
  have hstable : (prefixWord ++ tailWord_4177146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177146).length < 2 ^ (prefixWord ++ tailWord_4177146).sum := by decide
  have hdescent : baseEnd_4177146 < baseStart_4177146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177180 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4177180 : Nat := 118140960795 + 4177180 * 2 ^ 59
def prefixEnd_4177180 : Nat := 4983230072969 + 3 ^ 40 * 4177180 * 2
def baseEnd_4177180 : Nat := 2144901120348071997739505

theorem tailTrace_4177180 : CollatzResearch.WordTrace tailWord_4177180 prefixEnd_4177180 2144901120348071997739505 := by
  unfold tailWord_4177180
  simp only [CollatzResearch.WordTrace]
  refine ⟨76177135503398870195996497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101569514004531826927995329 76177135503398870195996497)
  ·
    refine ⟨57132851627549152646997373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76177135503398870195996497 57132851627549152646997373)
    ·
      refine ⟨21424819360330932242624015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57132851627549152646997373 21424819360330932242624015)
      ·
        refine ⟨32137229040496398363936023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21424819360330932242624015 32137229040496398363936023)
        ·
          refine ⟨48205843560744597545904035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32137229040496398363936023 48205843560744597545904035)
          ·
            refine ⟨72308765341116896318856053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48205843560744597545904035 72308765341116896318856053)
            ·
              refine ⟨6778946750729709029892755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72308765341116896318856053 6778946750729709029892755)
              ·
                refine ⟨10168420126094563544839133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778946750729709029892755 10168420126094563544839133)
                ·
                  refine ⟨3813157547285461329314675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10168420126094563544839133 3813157547285461329314675)
                  ·
                    refine ⟨5719736320928191993972013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813157547285461329314675 5719736320928191993972013)
                    ·
                      refine ⟨2144901120348071997739505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719736320928191993972013 2144901120348071997739505)
                      ·
                        rfl

theorem cell23_4177180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4177180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177180 prefixEnd_4177180 := by exact prefixLift 4177180
  have htrace : WordTrace (prefixWord ++ tailWord_4177180) baseStart_4177180 baseEnd_4177180 := by
    simpa [prefixWord, tailWord_4177180, baseEnd_4177180] using wordTrace_append hprefix tailTrace_4177180
  have hstable : (prefixWord ++ tailWord_4177180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177180).length < 2 ^ (prefixWord ++ tailWord_4177180).sum := by decide
  have hdescent : baseEnd_4177180 < baseStart_4177180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177196 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_4177196 : Nat := 118140960795 + 4177196 * 2 ^ 59
def prefixEnd_4177196 : Nat := 4983230072969 + 3 ^ 40 * 4177196 * 2
def baseEnd_4177196 : Nat := 714969778679514645046477

theorem tailTrace_4177196 : CollatzResearch.WordTrace tailWord_4177196 prefixEnd_4177196 714969778679514645046477 := by
  unfold tailWord_4177196
  simp only [CollatzResearch.WordTrace]
  refine ⟨76177427287369887562287721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101569903049826516749716961 76177427287369887562287721)
  ·
    refine ⟨57133070465527415671715791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76177427287369887562287721 57133070465527415671715791)
    ·
      refine ⟨85699605698291123507573687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57133070465527415671715791 85699605698291123507573687)
      ·
        refine ⟨128549408547436685261360531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85699605698291123507573687 128549408547436685261360531)
        ·
          refine ⟨192824112821155027892040797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128549408547436685261360531 192824112821155027892040797)
          ·
            refine ⟨72309042307933135459515299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192824112821155027892040797 72309042307933135459515299)
            ·
              refine ⟨108463563461899703189272949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72309042307933135459515299 108463563461899703189272949)
              ·
                refine ⟨10168459074553097173994339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108463563461899703189272949 10168459074553097173994339)
                ·
                  refine ⟨15252688611829645760991509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168459074553097173994339 15252688611829645760991509)
                  ·
                    refine ⟨714969778679514645046477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15252688611829645760991509 714969778679514645046477)
                    ·
                      rfl

theorem cell23_4177196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_4177196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177196 prefixEnd_4177196 := by exact prefixLift 4177196
  have htrace : WordTrace (prefixWord ++ tailWord_4177196) baseStart_4177196 baseEnd_4177196 := by
    simpa [prefixWord, tailWord_4177196, baseEnd_4177196] using wordTrace_append hprefix tailTrace_4177196
  have hstable : (prefixWord ++ tailWord_4177196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177196).length < 2 ^ (prefixWord ++ tailWord_4177196).sum := by decide
  have hdescent : baseEnd_4177196 < baseStart_4177196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177203 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4]
def baseStart_4177203 : Nat := 118140960795 + 4177203 * 2 ^ 59
def prefixEnd_4177203 : Nat := 4983230072969 + 3 ^ 40 * 4177203 * 2
def baseEnd_4177203 : Nat := 2144912930403125407751899

theorem tailTrace_4177203 : CollatzResearch.WordTrace tailWord_4177203 prefixEnd_4177203 2144912930403125407751899 := by
  unfold tailWord_4177203
  simp only [CollatzResearch.WordTrace]
  refine ⟨152355109885714415320080263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101570073257142943546720175 152355109885714415320080263)
  ·
    refine ⟨228532664828571622980120395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152355109885714415320080263 228532664828571622980120395)
    ·
      refine ⟨342798997242857434470180593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228532664828571622980120395 342798997242857434470180593)
      ·
        refine ⟨257099247932143075852635445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342798997242857434470180593 257099247932143075852635445)
        ·
          refine ⟨24103054493638413361184573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257099247932143075852635445 24103054493638413361184573)
          ·
            refine ⟨9038645435114405010444215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24103054493638413361184573 9038645435114405010444215)
            ·
              refine ⟨13557968152671607515666323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038645435114405010444215 13557968152671607515666323)
              ·
                refine ⟨20336952229007411273499485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557968152671607515666323 20336952229007411273499485)
                ·
                  refine ⟨7626357085877779227562307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20336952229007411273499485 7626357085877779227562307)
                  ·
                    refine ⟨11439535628816668841343461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7626357085877779227562307 11439535628816668841343461)
                    ·
                      refine ⟨2144912930403125407751899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11439535628816668841343461 2144912930403125407751899)
                      ·
                        rfl

theorem cell23_4177203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_4177203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177203 prefixEnd_4177203 := by exact prefixLift 4177203
  have htrace : WordTrace (prefixWord ++ tailWord_4177203) baseStart_4177203 baseEnd_4177203 := by
    simpa [prefixWord, tailWord_4177203, baseEnd_4177203] using wordTrace_append hprefix tailTrace_4177203
  have hstable : (prefixWord ++ tailWord_4177203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177203).length < 2 ^ (prefixWord ++ tailWord_4177203).sum := by decide
  have hdescent : baseEnd_4177203 < baseStart_4177203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177217 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4177217 : Nat := 118140960795 + 4177217 * 2 ^ 59
def prefixEnd_4177217 : Nat := 4983230072969 + 3 ^ 40 * 4177217 * 2
def baseEnd_4177217 : Nat := 714973373044096117658945

theorem tailTrace_4177217 : CollatzResearch.WordTrace tailWord_4177217 prefixEnd_4177217 714973373044096117658945 := by
  unfold tailWord_4177217
  simp only [CollatzResearch.WordTrace]
  refine ⟨152355620507663695711089905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101570413671775797140726603 152355620507663695711089905)
  ·
    refine ⟨114266715380747771783317429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152355620507663695711089905 114266715380747771783317429)
    ·
      refine ⟨10712504566945103604686009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114266715380747771783317429 10712504566945103604686009)
      ·
        refine ⟨8034378425208827703514507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10712504566945103604686009 8034378425208827703514507)
        ·
          refine ⟨12051567637813241555271761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034378425208827703514507 12051567637813241555271761)
          ·
            refine ⟨9038675728359931166453821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12051567637813241555271761 9038675728359931166453821)
            ·
              refine ⟨3389503398134974187420183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9038675728359931166453821 3389503398134974187420183)
              ·
                refine ⟨5084255097202461281130275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389503398134974187420183 5084255097202461281130275)
                ·
                  refine ⟨7626382645803691921695413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084255097202461281130275 7626382645803691921695413)
                  ·
                    refine ⟨714973373044096117658945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7626382645803691921695413 714973373044096117658945)
                    ·
                      rfl

theorem cell23_4177217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4177217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177217 prefixEnd_4177217 := by exact prefixLift 4177217
  have htrace : WordTrace (prefixWord ++ tailWord_4177217) baseStart_4177217 baseEnd_4177217 := by
    simpa [prefixWord, tailWord_4177217, baseEnd_4177217] using wordTrace_append hprefix tailTrace_4177217
  have hstable : (prefixWord ++ tailWord_4177217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177217).length < 2 ^ (prefixWord ++ tailWord_4177217).sum := by decide
  have hdescent : baseEnd_4177217 < baseStart_4177217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177223 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_4177223 : Nat := 118140960795 + 4177223 * 2 ^ 59
def prefixEnd_4177223 : Nat := 4983230072969 + 3 ^ 40 * 4177223 * 2
def baseEnd_4177223 : Nat := 2144923200016215329501807

theorem tailTrace_4177223 : CollatzResearch.WordTrace tailWord_4177223 prefixEnd_4177223 2144923200016215329501807 := by
  unfold tailWord_4177223
  simp only [CollatzResearch.WordTrace]
  refine ⟨152355839345641958735808323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101570559563761305823872215 152355839345641958735808323)
  ·
    refine ⟨228533759018462938103712485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152355839345641958735808323 228533759018462938103712485)
    ·
      refine ⟨42850079815961800894446091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228533759018462938103712485 42850079815961800894446091)
      ·
        refine ⟨64275119723942701341669137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42850079815961800894446091 64275119723942701341669137)
        ·
          refine ⟨48206339792957026006251853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64275119723942701341669137 48206339792957026006251853)
          ·
            refine ⟨18077377422358884752344445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48206339792957026006251853 18077377422358884752344445)
            ·
              refine ⟨6779016533384581782129167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18077377422358884752344445 6779016533384581782129167)
              ·
                refine ⟨10168524800076872673193751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779016533384581782129167 10168524800076872673193751)
                ·
                  refine ⟨15252787200115309009790627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168524800076872673193751 15252787200115309009790627)
                  ·
                    refine ⟨22879180800172963514685941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15252787200115309009790627 22879180800172963514685941)
                    ·
                      refine ⟨2144923200016215329501807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22879180800172963514685941 2144923200016215329501807)
                      ·
                        rfl

theorem cell23_4177223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_4177223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177223 prefixEnd_4177223 := by exact prefixLift 4177223
  have htrace : WordTrace (prefixWord ++ tailWord_4177223) baseStart_4177223 baseEnd_4177223 := by
    simpa [prefixWord, tailWord_4177223, baseEnd_4177223] using wordTrace_append hprefix tailTrace_4177223
  have hstable : (prefixWord ++ tailWord_4177223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177223).length < 2 ^ (prefixWord ++ tailWord_4177223).sum := by decide
  have hdescent : baseEnd_4177223 < baseStart_4177223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177230 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_4177230 : Nat := 118140960795 + 4177230 * 2 ^ 59
def prefixEnd_4177230 : Nat := 4983230072969 + 3 ^ 40 * 4177230 * 2
def baseEnd_4177230 : Nat := 714975598126932267371425

theorem tailTrace_4177230 : CollatzResearch.WordTrace tailWord_4177230 prefixEnd_4177230 714975598126932267371425 := by
  unfold tailWord_4177230
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044511832077074866414143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101570729771077732620875429 19044511832077074866414143)
  ·
    refine ⟨28566767748115612299621215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19044511832077074866414143 28566767748115612299621215)
    ·
      refine ⟨42850151622173418449431823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28566767748115612299621215 42850151622173418449431823)
      ·
        refine ⟨64275227433260127674147735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42850151622173418449431823 64275227433260127674147735)
        ·
          refine ⟨96412841149890191511221603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64275227433260127674147735 96412841149890191511221603)
          ·
            refine ⟨144619261724835287266832405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96412841149890191511221603 144619261724835287266832405)
            ·
              refine ⟨6779027893351654090632769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144619261724835287266832405 6779027893351654090632769)
              ·
                refine ⟨5084270920013740567974577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6779027893351654090632769 5084270920013740567974577)
                ·
                  refine ⟨3813203190010305425980933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084270920013740567974577 3813203190010305425980933)
                  ·
                    refine ⟨714975598126932267371425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813203190010305425980933 714975598126932267371425)
                    ·
                      rfl

theorem cell23_4177230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_4177230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177230 prefixEnd_4177230 := by exact prefixLift 4177230
  have htrace : WordTrace (prefixWord ++ tailWord_4177230) baseStart_4177230 baseEnd_4177230 := by
    simpa [prefixWord, tailWord_4177230, baseEnd_4177230] using wordTrace_append hprefix tailTrace_4177230
  have hstable : (prefixWord ++ tailWord_4177230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177230).length < 2 ^ (prefixWord ++ tailWord_4177230).sum := by decide
  have hdescent : baseEnd_4177230 < baseStart_4177230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177250 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4177250 : Nat := 118140960795 + 4177250 * 2 ^ 59
def prefixEnd_4177250 : Nat := 4983230072969 + 3 ^ 40 * 4177250 * 2
def baseEnd_4177250 : Nat := 2144937063993886723864183

theorem tailTrace_4177250 : CollatzResearch.WordTrace tailWord_4177250 prefixEnd_4177250 2144937063993886723864183 := by
  unfold tailWord_4177250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089206029136035586760301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101571216077696094898027469 38089206029136035586760301)
  ·
    refine ⟨14283452260926013345035113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38089206029136035586760301 14283452260926013345035113)
    ·
      refine ⟨10712589195694510008776335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14283452260926013345035113 10712589195694510008776335)
      ·
        refine ⟨16068883793541765013164503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10712589195694510008776335 16068883793541765013164503)
        ·
          refine ⟨24103325690312647519746755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068883793541765013164503 24103325690312647519746755)
          ·
            refine ⟨36154988535468971279620133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24103325690312647519746755 36154988535468971279620133)
            ·
              refine ⟨6779060350400432114928775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36154988535468971279620133 6779060350400432114928775)
              ·
                refine ⟨10168590525600648172393163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779060350400432114928775 10168590525600648172393163)
                ·
                  refine ⟨15252885788400972258589745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168590525600648172393163 15252885788400972258589745)
                  ·
                    refine ⟨11439664341300729193942309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15252885788400972258589745 11439664341300729193942309)
                    ·
                      refine ⟨2144937063993886723864183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11439664341300729193942309 2144937063993886723864183)
                      ·
                        rfl

theorem cell23_4177250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4177250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177250 prefixEnd_4177250 := by exact prefixLift 4177250
  have htrace : WordTrace (prefixWord ++ tailWord_4177250) baseStart_4177250 baseEnd_4177250 := by
    simpa [prefixWord, tailWord_4177250, baseEnd_4177250] using wordTrace_append hprefix tailTrace_4177250
  have hstable : (prefixWord ++ tailWord_4177250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177250).length < 2 ^ (prefixWord ++ tailWord_4177250).sum := by decide
  have hdescent : baseEnd_4177250 < baseStart_4177250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177287 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_4177287 : Nat := 118140960795 + 4177287 * 2 ^ 59
def prefixEnd_4177287 : Nat := 4983230072969 + 3 ^ 40 * 4177287 * 2
def baseEnd_4177287 : Nat := 2144956062778103079101513

theorem tailTrace_4177287 : CollatzResearch.WordTrace tailWord_4177287 prefixEnd_4177287 2144956062778103079101513 := by
  unfold tailWord_4177287
  simp only [CollatzResearch.WordTrace]
  refine ⟨152358173617410097666138115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101572115744940065110758743 152358173617410097666138115)
  ·
    refine ⟨228537260426115146499207173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152358173617410097666138115 228537260426115146499207173)
    ·
      refine ⟨42850736329896589968601345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228537260426115146499207173 42850736329896589968601345)
      ·
        refine ⟨32138052247422442476451009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42850736329896589968601345 32138052247422442476451009)
        ·
          refine ⟨24103539185566831857338257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32138052247422442476451009 24103539185566831857338257)
          ·
            refine ⟨18077654389175123893003693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24103539185566831857338257 18077654389175123893003693)
            ·
              refine ⟨6779120395940671459876385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18077654389175123893003693 6779120395940671459876385)
              ·
                refine ⟨5084340296955503594907289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6779120395940671459876385 5084340296955503594907289)
                ·
                  refine ⟨3813255222716627696180467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084340296955503594907289 3813255222716627696180467)
                  ·
                    refine ⟨5719882834074941544270701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813255222716627696180467 5719882834074941544270701)
                    ·
                      refine ⟨2144956062778103079101513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719882834074941544270701 2144956062778103079101513)
                      ·
                        rfl

theorem cell23_4177287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_4177287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177287 prefixEnd_4177287 := by exact prefixLift 4177287
  have htrace : WordTrace (prefixWord ++ tailWord_4177287) baseStart_4177287 baseEnd_4177287 := by
    simpa [prefixWord, tailWord_4177287, baseEnd_4177287] using wordTrace_append hprefix tailTrace_4177287
  have hstable : (prefixWord ++ tailWord_4177287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177287).length < 2 ^ (prefixWord ++ tailWord_4177287).sum := by decide
  have hdescent : baseEnd_4177287 < baseStart_4177287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177304 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4177304 : Nat := 118140960795 + 4177304 * 2 ^ 59
def prefixEnd_4177304 : Nat := 4983230072969 + 3 ^ 40 * 4177304 * 2
def baseEnd_4177304 : Nat := 2144964791949229512588935

theorem tailTrace_4177304 : CollatzResearch.WordTrace tailWord_4177304 prefixEnd_4177304 2144964791949229512588935 := by
  unfold tailWord_4177304
  simp only [CollatzResearch.WordTrace]
  refine ⟨76179396829174254784753483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101572529105565673046337977 76179396829174254784753483)
  ·
    refine ⟨114269095243761382177130225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76179396829174254784753483 114269095243761382177130225)
    ·
      refine ⟨85701821432821036632847669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114269095243761382177130225 85701821432821036632847669)
      ·
        refine ⟨8034545759326972184329469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85701821432821036632847669 8034545759326972184329469)
        ·
          refine ⟨3012954659747614569123551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8034545759326972184329469 3012954659747614569123551)
          ·
            refine ⟨4519431989621421853685327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012954659747614569123551 4519431989621421853685327)
            ·
              refine ⟨6779147984432132780527991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519431989621421853685327 6779147984432132780527991)
              ·
                refine ⟨10168721976648199170791987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779147984432132780527991 10168721976648199170791987)
                ·
                  refine ⟨15253082964972298756187981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168721976648199170791987 15253082964972298756187981)
                  ·
                    refine ⟨5719906111864612033570493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15253082964972298756187981 5719906111864612033570493)
                    ·
                      refine ⟨2144964791949229512588935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719906111864612033570493 2144964791949229512588935)
                      ·
                        rfl

theorem cell23_4177304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4177304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177304 prefixEnd_4177304 := by exact prefixLift 4177304
  have htrace : WordTrace (prefixWord ++ tailWord_4177304) baseStart_4177304 baseEnd_4177304 := by
    simpa [prefixWord, tailWord_4177304, baseEnd_4177304] using wordTrace_append hprefix tailTrace_4177304
  have hstable : (prefixWord ++ tailWord_4177304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177304).length < 2 ^ (prefixWord ++ tailWord_4177304).sum := by decide
  have hdescent : baseEnd_4177304 < baseStart_4177304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177314 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_4177314 : Nat := 118140960795 + 4177314 * 2 ^ 59
def prefixEnd_4177314 : Nat := 4983230072969 + 3 ^ 40 * 4177314 * 2
def baseEnd_4177314 : Nat := 2144969926755774473463889

theorem tailTrace_4177314 : CollatzResearch.WordTrace tailWord_4177314 prefixEnd_4177314 2144969926755774473463889 := by
  unfold tailWord_4177314
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089789597078070319342749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101572772258874854184913997 38089789597078070319342749)
  ·
    refine ⟨14283671098904276369753531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38089789597078070319342749 14283671098904276369753531)
    ·
      refine ⟨21425506648356414554630297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14283671098904276369753531 21425506648356414554630297)
      ·
        refine ⟨16069129986267310915972723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21425506648356414554630297 16069129986267310915972723)
        ·
          refine ⟨24103694979400966373959085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069129986267310915972723 24103694979400966373959085)
          ·
            refine ⟨9038885617275362390234657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24103694979400966373959085 9038885617275362390234657)
            ·
              refine ⟨6779164212956521792675993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9038885617275362390234657 6779164212956521792675993)
              ·
                refine ⟨5084373159717391344506995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6779164212956521792675993 5084373159717391344506995)
                ·
                  refine ⟨7626559739576087016760493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084373159717391344506995 7626559739576087016760493)
                  ·
                    refine ⟨2859959902341032631285185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7626559739576087016760493 2859959902341032631285185)
                    ·
                      refine ⟨2144969926755774473463889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2859959902341032631285185 2144969926755774473463889)
                      ·
                        rfl

theorem cell23_4177314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_4177314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177314 prefixEnd_4177314 := by exact prefixLift 4177314
  have htrace : WordTrace (prefixWord ++ tailWord_4177314) baseStart_4177314 baseEnd_4177314 := by
    simpa [prefixWord, tailWord_4177314, baseEnd_4177314] using wordTrace_append hprefix tailTrace_4177314
  have hstable : (prefixWord ++ tailWord_4177314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177314).length < 2 ^ (prefixWord ++ tailWord_4177314).sum := by decide
  have hdescent : baseEnd_4177314 < baseStart_4177314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177343 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_4177343 : Nat := 118140960795 + 4177343 * 2 ^ 59
def prefixEnd_4177343 : Nat := 4983230072969 + 3 ^ 40 * 4177343 * 2
def baseEnd_4177343 : Nat := 2144984817694754860001255

theorem tailTrace_4177343 : CollatzResearch.WordTrace tailWord_4177343 prefixEnd_4177343 2144984817694754860001255 := by
  unfold tailWord_4177343
  simp only [CollatzResearch.WordTrace]
  refine ⟨152360216105207219230176683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101573477403471479486784455 152360216105207219230176683)
  ·
    refine ⟨228540324157810828845265025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152360216105207219230176683 228540324157810828845265025)
    ·
      refine ⟨171405243118358121633948769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228540324157810828845265025 171405243118358121633948769)
      ·
        refine ⟨128553932338768591225461577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171405243118358121633948769 128553932338768591225461577)
        ·
          refine ⟨96415449254076443419096183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128553932338768591225461577 96415449254076443419096183)
          ·
            refine ⟨144623173881114665128644275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96415449254076443419096183 144623173881114665128644275)
            ·
              refine ⟨216934760821671997692966413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144623173881114665128644275 216934760821671997692966413)
              ·
                refine ⟨81350535308126999134862405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216934760821671997692966413 81350535308126999134862405)
                ·
                  refine ⟨15253225370273812337786701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81350535308126999134862405 15253225370273812337786701)
                  ·
                    refine ⟨5719959513852679626670013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15253225370273812337786701 5719959513852679626670013)
                    ·
                      refine ⟨2144984817694754860001255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5719959513852679626670013 2144984817694754860001255)
                      ·
                        rfl

theorem cell23_4177343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_4177343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177343 prefixEnd_4177343 := by exact prefixLift 4177343
  have htrace : WordTrace (prefixWord ++ tailWord_4177343) baseStart_4177343 baseEnd_4177343 := by
    simpa [prefixWord, tailWord_4177343, baseEnd_4177343] using wordTrace_append hprefix tailTrace_4177343
  have hstable : (prefixWord ++ tailWord_4177343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177343).length < 2 ^ (prefixWord ++ tailWord_4177343).sum := by decide
  have hdescent : baseEnd_4177343 < baseStart_4177343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177397 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4177397 : Nat := 118140960795 + 4177397 * 2 ^ 59
def prefixEnd_4177397 : Nat := 4983230072969 + 3 ^ 40 * 4177397 * 2
def baseEnd_4177397 : Nat := 715004181883365882908669

theorem tailTrace_4177397 : CollatzResearch.WordTrace tailWord_4177397 prefixEnd_4177397 715004181883365882908669 := by
  unfold tailWord_4177397
  simp only [CollatzResearch.WordTrace]
  refine ⟨152362185647011586452642445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101574790431341057635094963 152362185647011586452642445)
  ·
    refine ⟨57135819617629344919740917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152362185647011586452642445 57135819617629344919740917)
    ·
      refine ⟨5356483089152751086225711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57135819617629344919740917 5356483089152751086225711)
      ·
        refine ⟨8034724633729126629338567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356483089152751086225711 8034724633729126629338567)
        ·
          refine ⟨12052086950593689944007851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034724633729126629338567 12052086950593689944007851)
          ·
            refine ⟨18078130425890534916011777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052086950593689944007851 18078130425890534916011777)
            ·
              refine ⟨13558597819417901187008833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18078130425890534916011777 13558597819417901187008833)
              ·
                refine ⟨10168948364563425890256625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13558597819417901187008833 10168948364563425890256625)
                ·
                  refine ⟨7626711273422569417692469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10168948364563425890256625 7626711273422569417692469)
                  ·
                    refine ⟨715004181883365882908669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7626711273422569417692469 715004181883365882908669)
                    ·
                      rfl

theorem cell23_4177397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4177397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177397 prefixEnd_4177397 := by exact prefixLift 4177397
  have htrace : WordTrace (prefixWord ++ tailWord_4177397) baseStart_4177397 baseEnd_4177397 := by
    simpa [prefixWord, tailWord_4177397, baseEnd_4177397] using wordTrace_append hprefix tailTrace_4177397
  have hstable : (prefixWord ++ tailWord_4177397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177397).length < 2 ^ (prefixWord ++ tailWord_4177397).sum := by decide
  have hdescent : baseEnd_4177397 < baseStart_4177397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177400 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_4177400 : Nat := 118140960795 + 4177400 * 2 ^ 59
def prefixEnd_4177400 : Nat := 4983230072969 + 3 ^ 40 * 4177400 * 2
def baseEnd_4177400 : Nat := 2145014086092061136988493

theorem tailTrace_4177400 : CollatzResearch.WordTrace tailWord_4177400 prefixEnd_4177400 2145014086092061136988493 := by
  unfold tailWord_4177400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76181147533000358982500827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101574863377333811976667769 76181147533000358982500827)
  ·
    refine ⟨114271721299500538473751241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76181147533000358982500827 114271721299500538473751241)
    ·
      refine ⟨85703790974625403855313431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114271721299500538473751241 85703790974625403855313431)
      ·
        refine ⟨128555686461938105782970147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85703790974625403855313431 128555686461938105782970147)
        ·
          refine ⟨192833529692907158674455221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128555686461938105782970147 192833529692907158674455221)
          ·
            refine ⟨18078143408710046125730177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192833529692907158674455221 18078143408710046125730177)
            ·
              refine ⟨13558607556532534594297633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18078143408710046125730177 13558607556532534594297633)
              ·
                refine ⟨10168955667399400945723225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13558607556532534594297633 10168955667399400945723225)
                ·
                  refine ⟨7626716750549550709292419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10168955667399400945723225 7626716750549550709292419)
                  ·
                    refine ⟨11440075125824326063938629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7626716750549550709292419 11440075125824326063938629)
                    ·
                      refine ⟨2145014086092061136988493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11440075125824326063938629 2145014086092061136988493)
                      ·
                        rfl

theorem cell23_4177400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_4177400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177400 prefixEnd_4177400 := by exact prefixLift 4177400
  have htrace : WordTrace (prefixWord ++ tailWord_4177400) baseStart_4177400 baseEnd_4177400 := by
    simpa [prefixWord, tailWord_4177400, baseEnd_4177400] using wordTrace_append hprefix tailTrace_4177400
  have hstable : (prefixWord ++ tailWord_4177400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177400).length < 2 ^ (prefixWord ++ tailWord_4177400).sum := by decide
  have hdescent : baseEnd_4177400 < baseStart_4177400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177413 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_4177413 : Nat := 118140960795 + 4177413 * 2 ^ 59
def prefixEnd_4177413 : Nat := 4983230072969 + 3 ^ 40 * 4177413 * 2
def baseEnd_4177413 : Nat := 2145020761340569586125933

theorem tailTrace_4177413 : CollatzResearch.WordTrace tailWord_4177413 prefixEnd_4177413 2145020761340569586125933 := by
  unfold tailWord_4177413
  simp only [CollatzResearch.WordTrace]
  refine ⟨152362769214953621185224893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101575179476635747456816595 152362769214953621185224893)
  ·
    refine ⟨57136038455607607944459335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152362769214953621185224893 57136038455607607944459335)
    ·
      refine ⟨85704057683411411916689003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57136038455607607944459335 85704057683411411916689003)
      ·
        refine ⟨128556086525117117875033505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85704057683411411916689003 128556086525117117875033505)
        ·
          refine ⟨96417064893837838406275129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128556086525117117875033505 96417064893837838406275129)
          ·
            refine ⟨72312798670378378804706347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96417064893837838406275129 72312798670378378804706347)
            ·
              refine ⟨108469198005567568207059521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72312798670378378804706347 108469198005567568207059521)
              ·
                refine ⟨81351898504175676155294641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108469198005567568207059521 81351898504175676155294641)
                ·
                  refine ⟨61013923878131757116470981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81351898504175676155294641 61013923878131757116470981)
                  ·
                    refine ⟨11440110727149704459338309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61013923878131757116470981 11440110727149704459338309)
                    ·
                      refine ⟨2145020761340569586125933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11440110727149704459338309 2145020761340569586125933)
                      ·
                        rfl

theorem cell23_4177413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_4177413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177413 prefixEnd_4177413 := by exact prefixLift 4177413
  have htrace : WordTrace (prefixWord ++ tailWord_4177413) baseStart_4177413 baseEnd_4177413 := by
    simpa [prefixWord, tailWord_4177413, baseEnd_4177413] using wordTrace_append hprefix tailTrace_4177413
  have hstable : (prefixWord ++ tailWord_4177413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177413).length < 2 ^ (prefixWord ++ tailWord_4177413).sum := by decide
  have hdescent : baseEnd_4177413 < baseStart_4177413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177507 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 4]
def baseStart_4177507 : Nat := 118140960795 + 4177507 * 2 ^ 59
def prefixEnd_4177507 : Nat := 4983230072969 + 3 ^ 40 * 4177507 * 2
def baseEnd_4177507 : Nat := 2145069028522092218350501

theorem tailTrace_4177507 : CollatzResearch.WordTrace tailWord_4177507 prefixEnd_4177507 2145069028522092218350501 := by
  unfold tailWord_4177507
  simp only [CollatzResearch.WordTrace]
  refine ⟨152366197676613075239146775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101577465117742050159431183 152366197676613075239146775)
  ·
    refine ⟨228549296514919612858720163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152366197676613075239146775 228549296514919612858720163)
    ·
      refine ⟨342823944772379419288080245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228549296514919612858720163 342823944772379419288080245)
      ·
        refine ⟨32139744822410570558257523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342823944772379419288080245 32139744822410570558257523)
        ·
          refine ⟨48209617233615855837386285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32139744822410570558257523 48209617233615855837386285)
          ·
            refine ⟨18078606462605945939019857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48209617233615855837386285 18078606462605945939019857)
            ·
              refine ⟨13558954846954459454264893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18078606462605945939019857 13558954846954459454264893)
              ·
                refine ⟨5084608067607922295349335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13558954846954459454264893 5084608067607922295349335)
                ·
                  refine ⟨7626912101411883443024003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084608067607922295349335 7626912101411883443024003)
                  ·
                    refine ⟨11440368152117825164536005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7626912101411883443024003 11440368152117825164536005)
                    ·
                      refine ⟨2145069028522092218350501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11440368152117825164536005 2145069028522092218350501)
                      ·
                        rfl

theorem cell23_4177507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_4177507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177507 prefixEnd_4177507 := by exact prefixLift 4177507
  have htrace : WordTrace (prefixWord ++ tailWord_4177507) baseStart_4177507 baseEnd_4177507 := by
    simpa [prefixWord, tailWord_4177507, baseEnd_4177507] using wordTrace_append hprefix tailTrace_4177507
  have hstable : (prefixWord ++ tailWord_4177507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177507).length < 2 ^ (prefixWord ++ tailWord_4177507).sum := by decide
  have hdescent : baseEnd_4177507 < baseStart_4177507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177513 : List Nat := [1, 2, 1, 1, 1, 4, 13]
def baseStart_4177513 : Nat := 118140960795 + 4177513 * 2 ^ 59
def prefixEnd_4177513 : Nat := 4983230072969 + 3 ^ 40 * 4177513 * 2
def baseEnd_4177513 : Nat := 26482371721061965368833

theorem tailTrace_4177513 : CollatzResearch.WordTrace tailWord_4177513 prefixEnd_4177513 26482371721061965368833 := by
  unfold tailWord_4177513
  simp only [CollatzResearch.WordTrace]
  refine ⟨152366416514591338263865193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101577611009727558842576795 152366416514591338263865193)
  ·
    refine ⟨114274812385943503697898895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152366416514591338263865193 114274812385943503697898895)
    ·
      refine ⟨171412218578915255546848343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114274812385943503697898895 171412218578915255546848343)
      ·
        refine ⟨257118327868372883320272515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171412218578915255546848343 257118327868372883320272515)
        ·
          refine ⟨385677491802559324980408773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257118327868372883320272515 385677491802559324980408773)
          ·
            refine ⟨72314529712979873433826645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385677491802559324980408773 72314529712979873433826645)
            ·
              refine ⟨26482371721061965368833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 72314529712979873433826645 26482371721061965368833)
              ·
                rfl

theorem cell23_4177513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 13].length) (baseStart_4177513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177513 prefixEnd_4177513 := by exact prefixLift 4177513
  have htrace : WordTrace (prefixWord ++ tailWord_4177513) baseStart_4177513 baseEnd_4177513 := by
    simpa [prefixWord, tailWord_4177513, baseEnd_4177513] using wordTrace_append hprefix tailTrace_4177513
  have hstable : (prefixWord ++ tailWord_4177513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177513).length < 2 ^ (prefixWord ++ tailWord_4177513).sum := by decide
  have hdescent : baseEnd_4177513 < baseStart_4177513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177518 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_4177518 : Nat := 118140960795 + 4177518 * 2 ^ 59
def prefixEnd_4177518 : Nat := 4983230072969 + 3 ^ 40 * 4177518 * 2
def baseEnd_4177518 : Nat := 2145074676809291675312951

theorem tailTrace_4177518 : CollatzResearch.WordTrace tailWord_4177518 prefixEnd_4177518 2145074676809291675312951 := by
  unfold tailWord_4177518
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045824859946653014724651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101577732586382149411864805 19045824859946653014724651)
  ·
    refine ⟨28568737289919979522086977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19045824859946653014724651 28568737289919979522086977)
    ·
      refine ⟨21426552967439984641565233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28568737289919979522086977 21426552967439984641565233)
      ·
        refine ⟨16069914725579988481173925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21426552967439984641565233 16069914725579988481173925)
        ·
          refine ⟨3013109011046247840220111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16069914725579988481173925 3013109011046247840220111)
          ·
            refine ⟨4519663516569371760330167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013109011046247840220111 4519663516569371760330167)
            ·
              refine ⟨6779495274854057640495251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519663516569371760330167 6779495274854057640495251)
              ·
                refine ⟨10169242912281086460742877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779495274854057640495251 10169242912281086460742877)
                ·
                  refine ⟨3813466092105407422778579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10169242912281086460742877 3813466092105407422778579)
                  ·
                    refine ⟨5720199138158111134167869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813466092105407422778579 5720199138158111134167869)
                    ·
                      refine ⟨2145074676809291675312951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5720199138158111134167869 2145074676809291675312951)
                      ·
                        rfl

theorem cell23_4177518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_4177518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177518 prefixEnd_4177518 := by exact prefixLift 4177518
  have htrace : WordTrace (prefixWord ++ tailWord_4177518) baseStart_4177518 baseEnd_4177518 := by
    simpa [prefixWord, tailWord_4177518, baseEnd_4177518] using wordTrace_append hprefix tailTrace_4177518
  have hstable : (prefixWord ++ tailWord_4177518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177518).length < 2 ^ (prefixWord ++ tailWord_4177518).sum := by decide
  have hdescent : baseEnd_4177518 < baseStart_4177518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177520 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_4177520 : Nat := 118140960795 + 4177520 * 2 ^ 59
def prefixEnd_4177520 : Nat := 4983230072969 + 3 ^ 40 * 4177520 * 2
def baseEnd_4177520 : Nat := 2145075703770600667487941

theorem tailTrace_4177520 : CollatzResearch.WordTrace tailWord_4177520 prefixEnd_4177520 2145075703770600667487941 := by
  unfold tailWord_4177520
  simp only [CollatzResearch.WordTrace]
  refine ⟨76183335912782989229685007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101577781217043985639580009 76183335912782989229685007)
  ·
    refine ⟨114275003869174483844527511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76183335912782989229685007 114275003869174483844527511)
    ·
      refine ⟨171412505803761725766791267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114275003869174483844527511 171412505803761725766791267)
      ·
        refine ⟨257118758705642588650186901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171412505803761725766791267 257118758705642588650186901)
        ·
          refine ⟨12052441814326996342977511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 257118758705642588650186901 12052441814326996342977511)
          ·
            refine ⟨18078662721490494514466267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052441814326996342977511 18078662721490494514466267)
            ·
              refine ⟨27117994082235741771699401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18078662721490494514466267 27117994082235741771699401)
              ·
                refine ⟨20338495561676806328774551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27117994082235741771699401 20338495561676806328774551)
                ·
                  refine ⟨30507743342515209493161827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20338495561676806328774551 30507743342515209493161827)
                  ·
                    refine ⟨45761615013772814239742741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30507743342515209493161827 45761615013772814239742741)
                    ·
                      refine ⟨2145075703770600667487941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45761615013772814239742741 2145075703770600667487941)
                      ·
                        rfl

theorem cell23_4177520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_4177520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177520 prefixEnd_4177520 := by exact prefixLift 4177520
  have htrace : WordTrace (prefixWord ++ tailWord_4177520) baseStart_4177520 baseEnd_4177520 := by
    simpa [prefixWord, tailWord_4177520, baseEnd_4177520] using wordTrace_append hprefix tailTrace_4177520
  have hstable : (prefixWord ++ tailWord_4177520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177520).length < 2 ^ (prefixWord ++ tailWord_4177520).sum := by decide
  have hdescent : baseEnd_4177520 < baseStart_4177520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177554 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4177554 : Nat := 118140960795 + 4177554 * 2 ^ 59
def prefixEnd_4177554 : Nat := 4983230072969 + 3 ^ 40 * 4177554 * 2
def baseEnd_4177554 : Nat := 2145093162112853534462785

theorem tailTrace_4177554 : CollatzResearch.WordTrace tailWord_4177554 prefixEnd_4177554 2145093162112853534462785 := by
  unfold tailWord_4177554
  simp only [CollatzResearch.WordTrace]
  refine ⟨38091977976860700566526929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101578607938295201510738477 38091977976860700566526929)
  ·
    refine ⟨28568983482645525424895197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38091977976860700566526929 28568983482645525424895197)
    ·
      refine ⟨10713368805992072034335699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28568983482645525424895197 10713368805992072034335699)
      ·
        refine ⟨16070053208988108051503549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10713368805992072034335699 16070053208988108051503549)
        ·
          refine ⟨6026269953370540519313831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16070053208988108051503549 6026269953370540519313831)
          ·
            refine ⟨9039404930055810778970747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026269953370540519313831 9039404930055810778970747)
            ·
              refine ⟨13559107395083716168456121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039404930055810778970747 13559107395083716168456121)
              ·
                refine ⟨10169330546312787126342091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13559107395083716168456121 10169330546312787126342091)
                ·
                  refine ⟨15253995819469180689513137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10169330546312787126342091 15253995819469180689513137)
                  ·
                    refine ⟨11440496864601885517134853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15253995819469180689513137 11440496864601885517134853)
                    ·
                      refine ⟨2145093162112853534462785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11440496864601885517134853 2145093162112853534462785)
                      ·
                        rfl

theorem cell23_4177554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4177554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177554 prefixEnd_4177554 := by exact prefixLift 4177554
  have htrace : WordTrace (prefixWord ++ tailWord_4177554) baseStart_4177554 baseEnd_4177554 := by
    simpa [prefixWord, tailWord_4177554, baseEnd_4177554] using wordTrace_append hprefix tailTrace_4177554
  have hstable : (prefixWord ++ tailWord_4177554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177554).length < 2 ^ (prefixWord ++ tailWord_4177554).sum := by decide
  have hdescent : baseEnd_4177554 < baseStart_4177554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177557 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_4177557 : Nat := 118140960795 + 4177557 * 2 ^ 59
def prefixEnd_4177557 : Nat := 4983230072969 + 3 ^ 40 * 4177557 * 2
def baseEnd_4177557 : Nat := 2145094702554817022725271

theorem tailTrace_4177557 : CollatzResearch.WordTrace tailWord_4177557 prefixEnd_4177557 2145094702554817022725271 := by
  unfold tailWord_4177557
  simp only [CollatzResearch.WordTrace]
  refine ⟨152368021326431933778466925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101578680884287955852311283 152368021326431933778466925)
  ·
    refine ⟨57138007997411975166925097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152368021326431933778466925 57138007997411975166925097)
    ·
      refine ⟨42853505998058981375193823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57138007997411975166925097 42853505998058981375193823)
      ·
        refine ⟨64280258997088472062790735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42853505998058981375193823 64280258997088472062790735)
        ·
          refine ⟨96420388495632708094186103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64280258997088472062790735 96420388495632708094186103)
          ·
            refine ⟨144630582743449062141279155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96420388495632708094186103 144630582743449062141279155)
            ·
              refine ⟨216945874115173593211918733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144630582743449062141279155 216945874115173593211918733)
              ·
                refine ⟨81354702793190097454469525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216945874115173593211918733 81354702793190097454469525)
                ·
                  refine ⟨3813501693430785818178259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81354702793190097454469525 3813501693430785818178259)
                  ·
                    refine ⟨5720252540146178727267389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813501693430785818178259 5720252540146178727267389)
                    ·
                      refine ⟨2145094702554817022725271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5720252540146178727267389 2145094702554817022725271)
                      ·
                        rfl

theorem cell23_4177557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_4177557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177557 prefixEnd_4177557 := by exact prefixLift 4177557
  have htrace : WordTrace (prefixWord ++ tailWord_4177557) baseStart_4177557 baseEnd_4177557 := by
    simpa [prefixWord, tailWord_4177557, baseEnd_4177557] using wordTrace_append hprefix tailTrace_4177557
  have hstable : (prefixWord ++ tailWord_4177557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177557).length < 2 ^ (prefixWord ++ tailWord_4177557).sum := by decide
  have hdescent : baseEnd_4177557 < baseStart_4177557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177614 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_4177614 : Nat := 118140960795 + 4177614 * 2 ^ 59
def prefixEnd_4177614 : Nat := 4983230072969 + 3 ^ 40 * 4177614 * 2
def baseEnd_4177614 : Nat := 2145123970952123299712509

theorem tailTrace_4177614 : CollatzResearch.WordTrace tailWord_4177614 prefixEnd_4177614 2145123970952123299712509 := by
  unfold tailWord_4177614
  simp only [CollatzResearch.WordTrace]
  refine ⟨19046262535903179064161487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101580066858150288342194597 19046262535903179064161487)
  ·
    refine ⟨28569393803854768596242231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19046262535903179064161487 28569393803854768596242231)
    ·
      refine ⟨42854090705782152894363347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28569393803854768596242231 42854090705782152894363347)
      ·
        refine ⟨64281136058673229341545021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42854090705782152894363347 64281136058673229341545021)
        ·
          refine ⟨24105426022002461003079383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64281136058673229341545021 24105426022002461003079383)
          ·
            refine ⟨36158139033003691504619075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24105426022002461003079383 36158139033003691504619075)
            ·
              refine ⟨54237208549505537256928613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36158139033003691504619075 54237208549505537256928613)
              ·
                refine ⟨10169476603032288235674115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54237208549505537256928613 10169476603032288235674115)
                ·
                  refine ⟨15254214904548432353511173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10169476603032288235674115 15254214904548432353511173)
                  ·
                    refine ⟨2860165294602831066283345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15254214904548432353511173 2860165294602831066283345)
                    ·
                      refine ⟨2145123970952123299712509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860165294602831066283345 2145123970952123299712509)
                      ·
                        rfl

theorem cell23_4177614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_4177614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177614 prefixEnd_4177614 := by exact prefixLift 4177614
  have htrace : WordTrace (prefixWord ++ tailWord_4177614) baseStart_4177614 baseEnd_4177614 := by
    simpa [prefixWord, tailWord_4177614, baseEnd_4177614] using wordTrace_append hprefix tailTrace_4177614
  have hstable : (prefixWord ++ tailWord_4177614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177614).length < 2 ^ (prefixWord ++ tailWord_4177614).sum := by decide
  have hdescent : baseEnd_4177614 < baseStart_4177614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177618 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4177618 : Nat := 118140960795 + 4177618 * 2 ^ 59
def prefixEnd_4177618 : Nat := 4983230072969 + 3 ^ 40 * 4177618 * 2
def baseEnd_4177618 : Nat := 2145126024874741284062491

theorem tailTrace_4177618 : CollatzResearch.WordTrace tailWord_4177618 prefixEnd_4177618 2145126024874741284062491 := by
  unfold tailWord_4177618
  simp only [CollatzResearch.WordTrace]
  refine ⟨38092561544802735299109377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101580164119473960797625005 38092561544802735299109377)
  ·
    refine ⟨28569421158602051474332033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38092561544802735299109377 28569421158602051474332033)
    ·
      refine ⟨21427065868951538605749025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28569421158602051474332033 21427065868951538605749025)
      ·
        refine ⟨16070299401713653954311769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21427065868951538605749025 16070299401713653954311769)
        ·
          refine ⟨12052724551285240465733827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16070299401713653954311769 12052724551285240465733827)
          ·
            refine ⟨18079086826927860698600741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052724551285240465733827 18079086826927860698600741)
            ·
              refine ⟨3389828780048973880987639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18079086826927860698600741 3389828780048973880987639)
              ·
                refine ⟨5084743170073460821481459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389828780048973880987639 5084743170073460821481459)
                ·
                  refine ⟨7627114755110191232222189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084743170073460821481459 7627114755110191232222189)
                  ·
                    refine ⟨2860168033166321712083321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7627114755110191232222189 2860168033166321712083321)
                    ·
                      refine ⟨2145126024874741284062491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860168033166321712083321 2145126024874741284062491)
                      ·
                        rfl

theorem cell23_4177618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4177618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177618 prefixEnd_4177618 := by exact prefixLift 4177618
  have htrace : WordTrace (prefixWord ++ tailWord_4177618) baseStart_4177618 baseEnd_4177618 := by
    simpa [prefixWord, tailWord_4177618, baseEnd_4177618] using wordTrace_append hprefix tailTrace_4177618
  have hstable : (prefixWord ++ tailWord_4177618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177618).length < 2 ^ (prefixWord ++ tailWord_4177618).sum := by decide
  have hdescent : baseEnd_4177618 < baseStart_4177618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177637 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 7]
def baseStart_4177637 : Nat := 118140960795 + 4177637 * 2 ^ 59
def prefixEnd_4177637 : Nat := 4983230072969 + 3 ^ 40 * 4177637 * 2
def baseEnd_4177637 : Nat := 238348420111908523302767

theorem tailTrace_4177637 : CollatzResearch.WordTrace tailWord_4177637 prefixEnd_4177637 238348420111908523302767 := by
  unfold tailWord_4177637
  simp only [CollatzResearch.WordTrace]
  refine ⟨152370939166142107441379165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101580626110761404960919443 152370939166142107441379165)
  ·
    refine ⟨57139102187303290290517187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152370939166142107441379165 57139102187303290290517187)
    ·
      refine ⟨85708653280954935435775781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57139102187303290290517187 85708653280954935435775781)
      ·
        refine ⟨16070372490179050394207959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85708653280954935435775781 16070372490179050394207959)
        ·
          refine ⟨24105558735268575591311939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16070372490179050394207959 24105558735268575591311939)
          ·
            refine ⟨36158338102902863386967909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24105558735268575591311939 36158338102902863386967909)
            ·
              refine ⟨6779688394294286885056483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36158338102902863386967909 6779688394294286885056483)
              ·
                refine ⟨10169532591441430327584725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779688394294286885056483 10169532591441430327584725)
                ·
                  refine ⟨238348420111908523302767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10169532591441430327584725 238348420111908523302767)
                  ·
                    rfl

theorem cell23_4177637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_4177637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177637 prefixEnd_4177637 := by exact prefixLift 4177637
  have htrace : WordTrace (prefixWord ++ tailWord_4177637) baseStart_4177637 baseEnd_4177637 := by
    simpa [prefixWord, tailWord_4177637, baseEnd_4177637] using wordTrace_append hprefix tailTrace_4177637
  have hstable : (prefixWord ++ tailWord_4177637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177637).length < 2 ^ (prefixWord ++ tailWord_4177637).sum := by decide
  have hdescent : baseEnd_4177637 < baseStart_4177637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177647 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_4177647 : Nat := 118140960795 + 4177647 * 2 ^ 59
def prefixEnd_4177647 : Nat := 4983230072969 + 3 ^ 40 * 4177647 * 2
def baseEnd_4177647 : Nat := 2145140915813721670599857

theorem tailTrace_4177647 : CollatzResearch.WordTrace tailWord_4177647 prefixEnd_4177647 2145140915813721670599857 := by
  unfold tailWord_4177647
  simp only [CollatzResearch.WordTrace]
  refine ⟨152371303896105879149243195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101580869264070586099495463 152371303896105879149243195)
  ·
    refine ⟨228556955844158818723864793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152371303896105879149243195 228556955844158818723864793)
    ·
      refine ⟨171417716883119114042898595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228556955844158818723864793 171417716883119114042898595)
      ·
        refine ⟨257126575324678671064347893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171417716883119114042898595 257126575324678671064347893)
        ·
          refine ⟨24105616436688625412282615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257126575324678671064347893 24105616436688625412282615)
          ·
            refine ⟨36158424655032938118423923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24105616436688625412282615 36158424655032938118423923)
            ·
              refine ⟨54237636982549407177635885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36158424655032938118423923 54237636982549407177635885)
              ·
                refine ⟨20339113868456027691613457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54237636982549407177635885 20339113868456027691613457)
                ·
                  refine ⟨15254335401342020768710093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20339113868456027691613457 15254335401342020768710093)
                  ·
                    refine ⟨5720375775503257788266285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15254335401342020768710093 5720375775503257788266285)
                    ·
                      refine ⟨2145140915813721670599857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5720375775503257788266285 2145140915813721670599857)
                      ·
                        rfl

theorem cell23_4177647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_4177647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177647 prefixEnd_4177647 := by exact prefixLift 4177647
  have htrace : WordTrace (prefixWord ++ tailWord_4177647) baseStart_4177647 baseEnd_4177647 := by
    simpa [prefixWord, tailWord_4177647, baseEnd_4177647] using wordTrace_append hprefix tailTrace_4177647
  have hstable : (prefixWord ++ tailWord_4177647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177647).length < 2 ^ (prefixWord ++ tailWord_4177647).sum := by decide
  have hdescent : baseEnd_4177647 < baseStart_4177647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177724 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_4177724 : Nat := 118140960795 + 4177724 * 2 ^ 59
def prefixEnd_4177724 : Nat := 4983230072969 + 3 ^ 40 * 4177724 * 2
def baseEnd_4177724 : Nat := 2145180453824117869337003

theorem tailTrace_4177724 : CollatzResearch.WordTrace tailWord_4177724 prefixEnd_4177724 2145180453824117869337003 := by
  unfold tailWord_4177724
  simp only [CollatzResearch.WordTrace]
  refine ⟨76187056158413460649898113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101582741544551280866530817 76187056158413460649898113)
  ·
    refine ⟨57140292118810095487423585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76187056158413460649898113 57140292118810095487423585)
    ·
      refine ⟨42855219089107571615567689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57140292118810095487423585 42855219089107571615567689)
      ·
        refine ⟨32141414316830678711675767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42855219089107571615567689 32141414316830678711675767)
        ·
          refine ⟨48212121475246018067513651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32141414316830678711675767 48212121475246018067513651)
          ·
            refine ⟨72318182212869027101270477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48212121475246018067513651 72318182212869027101270477)
            ·
              refine ⟨27119318329825885162976429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72318182212869027101270477 27119318329825885162976429)
              ·
                refine ⟨10169744373684706936116161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27119318329825885162976429 10169744373684706936116161)
                ·
                  refine ⟨7627308280263530202087121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10169744373684706936116161 7627308280263530202087121)
                  ·
                    refine ⟨5720481210197647651565341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7627308280263530202087121 5720481210197647651565341)
                    ·
                      refine ⟨2145180453824117869337003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5720481210197647651565341 2145180453824117869337003)
                      ·
                        rfl

theorem cell23_4177724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_4177724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177724 prefixEnd_4177724 := by exact prefixLift 4177724
  have htrace : WordTrace (prefixWord ++ tailWord_4177724) baseStart_4177724 baseEnd_4177724 := by
    simpa [prefixWord, tailWord_4177724, baseEnd_4177724] using wordTrace_append hprefix tailTrace_4177724
  have hstable : (prefixWord ++ tailWord_4177724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177724).length < 2 ^ (prefixWord ++ tailWord_4177724).sum := by decide
  have hdescent : baseEnd_4177724 < baseStart_4177724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177748 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_4177748 : Nat := 118140960795 + 4177748 * 2 ^ 59
def prefixEnd_4177748 : Nat := 4983230072969 + 3 ^ 40 * 4177748 * 2
def baseEnd_4177748 : Nat := 715064259119941925145631

theorem tailTrace_4177748 : CollatzResearch.WordTrace tailWord_4177748 prefixEnd_4177748 715064259119941925145631 := by
  unfold tailWord_4177748
  simp only [CollatzResearch.WordTrace]
  refine ⟨76187493834369986699334949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101583325112493315599113265 76187493834369986699334949)
  ·
    refine ⟨14285155093944372506125303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76187493834369986699334949 14285155093944372506125303)
    ·
      refine ⟨21427732640916558759187955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285155093944372506125303 21427732640916558759187955)
      ·
        refine ⟨32141598961374838138781933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21427732640916558759187955 32141598961374838138781933)
        ·
          refine ⟨12053099610515564302043225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32141598961374838138781933 12053099610515564302043225)
          ·
            refine ⟨9039824707886673226532419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12053099610515564302043225 9039824707886673226532419)
            ·
              refine ⟨13559737061830009839798629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039824707886673226532419 13559737061830009839798629)
              ·
                refine ⟨2542450699093126844962243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13559737061830009839798629 2542450699093126844962243)
                ·
                  refine ⟨3813676048639690267443365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542450699093126844962243 3813676048639690267443365)
                  ·
                    refine ⟨715064259119941925145631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813676048639690267443365 715064259119941925145631)
                    ·
                      rfl

theorem cell23_4177748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_4177748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177748 prefixEnd_4177748 := by exact prefixLift 4177748
  have htrace : WordTrace (prefixWord ++ tailWord_4177748) baseStart_4177748 baseEnd_4177748 := by
    simpa [prefixWord, tailWord_4177748, baseEnd_4177748] using wordTrace_append hprefix tailTrace_4177748
  have hstable : (prefixWord ++ tailWord_4177748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177748).length < 2 ^ (prefixWord ++ tailWord_4177748).sum := by decide
  have hdescent : baseEnd_4177748 < baseStart_4177748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177767 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4177767 : Nat := 118140960795 + 4177767 * 2 ^ 59
def prefixEnd_4177767 : Nat := 4983230072969 + 3 ^ 40 * 4177767 * 2
def baseEnd_4177767 : Nat := 2145202533492261201099305

theorem tailTrace_4177767 : CollatzResearch.WordTrace tailWord_4177767 prefixEnd_4177767 2145202533492261201099305 := by
  unfold tailWord_4177767
  simp only [CollatzResearch.WordTrace]
  refine ⟨152375680655671139643611555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101583787103780759762407703 152375680655671139643611555)
  ·
    refine ⟨228563520983506709465417333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152375680655671139643611555 228563520983506709465417333)
    ·
      refine ⟨21427830092203754012382875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228563520983506709465417333 21427830092203754012382875)
      ·
        refine ⟨32141745138305631018574313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21427830092203754012382875 32141745138305631018574313)
        ·
          refine ⟨24106308853729223263930735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32141745138305631018574313 24106308853729223263930735)
          ·
            refine ⟨36159463280593834895896103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24106308853729223263930735 36159463280593834895896103)
            ·
              refine ⟨54239194920890752343844155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36159463280593834895896103 54239194920890752343844155)
              ·
                refine ⟨81358792381336128515766233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54239194920890752343844155 81358792381336128515766233)
                ·
                  refine ⟨61019094286002096386824675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81358792381336128515766233 61019094286002096386824675)
                  ·
                    refine ⟨91528641429003144580237013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61019094286002096386824675 91528641429003144580237013)
                    ·
                      refine ⟨2145202533492261201099305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91528641429003144580237013 2145202533492261201099305)
                      ·
                        rfl

theorem cell23_4177767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4177767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177767 prefixEnd_4177767 := by exact prefixLift 4177767
  have htrace : WordTrace (prefixWord ++ tailWord_4177767) baseStart_4177767 baseEnd_4177767 := by
    simpa [prefixWord, tailWord_4177767, baseEnd_4177767] using wordTrace_append hprefix tailTrace_4177767
  have hstable : (prefixWord ++ tailWord_4177767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177767).length < 2 ^ (prefixWord ++ tailWord_4177767).sum := by decide
  have hdescent : baseEnd_4177767 < baseStart_4177767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177781 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4177781 : Nat := 118140960795 + 4177781 * 2 ^ 59
def prefixEnd_4177781 : Nat := 4983230072969 + 3 ^ 40 * 4177781 * 2
def baseEnd_4177781 : Nat := 2145209722221424146324241

theorem tailTrace_4177781 : CollatzResearch.WordTrace tailWord_4177781 prefixEnd_4177781 2145209722221424146324241 := by
  unfold tailWord_4177781
  simp only [CollatzResearch.WordTrace]
  refine ⟨152376191277620420034621197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101584127518413613356414131 152376191277620420034621197)
  ·
    refine ⟨57141071729107657512982949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152376191277620420034621197 57141071729107657512982949)
    ·
      refine ⟨10713950949207685783684303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57141071729107657512982949 10713950949207685783684303)
      ·
        refine ⟨16070926423811528675526455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10713950949207685783684303 16070926423811528675526455)
        ·
          refine ⟨24106389635717293013289683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16070926423811528675526455 24106389635717293013289683)
          ·
            refine ⟨36159584453575939519934525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24106389635717293013289683 36159584453575939519934525)
            ·
              refine ⟨13559844170090977319975447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36159584453575939519934525 13559844170090977319975447)
              ·
                refine ⟨20339766255136465979963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13559844170090977319975447 20339766255136465979963171)
                ·
                  refine ⟨30509649382704698969944757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20339766255136465979963171 30509649382704698969944757)
                  ·
                    refine ⟨2860279629628565528432321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30509649382704698969944757 2860279629628565528432321)
                    ·
                      refine ⟨2145209722221424146324241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860279629628565528432321 2145209722221424146324241)
                      ·
                        rfl

theorem cell23_4177781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4177781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177781 prefixEnd_4177781 := by exact prefixLift 4177781
  have htrace : WordTrace (prefixWord ++ tailWord_4177781) baseStart_4177781 baseEnd_4177781 := by
    simpa [prefixWord, tailWord_4177781, baseEnd_4177781] using wordTrace_append hprefix tailTrace_4177781
  have hstable : (prefixWord ++ tailWord_4177781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177781).length < 2 ^ (prefixWord ++ tailWord_4177781).sum := by decide
  have hdescent : baseEnd_4177781 < baseStart_4177781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177821 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_4177821 : Nat := 118140960795 + 4177821 * 2 ^ 59
def prefixEnd_4177821 : Nat := 4983230072969 + 3 ^ 40 * 4177821 * 2
def baseEnd_4177821 : Nat := 715076753815867996608019

theorem tailTrace_4177821 : CollatzResearch.WordTrace tailWord_4177821 prefixEnd_4177821 715076753815867996608019 := by
  unfold tailWord_4177821
  simp only [CollatzResearch.WordTrace]
  refine ⟨152377650197475506866077317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101585100131650337910718211 152377650197475506866077317)
  ·
    refine ⟨28570809412026657537389497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152377650197475506866077317 28570809412026657537389497)
    ·
      refine ⟨21428107059019993153042123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28570809412026657537389497 21428107059019993153042123)
      ·
        refine ⟨32142160588529989729563185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21428107059019993153042123 32142160588529989729563185)
        ·
          refine ⟨24106620441397492297172389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32142160588529989729563185 24106620441397492297172389)
          ·
            refine ⟨4519991332762029805719823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24106620441397492297172389 4519991332762029805719823)
            ·
              refine ⟨6779986999143044708579735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519991332762029805719823 6779986999143044708579735)
              ·
                refine ⟨10169980498714567062869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779986999143044708579735 10169980498714567062869603)
                ·
                  refine ⟨15254970748071850594304405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10169980498714567062869603 15254970748071850594304405)
                  ·
                    refine ⟨715076753815867996608019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15254970748071850594304405 715076753815867996608019)
                    ·
                      rfl

theorem cell23_4177821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_4177821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177821 prefixEnd_4177821 := by exact prefixLift 4177821
  have htrace : WordTrace (prefixWord ++ tailWord_4177821) baseStart_4177821 baseEnd_4177821 := by
    simpa [prefixWord, tailWord_4177821, baseEnd_4177821] using wordTrace_append hprefix tailTrace_4177821
  have hstable : (prefixWord ++ tailWord_4177821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177821).length < 2 ^ (prefixWord ++ tailWord_4177821).sum := by decide
  have hdescent : baseEnd_4177821 < baseStart_4177821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177828 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_4177828 : Nat := 118140960795 + 4177828 * 2 ^ 59
def prefixEnd_4177828 : Nat := 4983230072969 + 3 ^ 40 * 4177828 * 2
def baseEnd_4177828 : Nat := 2145233855812185462436525

theorem tailTrace_4177828 : CollatzResearch.WordTrace tailWord_4177828 prefixEnd_4177828 2145233855812185462436525 := by
  unfold tailWord_4177828
  simp only [CollatzResearch.WordTrace]
  refine ⟨76188952754225073530791069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101585270338966764707721425 76188952754225073530791069)
  ·
    refine ⟨28570857282834402574046651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76188952754225073530791069 28570857282834402574046651)
    ·
      refine ⟨42856285924251603861069977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28570857282834402574046651 42856285924251603861069977)
      ·
        refine ⟨32142214443188702895802483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42856285924251603861069977 32142214443188702895802483)
        ·
          refine ⟨48213321664783054343703725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32142214443188702895802483 48213321664783054343703725)
          ·
            refine ⟨18079995624293645378888897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48213321664783054343703725 18079995624293645378888897)
            ·
              refine ⟨13559996718220234034166673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18079995624293645378888897 13559996718220234034166673)
              ·
                refine ⟨10169997538665175525625005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13559996718220234034166673 10169997538665175525625005)
                ·
                  refine ⟨3813749076999440822109377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10169997538665175525625005 3813749076999440822109377)
                  ·
                    refine ⟨2860311807749580616582033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3813749076999440822109377 2860311807749580616582033)
                    ·
                      refine ⟨2145233855812185462436525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860311807749580616582033 2145233855812185462436525)
                      ·
                        rfl

theorem cell23_4177828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_4177828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177828 prefixEnd_4177828 := by exact prefixLift 4177828
  have htrace : WordTrace (prefixWord ++ tailWord_4177828) baseStart_4177828 baseEnd_4177828 := by
    simpa [prefixWord, tailWord_4177828, baseEnd_4177828] using wordTrace_append hprefix tailTrace_4177828
  have hstable : (prefixWord ++ tailWord_4177828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177828).length < 2 ^ (prefixWord ++ tailWord_4177828).sum := by decide
  have hdescent : baseEnd_4177828 < baseStart_4177828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177847 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 9]
def baseStart_4177847 : Nat := 118140960795 + 4177847 * 2 ^ 59
def prefixEnd_4177847 : Nat := 4983230072969 + 3 ^ 40 * 4177847 * 2
def baseEnd_4177847 : Nat := 715081203981540296032979

theorem tailTrace_4177847 : CollatzResearch.WordTrace tailWord_4177847 prefixEnd_4177847 715081203981540296032979 := by
  unfold tailWord_4177847
  simp only [CollatzResearch.WordTrace]
  refine ⟨152378598495381313306523795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101585732330254208871015863 152378598495381313306523795)
  ·
    refine ⟨228567897743071969959785693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152378598495381313306523795 228567897743071969959785693)
    ·
      refine ⟨85712961653651988734919635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228567897743071969959785693 85712961653651988734919635)
      ·
        refine ⟨128569442480477983102379453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85712961653651988734919635 128569442480477983102379453)
        ·
          refine ⟨48213540930179243663392295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128569442480477983102379453 48213540930179243663392295)
          ·
            refine ⟨72320311395268865495088443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48213540930179243663392295 72320311395268865495088443)
            ·
              refine ⟨108480467092903298242632665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72320311395268865495088443 108480467092903298242632665)
              ·
                refine ⟨81360350319677473681974499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108480467092903298242632665 81360350319677473681974499)
                ·
                  refine ⟨122040525479516210522961749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81360350319677473681974499 122040525479516210522961749)
                  ·
                    refine ⟨715081203981540296032979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 122040525479516210522961749 715081203981540296032979)
                    ·
                      rfl

theorem cell23_4177847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_4177847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177847 prefixEnd_4177847 := by exact prefixLift 4177847
  have htrace : WordTrace (prefixWord ++ tailWord_4177847) baseStart_4177847 baseEnd_4177847 := by
    simpa [prefixWord, tailWord_4177847, baseEnd_4177847] using wordTrace_append hprefix tailTrace_4177847
  have hstable : (prefixWord ++ tailWord_4177847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177847).length < 2 ^ (prefixWord ++ tailWord_4177847).sum := by decide
  have hdescent : baseEnd_4177847 < baseStart_4177847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177871 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 3, 3, 2]
def baseStart_4177871 : Nat := 118140960795 + 4177871 * 2 ^ 59
def prefixEnd_4177871 : Nat := 4983230072969 + 3 ^ 40 * 4177871 * 2
def baseEnd_4177871 : Nat := 2145255935480328794198827

theorem tailTrace_4177871 : CollatzResearch.WordTrace tailWord_4177871 prefixEnd_4177871 2145255935480328794198827 := by
  unfold tailWord_4177871
  simp only [CollatzResearch.WordTrace]
  refine ⟨152379473847294365405397467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101586315898196243603598311 152379473847294365405397467)
  ·
    refine ⟨228569210770941548108096201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152379473847294365405397467 228569210770941548108096201)
    ·
      refine ⟨171426908078206161081072151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228569210770941548108096201 171426908078206161081072151)
      ·
        refine ⟨257140362117309241621608227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171426908078206161081072151 257140362117309241621608227)
        ·
          refine ⟨385710543175963862432412341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257140362117309241621608227 385710543175963862432412341)
          ·
            refine ⟨36160363422746612103038657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 385710543175963862432412341 36160363422746612103038657)
            ·
              refine ⟨27120272567059959077278993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36160363422746612103038657 27120272567059959077278993)
              ·
                refine ⟨20340204425294969307959245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27120272567059959077278993 20340204425294969307959245)
                ·
                  refine ⟨7627576659485613490484717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20340204425294969307959245 7627576659485613490484717)
                  ·
                    refine ⟨2860341247307105058931769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7627576659485613490484717 2860341247307105058931769)
                    ·
                      refine ⟨2145255935480328794198827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860341247307105058931769 2145255935480328794198827)
                      ·
                        rfl

theorem cell23_4177871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3, 2].length) (baseStart_4177871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177871 prefixEnd_4177871 := by exact prefixLift 4177871
  have htrace : WordTrace (prefixWord ++ tailWord_4177871) baseStart_4177871 baseEnd_4177871 := by
    simpa [prefixWord, tailWord_4177871, baseEnd_4177871] using wordTrace_append hprefix tailTrace_4177871
  have hstable : (prefixWord ++ tailWord_4177871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177871).length < 2 ^ (prefixWord ++ tailWord_4177871).sum := by decide
  have hdescent : baseEnd_4177871 < baseStart_4177871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177904 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_4177904 : Nat := 118140960795 + 4177904 * 2 ^ 59
def prefixEnd_4177904 : Nat := 4983230072969 + 3 ^ 40 * 4177904 * 2
def baseEnd_4177904 : Nat := 2145272880341927165086175

theorem tailTrace_4177904 : CollatzResearch.WordTrace tailWord_4177904 prefixEnd_4177904 2145272880341927165086175 := by
  unfold tailWord_4177904
  simp only [CollatzResearch.WordTrace]
  refine ⟨76190338728087406020674383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101587118304116541360899177 76190338728087406020674383)
  ·
    refine ⟨114285508092131109031011575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76190338728087406020674383 114285508092131109031011575)
    ·
      refine ⟨171428262138196663546517363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114285508092131109031011575 171428262138196663546517363)
      ·
        refine ⟨257142393207294995319776045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171428262138196663546517363 257142393207294995319776045)
        ·
          refine ⟨96428397452735623244916017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257142393207294995319776045 96428397452735623244916017)
          ·
            refine ⟨72321298089551717433687013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96428397452735623244916017 72321298089551717433687013)
            ·
              refine ⟨13560243391790947018816315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72321298089551717433687013 13560243391790947018816315)
              ·
                refine ⟨20340365087686420528224473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560243391790947018816315 20340365087686420528224473)
                ·
                  refine ⟨15255273815764815396168355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20340365087686420528224473 15255273815764815396168355)
                  ·
                    refine ⟨22882910723647223094252533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15255273815764815396168355 22882910723647223094252533)
                    ·
                      refine ⟨2145272880341927165086175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22882910723647223094252533 2145272880341927165086175)
                      ·
                        rfl

theorem cell23_4177904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_4177904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177904 prefixEnd_4177904 := by exact prefixLift 4177904
  have htrace : WordTrace (prefixWord ++ tailWord_4177904) baseStart_4177904 baseEnd_4177904 := by
    simpa [prefixWord, tailWord_4177904, baseEnd_4177904] using wordTrace_append hprefix tailTrace_4177904
  have hstable : (prefixWord ++ tailWord_4177904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177904).length < 2 ^ (prefixWord ++ tailWord_4177904).sum := by decide
  have hdescent : baseEnd_4177904 < baseStart_4177904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177941 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 7]
def baseStart_4177941 : Nat := 118140960795 + 4177941 * 2 ^ 59
def prefixEnd_4177941 : Nat := 4983230072969 + 3 ^ 40 * 4177941 * 2
def baseEnd_4177941 : Nat := 238365764347349280035945

theorem tailTrace_4177941 : CollatzResearch.WordTrace tailWord_4177941 prefixEnd_4177941 238365764347349280035945 := by
  unfold tailWord_4177941
  simp only [CollatzResearch.WordTrace]
  refine ⟨152382026957040767360445677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101588017971360511573630451 152382026957040767360445677)
  ·
    refine ⟨57143260108890287760167129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152382026957040767360445677 57143260108890287760167129)
    ·
      refine ⟨42857445081667715820125347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57143260108890287760167129 42857445081667715820125347)
      ·
        refine ⟨64286167622501573730188021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42857445081667715820125347 64286167622501573730188021)
        ·
          refine ⟨6026828214609522537205127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64286167622501573730188021 6026828214609522537205127)
          ·
            refine ⟨9040242321914283805807691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026828214609522537205127 9040242321914283805807691)
            ·
              refine ⟨13560363482871425708711537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040242321914283805807691 13560363482871425708711537)
              ·
                refine ⟨10170272612153569281533653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560363482871425708711537 10170272612153569281533653)
                ·
                  refine ⟨238365764347349280035945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10170272612153569281533653 238365764347349280035945)
                  ·
                    rfl

theorem cell23_4177941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_4177941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177941 prefixEnd_4177941 := by exact prefixLift 4177941
  have htrace : WordTrace (prefixWord ++ tailWord_4177941) baseStart_4177941 baseEnd_4177941 := by
    simpa [prefixWord, tailWord_4177941, baseEnd_4177941] using wordTrace_append hprefix tailTrace_4177941
  have hstable : (prefixWord ++ tailWord_4177941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177941).length < 2 ^ (prefixWord ++ tailWord_4177941).sum := by decide
  have hdescent : baseEnd_4177941 < baseStart_4177941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177964 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_4177964 : Nat := 118140960795 + 4177964 * 2 ^ 59
def prefixEnd_4177964 : Nat := 4983230072969 + 3 ^ 40 * 4177964 * 2
def baseEnd_4177964 : Nat := 2145303689181196930335899

theorem tailTrace_4177964 : CollatzResearch.WordTrace tailWord_4177964 prefixEnd_4177964 2145303689181196930335899 := by
  unfold tailWord_4177964
  simp only [CollatzResearch.WordTrace]
  refine ⟨76191432917978721144266473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101588577223971628192355297 76191432917978721144266473)
  ·
    refine ⟨57143574688484040858199855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76191432917978721144266473 57143574688484040858199855)
    ·
      refine ⟨85715362032726061287299783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57143574688484040858199855 85715362032726061287299783)
      ·
        refine ⟨128573043049089091930949675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85715362032726061287299783 128573043049089091930949675)
        ·
          refine ⟨192859564573633637896424513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128573043049089091930949675 192859564573633637896424513)
          ·
            refine ⟨144644673430225228422318385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192859564573633637896424513 144644673430225228422318385)
            ·
              refine ⟨108483505072668921316738789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144644673430225228422318385 108483505072668921316738789)
              ·
                refine ⟨20340657201125422746888523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108483505072668921316738789 20340657201125422746888523)
                ·
                  refine ⟨30510985801688134120332785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20340657201125422746888523 30510985801688134120332785)
                  ·
                    refine ⟨22883239351266100590249589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30510985801688134120332785 22883239351266100590249589)
                    ·
                      refine ⟨2145303689181196930335899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22883239351266100590249589 2145303689181196930335899)
                      ·
                        rfl

theorem cell23_4177964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_4177964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4177964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4177964 prefixEnd_4177964 := by exact prefixLift 4177964
  have htrace : WordTrace (prefixWord ++ tailWord_4177964) baseStart_4177964 baseEnd_4177964 := by
    simpa [prefixWord, tailWord_4177964, baseEnd_4177964] using wordTrace_append hprefix tailTrace_4177964
  have hstable : (prefixWord ++ tailWord_4177964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177964).length < 2 ^ (prefixWord ++ tailWord_4177964).sum := by decide
  have hdescent : baseEnd_4177964 < baseStart_4177964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178028 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_4178028 : Nat := 118140960795 + 4178028 * 2 ^ 59
def prefixEnd_4178028 : Nat := 4983230072969 + 3 ^ 40 * 4178028 * 2
def baseEnd_4178028 : Nat := 2145336551943084679935605

theorem tailTrace_4178028 : CollatzResearch.WordTrace tailWord_4178028 prefixEnd_4178028 2145336551943084679935605 := by
  unfold tailWord_4178028
  simp only [CollatzResearch.WordTrace]
  refine ⟨76192600053862790609431369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101590133405150387479241825 76192600053862790609431369)
  ·
    refine ⟨57144450040397092957073527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76192600053862790609431369 57144450040397092957073527)
    ·
      refine ⟨85716675060595639435610291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57144450040397092957073527 85716675060595639435610291)
      ·
        refine ⟨128575012590893459153415437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85716675060595639435610291 128575012590893459153415437)
        ·
          refine ⟨48215629721585047182530789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128575012590893459153415437 48215629721585047182530789)
          ·
            refine ⟨9040430572797196346724523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48215629721585047182530789 9040430572797196346724523)
            ·
              refine ⟨13560645859195794520086785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040430572797196346724523 13560645859195794520086785)
              ·
                refine ⟨10170484394396845890065089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560645859195794520086785 10170484394396845890065089)
                ·
                  refine ⟨7627863295797634417548817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10170484394396845890065089 7627863295797634417548817)
                  ·
                    refine ⟨5720897471848225813161613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7627863295797634417548817 5720897471848225813161613)
                    ·
                      refine ⟨2145336551943084679935605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5720897471848225813161613 2145336551943084679935605)
                      ·
                        rfl

theorem cell23_4178028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_4178028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178028 prefixEnd_4178028 := by exact prefixLift 4178028
  have htrace : WordTrace (prefixWord ++ tailWord_4178028) baseStart_4178028 baseEnd_4178028 := by
    simpa [prefixWord, tailWord_4178028, baseEnd_4178028] using wordTrace_append hprefix tailTrace_4178028
  have hstable : (prefixWord ++ tailWord_4178028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178028).length < 2 ^ (prefixWord ++ tailWord_4178028).sum := by decide
  have hdescent : baseEnd_4178028 < baseStart_4178028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178091 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 10, 4]
def baseStart_4178091 : Nat := 118140960795 + 4178091 * 2 ^ 59
def prefixEnd_4178091 : Nat := 4983230072969 + 3 ^ 40 * 4178091 * 2
def baseEnd_4178091 : Nat := 715122967074772644482605

theorem tailTrace_4178091 : CollatzResearch.WordTrace tailWord_4178091 prefixEnd_4178091 715122967074772644482605 := by
  unfold tailWord_4178091
  simp only [CollatzResearch.WordTrace]
  refine ⟨152387497906497342978406127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101591665270998228652270751 152387497906497342978406127)
  ·
    refine ⟨228581246859746014467609191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152387497906497342978406127 228581246859746014467609191)
    ·
      refine ⟨342871870289619021701413787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228581246859746014467609191 342871870289619021701413787)
      ·
        refine ⟨514307805434428532552120681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342871870289619021701413787 514307805434428532552120681)
        ·
          refine ⟨385730854075821399414090511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514307805434428532552120681 385730854075821399414090511)
          ·
            refine ⟨578596281113732099121135767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385730854075821399414090511 578596281113732099121135767)
            ·
              refine ⟨867894421670598148681703651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578596281113732099121135767 867894421670598148681703651)
              ·
                refine ⟨1301841632505897223022555477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867894421670598148681703651 1301841632505897223022555477)
                ·
                  refine ⟨3813989157732120770573893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1301841632505897223022555477 3813989157732120770573893)
                  ·
                    refine ⟨715122967074772644482605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813989157732120770573893 715122967074772644482605)
                    ·
                      rfl

theorem cell23_4178091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 4].length) (baseStart_4178091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178091 prefixEnd_4178091 := by exact prefixLift 4178091
  have htrace : WordTrace (prefixWord ++ tailWord_4178091) baseStart_4178091 baseEnd_4178091 := by
    simpa [prefixWord, tailWord_4178091, baseEnd_4178091] using wordTrace_append hprefix tailTrace_4178091
  have hstable : (prefixWord ++ tailWord_4178091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178091).length < 2 ^ (prefixWord ++ tailWord_4178091).sum := by decide
  have hdescent : baseEnd_4178091 < baseStart_4178091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178149 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4178149 : Nat := 118140960795 + 4178149 * 2 ^ 59
def prefixEnd_4178149 : Nat := 4983230072969 + 3 ^ 40 * 4178149 * 2
def baseEnd_4178149 : Nat := 2145398683102278706522549

theorem tailTrace_4178149 : CollatzResearch.WordTrace tailWord_4178149 prefixEnd_4178149 2145398683102278706522549 := by
  unfold tailWord_4178149
  simp only [CollatzResearch.WordTrace]
  refine ⟨152389613340287218884017501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101593075560191479256011667 152389613340287218884017501)
  ·
    refine ⟨57146105002607707081506563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152389613340287218884017501 57146105002607707081506563)
    ·
      refine ⟨85719157503911560622259845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57146105002607707081506563 85719157503911560622259845)
      ·
        refine ⟨16072342031983417616673721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85719157503911560622259845 16072342031983417616673721)
        ·
          refine ⟨12054256523987563212505291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16072342031983417616673721 12054256523987563212505291)
          ·
            refine ⟨18081384785981344818757937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054256523987563212505291 18081384785981344818757937)
            ·
              refine ⟨13561038589486008614068453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18081384785981344818757937 13561038589486008614068453)
              ·
                refine ⟨2542694735528626615137835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13561038589486008614068453 2542694735528626615137835)
                ·
                  refine ⟨3814042103292939922706753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542694735528626615137835 3814042103292939922706753)
                  ·
                    refine ⟨2860531577469704942030065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3814042103292939922706753 2860531577469704942030065)
                    ·
                      refine ⟨2145398683102278706522549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860531577469704942030065 2145398683102278706522549)
                      ·
                        rfl

theorem cell23_4178149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4178149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178149 prefixEnd_4178149 := by exact prefixLift 4178149
  have htrace : WordTrace (prefixWord ++ tailWord_4178149) baseStart_4178149 baseEnd_4178149 := by
    simpa [prefixWord, tailWord_4178149, baseEnd_4178149] using wordTrace_append hprefix tailTrace_4178149
  have hstable : (prefixWord ++ tailWord_4178149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178149).length < 2 ^ (prefixWord ++ tailWord_4178149).sum := by decide
  have hdescent : baseEnd_4178149 < baseStart_4178149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178181 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_4178181 : Nat := 118140960795 + 4178181 * 2 ^ 59
def prefixEnd_4178181 : Nat := 4983230072969 + 3 ^ 40 * 4178181 * 2
def baseEnd_4178181 : Nat := 715138371494407527107467

theorem tailTrace_4178181 : CollatzResearch.WordTrace tailWord_4178181 prefixEnd_4178181 715138371494407527107467 := by
  unfold tailWord_4178181
  simp only [CollatzResearch.WordTrace]
  refine ⟨152390780476171288349182397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101593853650780858899454931 152390780476171288349182397)
  ·
    refine ⟨57146542678564233130943399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152390780476171288349182397 57146542678564233130943399)
    ·
      refine ⟨85719814017846349696415099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57146542678564233130943399 85719814017846349696415099)
      ·
        refine ⟨128579721026769524544622649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85719814017846349696415099 128579721026769524544622649)
        ·
          refine ⟨96434790770077143408466987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128579721026769524544622649 96434790770077143408466987)
          ·
            refine ⟨144652186155115715112700481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96434790770077143408466987 144652186155115715112700481)
            ·
              refine ⟨108489139616336786334525361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144652186155115715112700481 108489139616336786334525361)
              ·
                refine ⟨81366854712252589750894021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108489139616336786334525361 81366854712252589750894021)
                ·
                  refine ⟨15256285258547360578292629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81366854712252589750894021 15256285258547360578292629)
                  ·
                    refine ⟨715138371494407527107467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15256285258547360578292629 715138371494407527107467)
                    ·
                      rfl

theorem cell23_4178181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_4178181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178181 prefixEnd_4178181 := by exact prefixLift 4178181
  have htrace : WordTrace (prefixWord ++ tailWord_4178181) baseStart_4178181 baseEnd_4178181 := by
    simpa [prefixWord, tailWord_4178181, baseEnd_4178181] using wordTrace_append hprefix tailTrace_4178181
  have hstable : (prefixWord ++ tailWord_4178181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178181).length < 2 ^ (prefixWord ++ tailWord_4178181).sum := by decide
  have hdescent : baseEnd_4178181 < baseStart_4178181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178183 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4178183 : Nat := 118140960795 + 4178183 * 2 ^ 59
def prefixEnd_4178183 : Nat := 4983230072969 + 3 ^ 40 * 4178183 * 2
def baseEnd_4178183 : Nat := 2145416141444531573497393

theorem tailTrace_4178183 : CollatzResearch.WordTrace tailWord_4178183 prefixEnd_4178183 2145416141444531573497393 := by
  unfold tailWord_4178183
  simp only [CollatzResearch.WordTrace]
  refine ⟨152390853422164042690755203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101593902281442695127170135 152390853422164042690755203)
  ·
    refine ⟨228586280133246064036132805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152390853422164042690755203 228586280133246064036132805)
    ·
      refine ⟨42859927524983637006774901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228586280133246064036132805 42859927524983637006774901)
      ·
        refine ⟨4018118205467215969385147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42859927524983637006774901 4018118205467215969385147)
        ·
          refine ⟨6027177308200823954077721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018118205467215969385147 6027177308200823954077721)
          ·
            refine ⟨4520382981150617965558291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027177308200823954077721 4520382981150617965558291)
            ·
              refine ⟨6780574471725926948337437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520382981150617965558291 6780574471725926948337437)
              ·
                refine ⟨2542715426897222605626539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6780574471725926948337437 2542715426897222605626539)
                ·
                  refine ⟨3814073140345833908439809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542715426897222605626539 3814073140345833908439809)
                  ·
                    refine ⟨2860554855259375431329857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3814073140345833908439809 2860554855259375431329857)
                    ·
                      refine ⟨2145416141444531573497393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860554855259375431329857 2145416141444531573497393)
                      ·
                        rfl

theorem cell23_4178183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4178183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178183 prefixEnd_4178183 := by exact prefixLift 4178183
  have htrace : WordTrace (prefixWord ++ tailWord_4178183) baseStart_4178183 baseEnd_4178183 := by
    simpa [prefixWord, tailWord_4178183, baseEnd_4178183] using wordTrace_append hprefix tailTrace_4178183
  have hstable : (prefixWord ++ tailWord_4178183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178183).length < 2 ^ (prefixWord ++ tailWord_4178183).sum := by decide
  have hdescent : baseEnd_4178183 < baseStart_4178183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178216 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4178216 : Nat := 118140960795 + 4178216 * 2 ^ 59
def prefixEnd_4178216 : Nat := 4983230072969 + 3 ^ 40 * 4178216 * 2
def baseEnd_4178216 : Nat := 2145433086306129944384741

theorem tailTrace_4178216 : CollatzResearch.WordTrace tailWord_4178216 prefixEnd_4178216 2145433086306129944384741 := by
  unfold tailWord_4178216
  simp only [CollatzResearch.WordTrace]
  refine ⟨76196028515522244663353251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101594704687362992884471001 76196028515522244663353251)
  ·
    refine ⟨114294042773283366995029877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76196028515522244663353251 114294042773283366995029877)
    ·
      refine ⟨10715066509995315655784051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114294042773283366995029877 10715066509995315655784051)
      ·
        refine ⟨16072599764992973483676077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715066509995315655784051 16072599764992973483676077)
        ·
          refine ⟨6027224911872365056378529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16072599764992973483676077 6027224911872365056378529)
          ·
            refine ⟨4520418683904273792283897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027224911872365056378529 4520418683904273792283897)
            ·
              refine ⟨3390314012928205344212923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520418683904273792283897 3390314012928205344212923)
              ·
                refine ⟨5085471019392308016319385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390314012928205344212923 5085471019392308016319385)
                ·
                  refine ⟨3814103264544231012239539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5085471019392308016319385 3814103264544231012239539)
                  ·
                    refine ⟨5721154896816346518359309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814103264544231012239539 5721154896816346518359309)
                    ·
                      refine ⟨2145433086306129944384741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721154896816346518359309 2145433086306129944384741)
                      ·
                        rfl

theorem cell23_4178216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4178216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178216 prefixEnd_4178216 := by exact prefixLift 4178216
  have htrace : WordTrace (prefixWord ++ tailWord_4178216) baseStart_4178216 baseEnd_4178216 := by
    simpa [prefixWord, tailWord_4178216, baseEnd_4178216] using wordTrace_append hprefix tailTrace_4178216
  have hstable : (prefixWord ++ tailWord_4178216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178216).length < 2 ^ (prefixWord ++ tailWord_4178216).sum := by decide
  have hdescent : baseEnd_4178216 < baseStart_4178216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178226 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_4178226 : Nat := 118140960795 + 4178226 * 2 ^ 59
def prefixEnd_4178226 : Nat := 4983230072969 + 3 ^ 40 * 4178226 * 2
def baseEnd_4178226 : Nat := 2145438221112674905259695

theorem tailTrace_4178226 : CollatzResearch.WordTrace tailWord_4178226 prefixEnd_4178226 2145438221112674905259695 := by
  unfold tailWord_4178226
  simp only [CollatzResearch.WordTrace]
  refine ⟨38098105440252065258642633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101594947840672174023047021 38098105440252065258642633)
  ·
    refine ⟨28573579080189048943981975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38098105440252065258642633 28573579080189048943981975)
    ·
      refine ⟨42860368620283573415972963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28573579080189048943981975 42860368620283573415972963)
      ·
        refine ⟨64290552930425360123959445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42860368620283573415972963 64290552930425360123959445)
        ·
          refine ⟨3013619668613688755810599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64290552930425360123959445 3013619668613688755810599)
          ·
            refine ⟨4520429502920533133715899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013619668613688755810599 4520429502920533133715899)
            ·
              refine ⟨6780644254380799700573849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520429502920533133715899 6780644254380799700573849)
              ·
                refine ⟨5085483190785599775430387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6780644254380799700573849 5085483190785599775430387)
                ·
                  refine ⟨7628224786178399663145581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085483190785599775430387 7628224786178399663145581)
                  ·
                    refine ⟨2860584294816899873679593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7628224786178399663145581 2860584294816899873679593)
                    ·
                      refine ⟨2145438221112674905259695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860584294816899873679593 2145438221112674905259695)
                      ·
                        rfl

theorem cell23_4178226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_4178226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178226 prefixEnd_4178226 := by exact prefixLift 4178226
  have htrace : WordTrace (prefixWord ++ tailWord_4178226) baseStart_4178226 baseEnd_4178226 := by
    simpa [prefixWord, tailWord_4178226, baseEnd_4178226] using wordTrace_append hprefix tailTrace_4178226
  have hstable : (prefixWord ++ tailWord_4178226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178226).length < 2 ^ (prefixWord ++ tailWord_4178226).sum := by decide
  have hdescent : baseEnd_4178226 < baseStart_4178226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178231 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_4178231 : Nat := 118140960795 + 4178231 * 2 ^ 59
def prefixEnd_4178231 : Nat := 4983230072969 + 3 ^ 40 * 4178231 * 2
def baseEnd_4178231 : Nat := 2145440788515947385697171

theorem tailTrace_4178231 : CollatzResearch.WordTrace tailWord_4178231 prefixEnd_4178231 2145440788515947385697171 := by
  unfold tailWord_4178231
  simp only [CollatzResearch.WordTrace]
  refine ⟨152392604125990146888502547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101595069417326764592335031 152392604125990146888502547)
  ·
    refine ⟨228588906188985220332753821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152392604125990146888502547 228588906188985220332753821)
    ·
      refine ⟨85720839820869457624782683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228588906188985220332753821 85720839820869457624782683)
      ·
        refine ⟨128581259731304186437174025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85720839820869457624782683 128581259731304186437174025)
        ·
          refine ⟨96435944798478139827880519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128581259731304186437174025 96435944798478139827880519)
          ·
            refine ⟨144653917197717209741820779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96435944798478139827880519 144653917197717209741820779)
            ·
              refine ⟨216980875796575814612731169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144653917197717209741820779 216980875796575814612731169)
              ·
                refine ⟨162735656847431860959548377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216980875796575814612731169 162735656847431860959548377)
                ·
                  refine ⟨122051742635573895719661283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162735656847431860959548377 122051742635573895719661283)
                  ·
                    refine ⟨183077613953360843579491925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122051742635573895719661283 183077613953360843579491925)
                    ·
                      refine ⟨2145440788515947385697171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183077613953360843579491925 2145440788515947385697171)
                      ·
                        rfl

theorem cell23_4178231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_4178231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178231 prefixEnd_4178231 := by exact prefixLift 4178231
  have htrace : WordTrace (prefixWord ++ tailWord_4178231) baseStart_4178231 baseEnd_4178231 := by
    simpa [prefixWord, tailWord_4178231, baseEnd_4178231] using wordTrace_append hprefix tailTrace_4178231
  have hstable : (prefixWord ++ tailWord_4178231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178231).length < 2 ^ (prefixWord ++ tailWord_4178231).sum := by decide
  have hdescent : baseEnd_4178231 < baseStart_4178231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178308 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4178308 : Nat := 118140960795 + 4178308 * 2 ^ 59
def prefixEnd_4178308 : Nat := 4983230072969 + 3 ^ 40 * 4178308 * 2
def baseEnd_4178308 : Nat := 2145480326526343584434317

theorem tailTrace_4178308 : CollatzResearch.WordTrace tailWord_4178308 prefixEnd_4178308 2145480326526343584434317 := by
  unfold tailWord_4178308
  simp only [CollatzResearch.WordTrace]
  refine ⟨76197706273355594519527789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101596941697807459359370385 76197706273355594519527789)
  ·
    refine ⟨28574139852508347944822921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76197706273355594519527789 28574139852508347944822921)
    ·
      refine ⟨21430604889381260958617191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28574139852508347944822921 21430604889381260958617191)
      ·
        refine ⟨32145907334071891437925787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430604889381260958617191 32145907334071891437925787)
        ·
          refine ⟨48218861001107837156888681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32145907334071891437925787 48218861001107837156888681)
          ·
            refine ⟨36164145750830877867666511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48218861001107837156888681 36164145750830877867666511)
            ·
              refine ⟨54246218626246316801499767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36164145750830877867666511 54246218626246316801499767)
              ·
                refine ⟨81369327939369475202249651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54246218626246316801499767 81369327939369475202249651)
                ·
                  refine ⟨122053991909054212803374477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81369327939369475202249651 122053991909054212803374477)
                  ·
                    refine ⟨45770246965895329801265429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122053991909054212803374477 45770246965895329801265429)
                    ·
                      refine ⟨2145480326526343584434317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45770246965895329801265429 2145480326526343584434317)
                      ·
                        rfl

theorem cell23_4178308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4178308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178308 prefixEnd_4178308 := by exact prefixLift 4178308
  have htrace : WordTrace (prefixWord ++ tailWord_4178308) baseStart_4178308 baseEnd_4178308 := by
    simpa [prefixWord, tailWord_4178308, baseEnd_4178308] using wordTrace_append hprefix tailTrace_4178308
  have hstable : (prefixWord ++ tailWord_4178308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178308).length < 2 ^ (prefixWord ++ tailWord_4178308).sum := by decide
  have hdescent : baseEnd_4178308 < baseStart_4178308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178386 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_4178386 : Nat := 118140960795 + 4178386 * 2 ^ 59
def prefixEnd_4178386 : Nat := 4983230072969 + 3 ^ 40 * 4178386 * 2
def baseEnd_4178386 : Nat := 238391153113043808806551

theorem tailTrace_4178386 : CollatzResearch.WordTrace tailWord_4178386 prefixEnd_4178386 238391153113043808806551 := by
  unfold tailWord_4178386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38099564360107152090098753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101598838293619072240263341 38099564360107152090098753)
  ·
    refine ⟨28574673270080364067574065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38099564360107152090098753 28574673270080364067574065)
    ·
      refine ⟨21431004952560273050680549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28574673270080364067574065 21431004952560273050680549)
      ·
        refine ⟨4018313428605051197002603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21431004952560273050680549 4018313428605051197002603)
        ·
          refine ⟨6027470142907576795503905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018313428605051197002603 6027470142907576795503905)
          ·
            refine ⟨4520602607180682596627929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027470142907576795503905 4520602607180682596627929)
            ·
              refine ⟨3390451955385511947470947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520602607180682596627929 3390451955385511947470947)
              ·
                refine ⟨5085677933078267921206421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390451955385511947470947 5085677933078267921206421)
                ·
                  refine ⟨238391153113043808806551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5085677933078267921206421 238391153113043808806551)
                  ·
                    rfl

theorem cell23_4178386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_4178386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178386 prefixEnd_4178386 := by exact prefixLift 4178386
  have htrace : WordTrace (prefixWord ++ tailWord_4178386) baseStart_4178386 baseEnd_4178386 := by
    simpa [prefixWord, tailWord_4178386, baseEnd_4178386] using wordTrace_append hprefix tailTrace_4178386
  have hstable : (prefixWord ++ tailWord_4178386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178386).length < 2 ^ (prefixWord ++ tailWord_4178386).sum := by decide
  have hdescent : baseEnd_4178386 < baseStart_4178386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178435 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3]
def baseStart_4178435 : Nat := 118140960795 + 4178435 * 2 ^ 59
def prefixEnd_4178435 : Nat := 4983230072969 + 3 ^ 40 * 4178435 * 2
def baseEnd_4178435 : Nat := 2145545538569464587546233

theorem tailTrace_4178435 : CollatzResearch.WordTrace tailWord_4178435 prefixEnd_4178435 2145545538569464587546233 := by
  unfold tailWord_4178435
  simp only [CollatzResearch.WordTrace]
  refine ⟨152400044617251089728928759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101600029744834059819285839 152400044617251089728928759)
  ·
    refine ⟨228600066925876634593393139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152400044617251089728928759 228600066925876634593393139)
    ·
      refine ⟨342900100388814951890089709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228600066925876634593393139 342900100388814951890089709)
      ·
        refine ⟨128587537645805606958783641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342900100388814951890089709 128587537645805606958783641)
        ·
          refine ⟨96440653234354205219087731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128587537645805606958783641 96440653234354205219087731)
          ·
            refine ⟨144660979851531307828631597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96440653234354205219087731 144660979851531307828631597)
            ·
              refine ⟨54247867444324240435736849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144660979851531307828631597 54247867444324240435736849)
              ·
                refine ⟨40685900583243180326802637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54247867444324240435736849 40685900583243180326802637)
                ·
                  refine ⟨15257212718716192622550989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40685900583243180326802637 15257212718716192622550989)
                  ·
                    refine ⟨5721454769518572233456621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15257212718716192622550989 5721454769518572233456621)
                    ·
                      refine ⟨2145545538569464587546233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721454769518572233456621 2145545538569464587546233)
                      ·
                        rfl

theorem cell23_4178435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_4178435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178435 prefixEnd_4178435 := by exact prefixLift 4178435
  have htrace : WordTrace (prefixWord ++ tailWord_4178435) baseStart_4178435 baseEnd_4178435 := by
    simpa [prefixWord, tailWord_4178435, baseEnd_4178435] using wordTrace_append hprefix tailTrace_4178435
  have hstable : (prefixWord ++ tailWord_4178435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178435).length < 2 ^ (prefixWord ++ tailWord_4178435).sum := by decide
  have hdescent : baseEnd_4178435 < baseStart_4178435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178465 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4178465 : Nat := 118140960795 + 4178465 * 2 ^ 59
def prefixEnd_4178465 : Nat := 4983230072969 + 3 ^ 40 * 4178465 * 2
def baseEnd_4178465 : Nat := 2145560942989099470171095

theorem tailTrace_4178465 : CollatzResearch.WordTrace tailWord_4178465 prefixEnd_4178465 2145560942989099470171095 := by
  unfold tailWord_4178465
  simp only [CollatzResearch.WordTrace]
  refine ⟨152401138807142404852520849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101600759204761603235013899 152401138807142404852520849)
  ·
    refine ⟨114300854105356803639390637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152401138807142404852520849 114300854105356803639390637)
    ·
      refine ⟨42862820289508801364771489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114300854105356803639390637 42862820289508801364771489)
      ·
        refine ⟨32147115217131601023578617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42862820289508801364771489 32147115217131601023578617)
        ·
          refine ⟨24110336412848700767683963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32147115217131601023578617 24110336412848700767683963)
          ·
            refine ⟨36165504619273051151525945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24110336412848700767683963 36165504619273051151525945)
            ·
              refine ⟨27124128464454788363644459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36165504619273051151525945 27124128464454788363644459)
              ·
                refine ⟨40686192696682182545466689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27124128464454788363644459 40686192696682182545466689)
                ·
                  refine ⟨30514644522511636909100017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40686192696682182545466689 30514644522511636909100017)
                  ·
                    refine ⟨22885983391883727681825013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30514644522511636909100017 22885983391883727681825013)
                    ·
                      refine ⟨2145560942989099470171095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22885983391883727681825013 2145560942989099470171095)
                      ·
                        rfl

theorem cell23_4178465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4178465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178465 prefixEnd_4178465 := by exact prefixLift 4178465
  have htrace : WordTrace (prefixWord ++ tailWord_4178465) baseStart_4178465 baseEnd_4178465 := by
    simpa [prefixWord, tailWord_4178465, baseEnd_4178465] using wordTrace_append hprefix tailTrace_4178465
  have hstable : (prefixWord ++ tailWord_4178465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178465).length < 2 ^ (prefixWord ++ tailWord_4178465).sum := by decide
  have hdescent : baseEnd_4178465 < baseStart_4178465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178485 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_4178485 : Nat := 118140960795 + 4178485 * 2 ^ 59
def prefixEnd_4178485 : Nat := 4983230072969 + 3 ^ 40 * 4178485 * 2
def baseEnd_4178485 : Nat := 715190404200729797307001

theorem tailTrace_4178485 : CollatzResearch.WordTrace tailWord_4178485 prefixEnd_4178485 715190404200729797307001 := by
  unfold tailWord_4178485
  simp only [CollatzResearch.WordTrace]
  refine ⟨152401868267069948268248909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101601245511379965512165939 152401868267069948268248909)
  ·
    refine ⟨57150700600151230600593341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152401868267069948268248909 57150700600151230600593341)
    ·
      refine ⟨21431512725056711475222503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57150700600151230600593341 21431512725056711475222503)
      ·
        refine ⟨32147269087585067212833755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21431512725056711475222503 32147269087585067212833755)
        ·
          refine ⟨48220903631377600819250633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32147269087585067212833755 48220903631377600819250633)
          ·
            refine ⟨36165677723533200614437975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48220903631377600819250633 36165677723533200614437975)
            ·
              refine ⟨54248516585299800921656963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36165677723533200614437975 54248516585299800921656963)
              ·
                refine ⟨81372774877949701382485445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54248516585299800921656963 81372774877949701382485445)
                ·
                  refine ⟨15257395289615569009216021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81372774877949701382485445 15257395289615569009216021)
                  ·
                    refine ⟨715190404200729797307001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15257395289615569009216021 715190404200729797307001)
                    ·
                      rfl

theorem cell23_4178485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_4178485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178485 prefixEnd_4178485 := by exact prefixLift 4178485
  have htrace : WordTrace (prefixWord ++ tailWord_4178485) baseStart_4178485 baseEnd_4178485 := by
    simpa [prefixWord, tailWord_4178485, baseEnd_4178485] using wordTrace_append hprefix tailTrace_4178485
  have hstable : (prefixWord ++ tailWord_4178485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178485).length < 2 ^ (prefixWord ++ tailWord_4178485).sum := by decide
  have hdescent : baseEnd_4178485 < baseStart_4178485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178486 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4178486 : Nat := 118140960795 + 4178486 * 2 ^ 59
def prefixEnd_4178486 : Nat := 4983230072969 + 3 ^ 40 * 4178486 * 2
def baseEnd_4178486 : Nat := 2145571726082843888008499

theorem tailTrace_4178486 : CollatzResearch.WordTrace tailWord_4178486 prefixEnd_4178486 2145571726082843888008499 := by
  unfold tailWord_4178486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525119046254145339939707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101601269826710883626023541 9525119046254145339939707)
  ·
    refine ⟨14287678569381218009909561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9525119046254145339939707 14287678569381218009909561)
    ·
      refine ⟨10715758927035913507432171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14287678569381218009909561 10715758927035913507432171)
      ·
        refine ⟨16073638390553870261148257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715758927035913507432171 16073638390553870261148257)
        ·
          refine ⟨12055228792915402695861193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16073638390553870261148257 12055228792915402695861193)
          ·
            refine ⟨9041421594686552021895895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055228792915402695861193 9041421594686552021895895)
            ·
              refine ⟨13562132392029828032843843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041421594686552021895895 13562132392029828032843843)
              ·
                refine ⟨20343198588044742049265765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562132392029828032843843 20343198588044742049265765)
                ·
                  refine ⟨3814349735258389134237331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20343198588044742049265765 3814349735258389134237331)
                  ·
                    refine ⟨5721524602887583701355997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814349735258389134237331 5721524602887583701355997)
                    ·
                      refine ⟨2145571726082843888008499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721524602887583701355997 2145571726082843888008499)
                      ·
                        rfl

theorem cell23_4178486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4178486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178486 prefixEnd_4178486 := by exact prefixLift 4178486
  have htrace : WordTrace (prefixWord ++ tailWord_4178486) baseStart_4178486 baseEnd_4178486 := by
    simpa [prefixWord, tailWord_4178486, baseEnd_4178486] using wordTrace_append hprefix tailTrace_4178486
  have hstable : (prefixWord ++ tailWord_4178486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178486).length < 2 ^ (prefixWord ++ tailWord_4178486).sum := by decide
  have hdescent : baseEnd_4178486 < baseStart_4178486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178500 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4178500 : Nat := 118140960795 + 4178500 * 2 ^ 59
def prefixEnd_4178500 : Nat := 4983230072969 + 3 ^ 40 * 4178500 * 2
def baseEnd_4178500 : Nat := 2145578914812006833233435

theorem tailTrace_4178500 : CollatzResearch.WordTrace tailWord_4178500 prefixEnd_4178500 2145578914812006833233435 := by
  unfold tailWord_4178500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76201207681007802915022477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101601610241343737220029969 76201207681007802915022477)
  ·
    refine ⟨28575452880377926093133429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76201207681007802915022477 28575452880377926093133429)
    ·
      refine ⟨2678948707535430571231259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28575452880377926093133429 2678948707535430571231259)
      ·
        refine ⟨4018423061303145856846889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678948707535430571231259 4018423061303145856846889)
        ·
          refine ⟨3013817295977359392635167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018423061303145856846889 3013817295977359392635167)
          ·
            refine ⟨4520725943966039088952751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013817295977359392635167 4520725943966039088952751)
            ·
              refine ⟨6781088915949058633429127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520725943966039088952751 6781088915949058633429127)
              ·
                refine ⟨10171633373923587950143691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781088915949058633429127 10171633373923587950143691)
                ·
                  refine ⟨15257450060885381925215537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171633373923587950143691 15257450060885381925215537)
                  ·
                    refine ⟨11443087545664036443911653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15257450060885381925215537 11443087545664036443911653)
                    ·
                      refine ⟨2145578914812006833233435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11443087545664036443911653 2145578914812006833233435)
                      ·
                        rfl

theorem cell23_4178500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4178500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178500 prefixEnd_4178500 := by exact prefixLift 4178500
  have htrace : WordTrace (prefixWord ++ tailWord_4178500) baseStart_4178500 baseEnd_4178500 := by
    simpa [prefixWord, tailWord_4178500, baseEnd_4178500] using wordTrace_append hprefix tailTrace_4178500
  have hstable : (prefixWord ++ tailWord_4178500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178500).length < 2 ^ (prefixWord ++ tailWord_4178500).sum := by decide
  have hdescent : baseEnd_4178500 < baseStart_4178500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178552 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_4178552 : Nat := 118140960795 + 4178552 * 2 ^ 59
def prefixEnd_4178552 : Nat := 4983230072969 + 3 ^ 40 * 4178552 * 2
def baseEnd_4178552 : Nat := 2145605615806040629783195

theorem tailTrace_4178552 : CollatzResearch.WordTrace tailWord_4178552 prefixEnd_4178552 2145605615806040629783195 := by
  unfold tailWord_4178552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76202155978913609355468955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101602874638551479140625273 76202155978913609355468955)
  ·
    refine ⟨114303233968370414033203433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76202155978913609355468955 114303233968370414033203433)
    ·
      refine ⟨85727425476277810524902575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114303233968370414033203433 85727425476277810524902575)
      ·
        refine ⟨128591138214416715787353863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85727425476277810524902575 128591138214416715787353863)
        ·
          refine ⟨192886707321625073681030795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128591138214416715787353863 192886707321625073681030795)
          ·
            refine ⟨289330060982437610521546193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192886707321625073681030795 289330060982437610521546193)
            ·
              refine ⟨216997545736828207891159645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289330060982437610521546193 216997545736828207891159645)
              ·
                refine ⟨81374079651310577959184867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216997545736828207891159645 81374079651310577959184867)
                ·
                  refine ⟨122061119476965866938777301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81374079651310577959184867 122061119476965866938777301)
                  ·
                    refine ⟨2860807487741387506377593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 122061119476965866938777301 2860807487741387506377593)
                    ·
                      refine ⟨2145605615806040629783195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860807487741387506377593 2145605615806040629783195)
                      ·
                        rfl

theorem cell23_4178552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_4178552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178552 prefixEnd_4178552 := by exact prefixLift 4178552
  have htrace : WordTrace (prefixWord ++ tailWord_4178552) baseStart_4178552 baseEnd_4178552 := by
    simpa [prefixWord, tailWord_4178552, baseEnd_4178552] using wordTrace_append hprefix tailTrace_4178552
  have hstable : (prefixWord ++ tailWord_4178552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178552).length < 2 ^ (prefixWord ++ tailWord_4178552).sum := by decide
  have hdescent : baseEnd_4178552 < baseStart_4178552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178630 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4178630 : Nat := 118140960795 + 4178630 * 2 ^ 59
def prefixEnd_4178630 : Nat := 4983230072969 + 3 ^ 40 * 4178630 * 2
def baseEnd_4178630 : Nat := 715215222432363774869279

theorem tailTrace_4178630 : CollatzResearch.WordTrace tailWord_4178630 prefixEnd_4178630 715215222432363774869279 := by
  unfold tailWord_4178630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762723651610769938508667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101604771234363092021518229 4762723651610769938508667)
  ·
    refine ⟨7144085477416154907763001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4762723651610769938508667 7144085477416154907763001)
    ·
      refine ⟨5358064108062116180822251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7144085477416154907763001 5358064108062116180822251)
      ·
        refine ⟨8037096162093174271233377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358064108062116180822251 8037096162093174271233377)
        ·
          refine ⟨6027822121569880703425033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037096162093174271233377 6027822121569880703425033)
          ·
            refine ⟨4520866591177410527568775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027822121569880703425033 4520866591177410527568775)
            ·
              refine ⟨6781299886766115791353163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520866591177410527568775 6781299886766115791353163)
              ·
                refine ⟨10171949830149173687029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781299886766115791353163 10171949830149173687029745)
                ·
                  refine ⟨7628962372611880265272309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171949830149173687029745 7628962372611880265272309)
                  ·
                    refine ⟨715215222432363774869279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7628962372611880265272309 715215222432363774869279)
                    ·
                      rfl

theorem cell23_4178630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4178630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178630 prefixEnd_4178630 := by exact prefixLift 4178630
  have htrace : WordTrace (prefixWord ++ tailWord_4178630) baseStart_4178630 baseEnd_4178630 := by
    simpa [prefixWord, tailWord_4178630, baseEnd_4178630] using wordTrace_append hprefix tailTrace_4178630
  have hstable : (prefixWord ++ tailWord_4178630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178630).length < 2 ^ (prefixWord ++ tailWord_4178630).sum := by decide
  have hdescent : baseEnd_4178630 < baseStart_4178630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178636 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4178636 : Nat := 118140960795 + 4178636 * 2 ^ 59
def prefixEnd_4178636 : Nat := 4983230072969 + 3 ^ 40 * 4178636 * 2
def baseEnd_4178636 : Nat := 2145648748181018301132809

theorem tailTrace_4178636 : CollatzResearch.WordTrace tailWord_4178636 prefixEnd_4178636 2145648748181018301132809 := by
  unfold tailWord_4178636
  simp only [CollatzResearch.WordTrace]
  refine ⟨76203687844761450528497881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101604917126348600704663841 76203687844761450528497881)
  ·
    refine ⟨57152765883571087896373411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76203687844761450528497881 57152765883571087896373411)
    ·
      refine ⟨85729148825356631844560117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57152765883571087896373411 85729148825356631844560117)
      ·
        refine ⟨8037107702377184235427511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85729148825356631844560117 8037107702377184235427511)
        ·
          refine ⟨12055661553565776353141267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037107702377184235427511 12055661553565776353141267)
          ·
            refine ⟨18083492330348664529711901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055661553565776353141267 18083492330348664529711901)
            ·
              refine ⟨6781309623880749198641963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18083492330348664529711901 6781309623880749198641963)
              ·
                refine ⟨10171964435821123797962945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781309623880749198641963 10171964435821123797962945)
                ·
                  refine ⟨7628973326865842848472209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171964435821123797962945 7628973326865842848472209)
                  ·
                    refine ⟨5721729995149382136354157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628973326865842848472209 5721729995149382136354157)
                    ·
                      refine ⟨2145648748181018301132809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721729995149382136354157 2145648748181018301132809)
                      ·
                        rfl

theorem cell23_4178636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4178636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178636 prefixEnd_4178636 := by exact prefixLift 4178636
  have htrace : WordTrace (prefixWord ++ tailWord_4178636) baseStart_4178636 baseEnd_4178636 := by
    simpa [prefixWord, tailWord_4178636, baseEnd_4178636] using wordTrace_append hprefix tailTrace_4178636
  have hstable : (prefixWord ++ tailWord_4178636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178636).length < 2 ^ (prefixWord ++ tailWord_4178636).sum := by decide
  have hdescent : baseEnd_4178636 < baseStart_4178636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178649 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 3]
def baseStart_4178649 : Nat := 118140960795 + 4178649 * 2 ^ 59
def prefixEnd_4178649 : Nat := 4983230072969 + 3 ^ 40 * 4178649 * 2
def baseEnd_4178649 : Nat := 2145655423429526750270249

theorem tailTrace_4178649 : CollatzResearch.WordTrace tailWord_4178649 prefixEnd_4178649 2145655423429526750270249 := by
  unfold tailWord_4178649
  simp only [CollatzResearch.WordTrace]
  refine ⟨152407849838475804277219001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101605233225650536184812667 152407849838475804277219001)
  ·
    refine ⟨114305887378856853207914251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152407849838475804277219001 114305887378856853207914251)
    ·
      refine ⟨171458831068285279811871377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114305887378856853207914251 171458831068285279811871377)
      ·
        refine ⟨128594123301213959858903533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171458831068285279811871377 128594123301213959858903533)
        ·
          refine ⟨48222796237955234947088825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128594123301213959858903533 48222796237955234947088825)
          ·
            refine ⟨36167097178466426210316619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48222796237955234947088825 36167097178466426210316619)
            ·
              refine ⟨54250645767699639315474929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36167097178466426210316619 54250645767699639315474929)
              ·
                refine ⟨40687984325774729486606197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54250645767699639315474929 40687984325774729486606197)
                ·
                  refine ⟨3814498530541380889369331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40687984325774729486606197 3814498530541380889369331)
                  ·
                    refine ⟨5721747795812071334053997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814498530541380889369331 5721747795812071334053997)
                    ·
                      refine ⟨2145655423429526750270249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721747795812071334053997 2145655423429526750270249)
                      ·
                        rfl

theorem cell23_4178649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_4178649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178649 prefixEnd_4178649 := by exact prefixLift 4178649
  have htrace : WordTrace (prefixWord ++ tailWord_4178649) baseStart_4178649 baseEnd_4178649 := by
    simpa [prefixWord, tailWord_4178649, baseEnd_4178649] using wordTrace_append hprefix tailTrace_4178649
  have hstable : (prefixWord ++ tailWord_4178649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178649).length < 2 ^ (prefixWord ++ tailWord_4178649).sum := by decide
  have hdescent : baseEnd_4178649 < baseStart_4178649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178686 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4178686 : Nat := 118140960795 + 4178686 * 2 ^ 59
def prefixEnd_4178686 : Nat := 4983230072969 + 3 ^ 40 * 4178686 * 2
def baseEnd_4178686 : Nat := 715224807404581035169193

theorem tailTrace_4178686 : CollatzResearch.WordTrace tailWord_4178686 prefixEnd_4178686 715224807404581035169193 := by
  unfold tailWord_4178686
  simp only [CollatzResearch.WordTrace]
  refine ⟨19051149917417719949539489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101606132892894506397543941 19051149917417719949539489)
  ·
    refine ⟨14288362438063289962154617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19051149917417719949539489 14288362438063289962154617)
    ·
      refine ⟨10716271828547467471615963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14288362438063289962154617 10716271828547467471615963)
      ·
        refine ⟨16074407742821201207423945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716271828547467471615963 16074407742821201207423945)
        ·
          refine ⟨12055805807115900905567959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16074407742821201207423945 12055805807115900905567959)
          ·
            refine ⟨18083708710673851358351939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055805807115900905567959 18083708710673851358351939)
            ·
              refine ⟨27125563066010777037527909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18083708710673851358351939 27125563066010777037527909)
              ·
                refine ⟨5086043074877020694536483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27125563066010777037527909 5086043074877020694536483)
                ·
                  refine ⟨7629064612315531041804725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086043074877020694536483 7629064612315531041804725)
                  ·
                    refine ⟨715224807404581035169193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7629064612315531041804725 715224807404581035169193)
                    ·
                      rfl

theorem cell23_4178686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4178686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178686 prefixEnd_4178686 := by exact prefixLift 4178686
  have htrace : WordTrace (prefixWord ++ tailWord_4178686) baseStart_4178686 baseEnd_4178686 := by
    simpa [prefixWord, tailWord_4178686, baseEnd_4178686] using wordTrace_append hprefix tailTrace_4178686
  have hstable : (prefixWord ++ tailWord_4178686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178686).length < 2 ^ (prefixWord ++ tailWord_4178686).sum := by decide
  have hdescent : baseEnd_4178686 < baseStart_4178686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178689 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_4178689 : Nat := 118140960795 + 4178689 * 2 ^ 59
def prefixEnd_4178689 : Nat := 4983230072969 + 3 ^ 40 * 4178689 * 2
def baseEnd_4178689 : Nat := 2145675962655706593770065

theorem tailTrace_4178689 : CollatzResearch.WordTrace tailWord_4178689 prefixEnd_4178689 2145675962655706593770065 := by
  unfold tailWord_4178689
  simp only [CollatzResearch.WordTrace]
  refine ⟨152409308758330891108675121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101606205838887260739116747 152409308758330891108675121)
  ·
    refine ⟨114306981568748168331506341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152409308758330891108675121 114306981568748168331506341)
    ·
      refine ⟨21432559044140281562157439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114306981568748168331506341 21432559044140281562157439)
      ·
        refine ⟨32148838566210422343236159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21432559044140281562157439 32148838566210422343236159)
        ·
          refine ⟨48223257849315633514854239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32148838566210422343236159 48223257849315633514854239)
          ·
            refine ⟨72334886773973450272281359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48223257849315633514854239 72334886773973450272281359)
            ·
              refine ⟨108502330160960175408422039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72334886773973450272281359 108502330160960175408422039)
              ·
                refine ⟨162753495241440263112633059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108502330160960175408422039 162753495241440263112633059)
                ·
                  refine ⟨244130242862160394668949589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162753495241440263112633059 244130242862160394668949589)
                  ·
                    refine ⟨2860901283540942125026753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 244130242862160394668949589 2860901283540942125026753)
                    ·
                      refine ⟨2145675962655706593770065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2860901283540942125026753 2145675962655706593770065)
                      ·
                        rfl

theorem cell23_4178689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_4178689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178689 prefixEnd_4178689 := by exact prefixLift 4178689
  have htrace : WordTrace (prefixWord ++ tailWord_4178689) baseStart_4178689 baseEnd_4178689 := by
    simpa [prefixWord, tailWord_4178689, baseEnd_4178689] using wordTrace_append hprefix tailTrace_4178689
  have hstable : (prefixWord ++ tailWord_4178689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178689).length < 2 ^ (prefixWord ++ tailWord_4178689).sum := by decide
  have hdescent : baseEnd_4178689 < baseStart_4178689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178709 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_4178709 : Nat := 118140960795 + 4178709 * 2 ^ 59
def prefixEnd_4178709 : Nat := 4983230072969 + 3 ^ 40 * 4178709 * 2
def baseEnd_4178709 : Nat := 2145686232268796515519973

theorem tailTrace_4178709 : CollatzResearch.WordTrace tailWord_4178709 prefixEnd_4178709 2145686232268796515519973 := by
  unfold tailWord_4178709
  simp only [CollatzResearch.WordTrace]
  refine ⟨152410038218258434524403181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101606692145505623016268787 152410038218258434524403181)
  ·
    refine ⟨57153764331846912946651193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152410038218258434524403181 57153764331846912946651193)
    ·
      refine ⟨42865323248885184709988395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57153764331846912946651193 42865323248885184709988395)
      ·
        refine ⟨64297984873327777064982593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42865323248885184709988395 64297984873327777064982593)
        ·
          refine ⟨48223488654995832798736945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64297984873327777064982593 48223488654995832798736945)
          ·
            refine ⟨36167616491246874599052709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48223488654995832798736945 36167616491246874599052709)
            ·
              refine ⟨6781428092108788987322383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36167616491246874599052709 6781428092108788987322383)
              ·
                refine ⟨10172142138163183480983575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781428092108788987322383 10172142138163183480983575)
                ·
                  refine ⟨15258213207244775221475363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10172142138163183480983575 15258213207244775221475363)
                  ·
                    refine ⟨22887319810867162832213045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15258213207244775221475363 22887319810867162832213045)
                    ·
                      refine ⟨2145686232268796515519973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22887319810867162832213045 2145686232268796515519973)
                      ·
                        rfl

theorem cell23_4178709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_4178709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178709 prefixEnd_4178709 := by exact prefixLift 4178709
  have htrace : WordTrace (prefixWord ++ tailWord_4178709) baseStart_4178709 baseEnd_4178709 := by
    simpa [prefixWord, tailWord_4178709, baseEnd_4178709] using wordTrace_append hprefix tailTrace_4178709
  have hstable : (prefixWord ++ tailWord_4178709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178709).length < 2 ^ (prefixWord ++ tailWord_4178709).sum := by decide
  have hdescent : baseEnd_4178709 < baseStart_4178709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178717 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4178717 : Nat := 118140960795 + 4178717 * 2 ^ 59
def prefixEnd_4178717 : Nat := 4983230072969 + 3 ^ 40 * 4178717 * 2
def baseEnd_4178717 : Nat := 2145690340114032484219937

theorem tailTrace_4178717 : CollatzResearch.WordTrace tailWord_4178717 prefixEnd_4178717 2145690340114032484219937 := by
  unfold tailWord_4178717
  simp only [CollatzResearch.WordTrace]
  refine ⟨152410330002229451890694405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101606886668152967927129603 152410330002229451890694405)
  ·
    refine ⟨28576936875418022229505201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152410330002229451890694405 28576936875418022229505201)
    ·
      refine ⟨21432702656563516672128901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28576936875418022229505201 21432702656563516672128901)
      ·
        refine ⟨4018631748105659376024169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21432702656563516672128901 4018631748105659376024169)
        ·
          refine ⟨3013973811079244532018127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018631748105659376024169 3013973811079244532018127)
          ·
            refine ⟨4520960716618866798027191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013973811079244532018127 4520960716618866798027191)
            ·
              refine ⟨6781441074928300197040787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520960716618866798027191 6781441074928300197040787)
              ·
                refine ⟨10172161612392450295561181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781441074928300197040787 10172161612392450295561181)
                ·
                  refine ⟨3814560604647168860835443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10172161612392450295561181 3814560604647168860835443)
                  ·
                    refine ⟨5721840906970753291253165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814560604647168860835443 5721840906970753291253165)
                    ·
                      refine ⟨2145690340114032484219937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721840906970753291253165 2145690340114032484219937)
                      ·
                        rfl

theorem cell23_4178717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4178717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178717 prefixEnd_4178717 := by exact prefixLift 4178717
  have htrace : WordTrace (prefixWord ++ tailWord_4178717) baseStart_4178717 baseEnd_4178717 := by
    simpa [prefixWord, tailWord_4178717, baseEnd_4178717] using wordTrace_append hprefix tailTrace_4178717
  have hstable : (prefixWord ++ tailWord_4178717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178717).length < 2 ^ (prefixWord ++ tailWord_4178717).sum := by decide
  have hdescent : baseEnd_4178717 < baseStart_4178717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178732 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_4178732 : Nat := 118140960795 + 4178732 * 2 ^ 59
def prefixEnd_4178732 : Nat := 4983230072969 + 3 ^ 40 * 4178732 * 2
def baseEnd_4178732 : Nat := 2145698042323849925532367

theorem tailTrace_4178732 : CollatzResearch.WordTrace tailWord_4178732 prefixEnd_4178732 2145698042323849925532367 := by
  unfold tailWord_4178732
  simp only [CollatzResearch.WordTrace]
  refine ⟨76205438548587554726245225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101607251398116739634993633 76205438548587554726245225)
  ·
    refine ⟨57154078911440666044683919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76205438548587554726245225 57154078911440666044683919)
    ·
      refine ⟨85731118367160999067025879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57154078911440666044683919 85731118367160999067025879)
      ·
        refine ⟨128596677550741498600538819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85731118367160999067025879 128596677550741498600538819)
        ·
          refine ⟨192895016326112247900808229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128596677550741498600538819 192895016326112247900808229)
          ·
            refine ⟨36167815561146046481401543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192895016326112247900808229 36167815561146046481401543)
            ·
              refine ⟨54251723341719069722102315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36167815561146046481401543 54251723341719069722102315)
              ·
                refine ⟨81377585012578604583153473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54251723341719069722102315 81377585012578604583153473)
                ·
                  refine ⟨61033188759433953437365105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81377585012578604583153473 61033188759433953437365105)
                  ·
                    refine ⟨45774891569575465078023829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61033188759433953437365105 45774891569575465078023829)
                    ·
                      refine ⟨2145698042323849925532367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45774891569575465078023829 2145698042323849925532367)
                      ·
                        rfl

theorem cell23_4178732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_4178732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178732 prefixEnd_4178732 := by exact prefixLift 4178732
  have htrace : WordTrace (prefixWord ++ tailWord_4178732) baseStart_4178732 baseEnd_4178732 := by
    simpa [prefixWord, tailWord_4178732, baseEnd_4178732] using wordTrace_append hprefix tailTrace_4178732
  have hstable : (prefixWord ++ tailWord_4178732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178732).length < 2 ^ (prefixWord ++ tailWord_4178732).sum := by decide
  have hdescent : baseEnd_4178732 < baseStart_4178732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178740 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4178740 : Nat := 118140960795 + 4178740 * 2 ^ 59
def prefixEnd_4178740 : Nat := 4983230072969 + 3 ^ 40 * 4178740 * 2
def baseEnd_4178740 : Nat := 2145702150169085894232331

theorem tailTrace_4178740 : CollatzResearch.WordTrace tailWord_4178740 prefixEnd_4178740 2145702150169085894232331 := by
  unfold tailWord_4178740
  simp only [CollatzResearch.WordTrace]
  refine ⟨76205584440573063409390837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101607445920764084545854449 76205584440573063409390837)
  ·
    refine ⟨7144273541303724694630391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76205584440573063409390837 7144273541303724694630391)
    ·
      refine ⟨10716410311955587041945587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144273541303724694630391 10716410311955587041945587)
      ·
        refine ⟨16074615467933380562918381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716410311955587041945587 16074615467933380562918381)
        ·
          refine ⟨6027980800475017711094393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16074615467933380562918381 6027980800475017711094393)
          ·
            refine ⟨4520985600356263283320795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027980800475017711094393 4520985600356263283320795)
            ·
              refine ⟨6781478400534394924981193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520985600356263283320795 6781478400534394924981193)
              ·
                refine ⟨5086108800400796193735895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781478400534394924981193 5086108800400796193735895)
                ·
                  refine ⟨7629163200601194290603843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086108800400796193735895 7629163200601194290603843)
                  ·
                    refine ⟨11443744800901791435905765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629163200601194290603843 11443744800901791435905765)
                    ·
                      refine ⟨2145702150169085894232331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11443744800901791435905765 2145702150169085894232331)
                      ·
                        rfl

theorem cell23_4178740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4178740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178740 prefixEnd_4178740 := by exact prefixLift 4178740
  have htrace : WordTrace (prefixWord ++ tailWord_4178740) baseStart_4178740 baseEnd_4178740 := by
    simpa [prefixWord, tailWord_4178740, baseEnd_4178740] using wordTrace_append hprefix tailTrace_4178740
  have hstable : (prefixWord ++ tailWord_4178740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178740).length < 2 ^ (prefixWord ++ tailWord_4178740).sum := by decide
  have hdescent : baseEnd_4178740 < baseStart_4178740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178752 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_4178752 : Nat := 118140960795 + 4178752 * 2 ^ 59
def prefixEnd_4178752 : Nat := 4983230072969 + 3 ^ 40 * 4178752 * 2
def baseEnd_4178752 : Nat := 2145708311936939847282275

theorem tailTrace_4178752 : CollatzResearch.WordTrace tailWord_4178752 prefixEnd_4178752 2145708311936939847282275 := by
  unfold tailWord_4178752
  simp only [CollatzResearch.WordTrace]
  refine ⟨76205803278551326434109255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101607737704735101912145673 76205803278551326434109255)
  ·
    refine ⟨114308704917826989651163883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76205803278551326434109255 114308704917826989651163883)
    ·
      refine ⟨171463057376740484476745825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114308704917826989651163883 171463057376740484476745825)
      ·
        refine ⟨128597293032555363357559369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171463057376740484476745825 128597293032555363357559369)
        ·
          refine ⟨96447969774416522518169527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128597293032555363357559369 96447969774416522518169527)
          ·
            refine ⟨144671954661624783777254291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96447969774416522518169527 144671954661624783777254291)
            ·
              refine ⟨217007931992437175665881437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144671954661624783777254291 217007931992437175665881437)
              ·
                refine ⟨81377974497163940874705539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217007931992437175665881437 81377974497163940874705539)
                ·
                  refine ⟨122066961745745911312058309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81377974497163940874705539 122066961745745911312058309)
                  ·
                    refine ⟨22887555327327358371010933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122066961745745911312058309 22887555327327358371010933)
                    ·
                      refine ⟨2145708311936939847282275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22887555327327358371010933 2145708311936939847282275)
                      ·
                        rfl

theorem cell23_4178752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_4178752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178752 prefixEnd_4178752 := by exact prefixLift 4178752
  have htrace : WordTrace (prefixWord ++ tailWord_4178752) baseStart_4178752 baseEnd_4178752 := by
    simpa [prefixWord, tailWord_4178752, baseEnd_4178752] using wordTrace_append hprefix tailTrace_4178752
  have hstable : (prefixWord ++ tailWord_4178752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178752).length < 2 ^ (prefixWord ++ tailWord_4178752).sum := by decide
  have hdescent : baseEnd_4178752 < baseStart_4178752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178753 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4178753 : Nat := 118140960795 + 4178753 * 2 ^ 59
def prefixEnd_4178753 : Nat := 4983230072969 + 3 ^ 40 * 4178753 * 2
def baseEnd_4178753 : Nat := 2145708825417594343369771

theorem tailTrace_4178753 : CollatzResearch.WordTrace tailWord_4178753 prefixEnd_4178753 2145708825417594343369771 := by
  unfold tailWord_4178753
  simp only [CollatzResearch.WordTrace]
  refine ⟨152411643030099030039004913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101607762020066020026003275 152411643030099030039004913)
  ·
    refine ⟨114308732272574272529253685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152411643030099030039004913 114308732272574272529253685)
    ·
      refine ⟨10716443650553838049617533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114308732272574272529253685 10716443650553838049617533)
      ·
        refine ⟨4018666368957689268606575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10716443650553838049617533 4018666368957689268606575)
        ·
          refine ⟨6027999553436533902909863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018666368957689268606575 6027999553436533902909863)
          ·
            refine ⟨9041999330154800854364795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027999553436533902909863 9041999330154800854364795)
            ·
              refine ⟨13562998995232201281547193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041999330154800854364795 13562998995232201281547193)
              ·
                refine ⟨10172249246424150961160395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13562998995232201281547193 10172249246424150961160395)
                ·
                  refine ⟨15258373869636226441740593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10172249246424150961160395 15258373869636226441740593)
                  ·
                    refine ⟨11443780402227169831305445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15258373869636226441740593 11443780402227169831305445)
                    ·
                      refine ⟨2145708825417594343369771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11443780402227169831305445 2145708825417594343369771)
                      ·
                        rfl

theorem cell23_4178753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4178753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178753 prefixEnd_4178753 := by exact prefixLift 4178753
  have htrace : WordTrace (prefixWord ++ tailWord_4178753) baseStart_4178753 baseEnd_4178753 := by
    simpa [prefixWord, tailWord_4178753, baseEnd_4178753] using wordTrace_append hprefix tailTrace_4178753
  have hstable : (prefixWord ++ tailWord_4178753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178753).length < 2 ^ (prefixWord ++ tailWord_4178753).sum := by decide
  have hdescent : baseEnd_4178753 < baseStart_4178753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178773 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4178773 : Nat := 118140960795 + 4178773 * 2 ^ 59
def prefixEnd_4178773 : Nat := 4983230072969 + 3 ^ 40 * 4178773 * 2
def baseEnd_4178773 : Nat := 2145719095030684265119679

theorem tailTrace_4178773 : CollatzResearch.WordTrace tailWord_4178773 prefixEnd_4178773 2145719095030684265119679 := by
  unfold tailWord_4178773
  simp only [CollatzResearch.WordTrace]
  refine ⟨152412372490026573454732973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101608248326684382303155315 152412372490026573454732973)
  ·
    refine ⟨57154639683759965045524865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152412372490026573454732973 57154639683759965045524865)
    ·
      refine ⟨42865979762819973784143649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57154639683759965045524865 42865979762819973784143649)
      ·
        refine ⟨32149484822114980338107737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42865979762819973784143649 32149484822114980338107737)
        ·
          refine ⟨24112113616586235253580803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32149484822114980338107737 24112113616586235253580803)
          ·
            refine ⟨36168170424879352880371205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24112113616586235253580803 36168170424879352880371205)
            ·
              refine ⟨6781531954664878665069601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36168170424879352880371205 6781531954664878665069601)
              ·
                refine ⟨5086148965998658998802201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781531954664878665069601 5086148965998658998802201)
                ·
                  refine ⟨3814611724498994249101651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086148965998658998802201 3814611724498994249101651)
                  ·
                    refine ⟨5721917586748491373652477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814611724498994249101651 5721917586748491373652477)
                    ·
                      refine ⟨2145719095030684265119679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5721917586748491373652477 2145719095030684265119679)
                      ·
                        rfl

theorem cell23_4178773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4178773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178773 prefixEnd_4178773 := by exact prefixLift 4178773
  have htrace : WordTrace (prefixWord ++ tailWord_4178773) baseStart_4178773 baseEnd_4178773 := by
    simpa [prefixWord, tailWord_4178773, baseEnd_4178773] using wordTrace_append hprefix tailTrace_4178773
  have hstable : (prefixWord ++ tailWord_4178773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178773).length < 2 ^ (prefixWord ++ tailWord_4178773).sum := by decide
  have hdescent : baseEnd_4178773 < baseStart_4178773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178826 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4178826 : Nat := 118140960795 + 4178826 * 2 ^ 59
def prefixEnd_4178826 : Nat := 4983230072969 + 3 ^ 40 * 4178826 * 2
def baseEnd_4178826 : Nat := 2145746309505372557756935

theorem tailTrace_4178826 : CollatzResearch.WordTrace tailWord_4178826 prefixEnd_4178826 2145746309505372557756935 := by
  unfold tailWord_4178826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38103576389708640876603083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101609537039223042337608221 38103576389708640876603083)
  ·
    refine ⟨57155364584562961314904625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38103576389708640876603083 57155364584562961314904625)
    ·
      refine ⟨42866523438422220986178469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57155364584562961314904625 42866523438422220986178469)
      ·
        refine ⟨8037473144704166434908463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42866523438422220986178469 8037473144704166434908463)
        ·
          refine ⟨12056209717056249652362695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037473144704166434908463 12056209717056249652362695)
          ·
            refine ⟨18084314575584374478544043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12056209717056249652362695 18084314575584374478544043)
            ·
              refine ⟨27126471863376561717816065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18084314575584374478544043 27126471863376561717816065)
              ·
                refine ⟨20344853897532421288362049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27126471863376561717816065 20344853897532421288362049)
                ·
                  refine ⟨15258640423149315966271537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20344853897532421288362049 15258640423149315966271537)
                  ·
                    refine ⟨11443980317361986974703653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15258640423149315966271537 11443980317361986974703653)
                    ·
                      refine ⟨2145746309505372557756935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11443980317361986974703653 2145746309505372557756935)
                      ·
                        rfl

theorem cell23_4178826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4178826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178826 prefixEnd_4178826 := by exact prefixLift 4178826
  have htrace : WordTrace (prefixWord ++ tailWord_4178826) baseStart_4178826 baseEnd_4178826 := by
    simpa [prefixWord, tailWord_4178826, baseEnd_4178826] using wordTrace_append hprefix tailTrace_4178826
  have hstable : (prefixWord ++ tailWord_4178826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178826).length < 2 ^ (prefixWord ++ tailWord_4178826).sum := by decide
  have hdescent : baseEnd_4178826 < baseStart_4178826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178836 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 7]
def baseStart_4178836 : Nat := 118140960795 + 4178836 * 2 ^ 59
def prefixEnd_4178836 : Nat := 4983230072969 + 3 ^ 40 * 4178836 * 2
def baseEnd_4178836 : Nat := 238416827145768613181321

theorem tailTrace_4178836 : CollatzResearch.WordTrace tailWord_4178836 prefixEnd_4178836 238416827145768613181321 := by
  unfold tailWord_4178836
  simp only [CollatzResearch.WordTrace]
  refine ⟨76207335144399167607138181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101609780192532223476184241 76207335144399167607138181)
  ·
    refine ⟨14288875339574843926338409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76207335144399167607138181 14288875339574843926338409)
    ·
      refine ⟨10716656504681132944753807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14288875339574843926338409 10716656504681132944753807)
      ·
        refine ⟨16074984757021699417130711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716656504681132944753807 16074984757021699417130711)
        ·
          refine ⟨24112477135532549125696067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16074984757021699417130711 24112477135532549125696067)
          ·
            refine ⟨36168715703298823688544101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24112477135532549125696067 36168715703298823688544101)
            ·
              refine ⟨6781634194368529441602019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36168715703298823688544101 6781634194368529441602019)
              ·
                refine ⟨10172451291552794162403029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781634194368529441602019 10172451291552794162403029)
                ·
                  refine ⟨238416827145768613181321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10172451291552794162403029 238416827145768613181321)
                  ·
                    rfl

theorem cell23_4178836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_4178836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178836 prefixEnd_4178836 := by exact prefixLift 4178836
  have htrace : WordTrace (prefixWord ++ tailWord_4178836) baseStart_4178836 baseEnd_4178836 := by
    simpa [prefixWord, tailWord_4178836, baseEnd_4178836] using wordTrace_append hprefix tailTrace_4178836
  have hstable : (prefixWord ++ tailWord_4178836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178836).length < 2 ^ (prefixWord ++ tailWord_4178836).sum := by decide
  have hdescent : baseEnd_4178836 < baseStart_4178836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178847 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4178847 : Nat := 118140960795 + 4178847 * 2 ^ 59
def prefixEnd_4178847 : Nat := 4983230072969 + 3 ^ 40 * 4178847 * 2
def baseEnd_4178847 : Nat := 2145757092599116975594339

theorem tailTrace_4178847 : CollatzResearch.WordTrace tailWord_4178847 prefixEnd_4178847 2145757092599116975594339 := by
  unfold tailWord_4178847
  simp only [CollatzResearch.WordTrace]
  refine ⟨152415071491758484092926795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101610047661172322728617863 152415071491758484092926795)
  ·
    refine ⟨228622607237637726139390193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152415071491758484092926795 228622607237637726139390193)
    ·
      refine ⟨171466955428228294604542645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228622607237637726139390193 171466955428228294604542645)
      ·
        refine ⟨16075027071396402619175873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171466955428228294604542645 16075027071396402619175873)
        ·
          refine ⟨12056270303547301964381905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16075027071396402619175873 12056270303547301964381905)
          ·
            refine ⟨9042202727660476473286429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056270303547301964381905 9042202727660476473286429)
            ·
              refine ⟨3390826022872678677482411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9042202727660476473286429 3390826022872678677482411)
              ·
                refine ⟨5086239034309018016223617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390826022872678677482411 5086239034309018016223617)
                ·
                  refine ⟨3814679275731763512167713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086239034309018016223617 3814679275731763512167713)
                  ·
                    refine ⟨2861009456798822634125785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3814679275731763512167713 2861009456798822634125785)
                    ·
                      refine ⟨2145757092599116975594339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861009456798822634125785 2145757092599116975594339)
                      ·
                        rfl

theorem cell23_4178847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4178847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178847 prefixEnd_4178847 := by exact prefixLift 4178847
  have htrace : WordTrace (prefixWord ++ tailWord_4178847) baseStart_4178847 baseEnd_4178847 := by
    simpa [prefixWord, tailWord_4178847, baseEnd_4178847] using wordTrace_append hprefix tailTrace_4178847
  have hstable : (prefixWord ++ tailWord_4178847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178847).length < 2 ^ (prefixWord ++ tailWord_4178847).sum := by decide
  have hdescent : baseEnd_4178847 < baseStart_4178847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178956 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_4178956 : Nat := 118140960795 + 4178956 * 2 ^ 59
def prefixEnd_4178956 : Nat := 4983230072969 + 3 ^ 40 * 4178956 * 2
def baseEnd_4178956 : Nat := 715271020663485683043779

theorem tailTrace_4178956 : CollatzResearch.WordTrace tailWord_4178956 prefixEnd_4178956 715271020663485683043779 := by
  unfold tailWord_4178956
  simp only [CollatzResearch.WordTrace]
  refine ⟨76209523524181797854322361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101612698032242397139096481 76209523524181797854322361)
  ·
    refine ⟨57157142643136348390741771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76209523524181797854322361 57157142643136348390741771)
    ·
      refine ⟨85735713964704522586112657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57157142643136348390741771 85735713964704522586112657)
      ·
        refine ⟨64301785473528391939584493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85735713964704522586112657 64301785473528391939584493)
        ·
          refine ⟨24113169552573146977344185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64301785473528391939584493 24113169552573146977344185)
          ·
            refine ⟨18084877164429860233008139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24113169552573146977344185 18084877164429860233008139)
            ·
              refine ⟨27127315746644790349512209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18084877164429860233008139 27127315746644790349512209)
              ·
                refine ⟨20345486809983592762134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27127315746644790349512209 20345486809983592762134157)
                ·
                  refine ⟨7629557553743847285800309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20345486809983592762134157 7629557553743847285800309)
                  ·
                    refine ⟨715271020663485683043779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7629557553743847285800309 715271020663485683043779)
                    ·
                      rfl

theorem cell23_4178956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_4178956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178956 prefixEnd_4178956 := by exact prefixLift 4178956
  have htrace : WordTrace (prefixWord ++ tailWord_4178956) baseStart_4178956 baseEnd_4178956 := by
    simpa [prefixWord, tailWord_4178956, baseEnd_4178956] using wordTrace_append hprefix tailTrace_4178956
  have hstable : (prefixWord ++ tailWord_4178956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178956).length < 2 ^ (prefixWord ++ tailWord_4178956).sum := by decide
  have hdescent : baseEnd_4178956 < baseStart_4178956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178980 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4178980 : Nat := 118140960795 + 4178980 * 2 ^ 59
def prefixEnd_4178980 : Nat := 4983230072969 + 3 ^ 40 * 4178980 * 2
def baseEnd_4178980 : Nat := 2145825385526164955231227

theorem tailTrace_4178980 : CollatzResearch.WordTrace tailWord_4178980 prefixEnd_4178980 2145825385526164955231227 := by
  unfold tailWord_4178980
  simp only [CollatzResearch.WordTrace]
  refine ⟨76209961200138323903759197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101613281600184431871678929 76209961200138323903759197)
  ·
    refine ⟨28578735450051871463909699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76209961200138323903759197 28578735450051871463909699)
    ·
      refine ⟨42868103175077807195864549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28578735450051871463909699 42868103175077807195864549)
      ·
        refine ⟨8037769345327088849224603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42868103175077807195864549 8037769345327088849224603)
        ·
          refine ⟨12056654017990633273836905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037769345327088849224603 12056654017990633273836905)
          ·
            refine ⟨9042490513492974955377679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056654017990633273836905 9042490513492974955377679)
            ·
              refine ⟨13563735770239462433066519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042490513492974955377679 13563735770239462433066519)
              ·
                refine ⟨20345603655359193649599779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13563735770239462433066519 20345603655359193649599779)
                ·
                  refine ⟨30518405483038790474399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20345603655359193649599779 30518405483038790474399669)
                  ·
                    refine ⟨2861100514034886606974969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30518405483038790474399669 2861100514034886606974969)
                    ·
                      refine ⟨2145825385526164955231227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861100514034886606974969 2145825385526164955231227)
                      ·
                        rfl

theorem cell23_4178980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4178980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178980 prefixEnd_4178980 := by exact prefixLift 4178980
  have htrace : WordTrace (prefixWord ++ tailWord_4178980) baseStart_4178980 baseEnd_4178980 := by
    simpa [prefixWord, tailWord_4178980, baseEnd_4178980] using wordTrace_append hprefix tailTrace_4178980
  have hstable : (prefixWord ++ tailWord_4178980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178980).length < 2 ^ (prefixWord ++ tailWord_4178980).sum := by decide
  have hdescent : baseEnd_4178980 < baseStart_4178980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178993 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_4178993 : Nat := 118140960795 + 4178993 * 2 ^ 59
def prefixEnd_4178993 : Nat := 4983230072969 + 3 ^ 40 * 4178993 * 2
def baseEnd_4178993 : Nat := 2145832060774673404368667

theorem tailTrace_4178993 : CollatzResearch.WordTrace tailWord_4178993 prefixEnd_4178993 2145832060774673404368667 := by
  unfold tailWord_4178993
  simp only [CollatzResearch.WordTrace]
  refine ⟨152420396549229551027741633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101613597699486367351827755 152420396549229551027741633)
  ·
    refine ⟨114315297411922163270806225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152420396549229551027741633 114315297411922163270806225)
    ·
      refine ⟨85736473058941622453104669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114315297411922163270806225 85736473058941622453104669)
      ·
        refine ⟨32151177397103108419914251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85736473058941622453104669 32151177397103108419914251)
        ·
          refine ⟨48226766095654662629871377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32151177397103108419914251 48226766095654662629871377)
          ·
            refine ⟨36170074571740996972403533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48226766095654662629871377 36170074571740996972403533)
            ·
              refine ⟨13563777964402873864651325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36170074571740996972403533 13563777964402873864651325)
              ·
                refine ⟨5086416736651077699244247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13563777964402873864651325 5086416736651077699244247)
                ·
                  refine ⟨7629625104976616548866371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086416736651077699244247 7629625104976616548866371)
                  ·
                    refine ⟨11444437657464924823299557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629625104976616548866371 11444437657464924823299557)
                    ·
                      refine ⟨2145832060774673404368667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11444437657464924823299557 2145832060774673404368667)
                      ·
                        rfl

theorem cell23_4178993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_4178993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4178993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4178993 prefixEnd_4178993 := by exact prefixLift 4178993
  have htrace : WordTrace (prefixWord ++ tailWord_4178993) baseStart_4178993 baseEnd_4178993 := by
    simpa [prefixWord, tailWord_4178993, baseEnd_4178993] using wordTrace_append hprefix tailTrace_4178993
  have hstable : (prefixWord ++ tailWord_4178993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178993).length < 2 ^ (prefixWord ++ tailWord_4178993).sum := by decide
  have hdescent : baseEnd_4178993 < baseStart_4178993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179038 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4179038 : Nat := 118140960795 + 4179038 * 2 ^ 59
def prefixEnd_4179038 : Nat := 4983230072969 + 3 ^ 40 * 4179038 * 2
def baseEnd_4179038 : Nat := 2145855167404125728305961

theorem tailTrace_4179038 : CollatzResearch.WordTrace tailWord_4179038 prefixEnd_4179038 2145855167404125728305961 := by
  unfold tailWord_4179038
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052754729258315464141221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101614691889377682475419845 19052754729258315464141221)
  ·
    refine ⟨3572391511735934149526479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19052754729258315464141221 3572391511735934149526479)
    ·
      refine ⟨5358587267603901224289719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572391511735934149526479 5358587267603901224289719)
      ·
        refine ⟨8037880901405851836434579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358587267603901224289719 8037880901405851836434579)
        ·
          refine ⟨12056821352108777754651869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037880901405851836434579 12056821352108777754651869)
          ·
            refine ⟨4521308007040791657994451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12056821352108777754651869 4521308007040791657994451)
            ·
              refine ⟨6781962010561187486991677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521308007040791657994451 6781962010561187486991677)
              ·
                refine ⟨2543235753960445307621879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6781962010561187486991677 2543235753960445307621879)
                ·
                  refine ⟨3814853630940667961432819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543235753960445307621879 3814853630940667961432819)
                  ·
                    refine ⟨5722280446411001942149229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814853630940667961432819 5722280446411001942149229)
                    ·
                      refine ⟨2145855167404125728305961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5722280446411001942149229 2145855167404125728305961)
                      ·
                        rfl

theorem cell23_4179038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4179038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179038 prefixEnd_4179038 := by exact prefixLift 4179038
  have htrace : WordTrace (prefixWord ++ tailWord_4179038) baseStart_4179038 baseEnd_4179038 := by
    simpa [prefixWord, tailWord_4179038, baseEnd_4179038] using wordTrace_append hprefix tailTrace_4179038
  have hstable : (prefixWord ++ tailWord_4179038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179038).length < 2 ^ (prefixWord ++ tailWord_4179038).sum := by decide
  have hdescent : baseEnd_4179038 < baseStart_4179038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179056 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_4179056 : Nat := 118140960795 + 4179056 * 2 ^ 59
def prefixEnd_4179056 : Nat := 4983230072969 + 3 ^ 40 * 4179056 * 2
def baseEnd_4179056 : Nat := 2145864410055906657880877

theorem tailTrace_4179056 : CollatzResearch.WordTrace tailWord_4179056 prefixEnd_4179056 2145864410055906657880877 := by
  unfold tailWord_4179056
  simp only [CollatzResearch.WordTrace]
  refine ⟨76211347174000656393642511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101615129565334208524856681 76211347174000656393642511)
  ·
    refine ⟨114317020761000984590463767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76211347174000656393642511 114317020761000984590463767)
    ·
      refine ⟨171475531141501476885695651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114317020761000984590463767 171475531141501476885695651)
      ·
        refine ⟨257213296712252215328543477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171475531141501476885695651 257213296712252215328543477)
        ·
          refine ⟨24113746566773645187050951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257213296712252215328543477 24113746566773645187050951)
          ·
            refine ⟨36170619850160467780576427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24113746566773645187050951 36170619850160467780576427)
            ·
              refine ⟨54255929775240701670864641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36170619850160467780576427 54255929775240701670864641)
              ·
                refine ⟨40691947331430526253148481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54255929775240701670864641 40691947331430526253148481)
                ·
                  refine ⟨30518960498572894689861361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40691947331430526253148481 30518960498572894689861361)
                  ·
                    refine ⟨22889220373929671017396021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30518960498572894689861361 22889220373929671017396021)
                    ·
                      refine ⟨2145864410055906657880877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22889220373929671017396021 2145864410055906657880877)
                      ·
                        rfl

theorem cell23_4179056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_4179056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179056 prefixEnd_4179056 := by exact prefixLift 4179056
  have htrace : WordTrace (prefixWord ++ tailWord_4179056) baseStart_4179056 baseEnd_4179056 := by
    simpa [prefixWord, tailWord_4179056, baseEnd_4179056] using wordTrace_append hprefix tailTrace_4179056
  have hstable : (prefixWord ++ tailWord_4179056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179056).length < 2 ^ (prefixWord ++ tailWord_4179056).sum := by decide
  have hdescent : baseEnd_4179056 < baseStart_4179056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179061 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4179061 : Nat := 118140960795 + 4179061 * 2 ^ 59
def prefixEnd_4179061 : Nat := 4983230072969 + 3 ^ 40 * 4179061 * 2
def baseEnd_4179061 : Nat := 2145866977459179138318355

theorem tailTrace_4179061 : CollatzResearch.WordTrace tailWord_4179061 prefixEnd_4179061 2145866977459179138318355 := by
  unfold tailWord_4179061
  simp only [CollatzResearch.WordTrace]
  refine ⟨152422876712983198641217037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101615251141988799094144691 152422876712983198641217037)
  ·
    refine ⟨57158578767368699490456389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152422876712983198641217037 57158578767368699490456389)
    ·
      refine ⟨10717233518881631154460573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57158578767368699490456389 10717233518881631154460573)
      ·
        refine ⟨4018962569580611682922715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10717233518881631154460573 4018962569580611682922715)
        ·
          refine ⟨6028443854370917524384073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018962569580611682922715 6028443854370917524384073)
          ·
            refine ⟨4521332890778188143288055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028443854370917524384073 4521332890778188143288055)
            ·
              refine ⟨6781999336167282214932083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521332890778188143288055 6781999336167282214932083)
              ·
                refine ⟨10172999004250923322398125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781999336167282214932083 10172999004250923322398125)
                ·
                  refine ⟨3814874626594096245899297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10172999004250923322398125 3814874626594096245899297)
                  ·
                    refine ⟨2861155969945572184424473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3814874626594096245899297 2861155969945572184424473)
                    ·
                      refine ⟨2145866977459179138318355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861155969945572184424473 2145866977459179138318355)
                      ·
                        rfl

theorem cell23_4179061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4179061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179061 prefixEnd_4179061 := by exact prefixLift 4179061
  have htrace : WordTrace (prefixWord ++ tailWord_4179061) baseStart_4179061 baseEnd_4179061 := by
    simpa [prefixWord, tailWord_4179061, baseEnd_4179061] using wordTrace_append hprefix tailTrace_4179061
  have hstable : (prefixWord ++ tailWord_4179061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179061).length < 2 ^ (prefixWord ++ tailWord_4179061).sum := by decide
  have hdescent : baseEnd_4179061 < baseStart_4179061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179077 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_4179077 : Nat := 118140960795 + 4179077 * 2 ^ 59
def prefixEnd_4179077 : Nat := 4983230072969 + 3 ^ 40 * 4179077 * 2
def baseEnd_4179077 : Nat := 2145875193149651075718281

theorem tailTrace_4179077 : CollatzResearch.WordTrace tailWord_4179077 prefixEnd_4179077 2145875193149651075718281 := by
  unfold tailWord_4179077
  simp only [CollatzResearch.WordTrace]
  refine ⟨152423460280925233373799485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101615640187283488915866323 152423460280925233373799485)
  ·
    refine ⟨57158797605346962515174807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152423460280925233373799485 57158797605346962515174807)
    ·
      refine ⟨85738196408020443772762211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57158797605346962515174807 85738196408020443772762211)
      ·
        refine ⟨128607294612030665659143317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85738196408020443772762211 128607294612030665659143317)
        ·
          refine ⟨6028466934938937452772343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128607294612030665659143317 6028466934938937452772343)
          ·
            refine ⟨9042700402408406179158515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028466934938937452772343 9042700402408406179158515)
            ·
              refine ⟨13564050603612609268737773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042700402408406179158515 13564050603612609268737773)
              ·
                refine ⟨5086518976354728475776665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13564050603612609268737773 5086518976354728475776665)
                ·
                  refine ⟨3814889232266046356832499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086518976354728475776665 3814889232266046356832499)
                  ·
                    refine ⟨5722333848399069535248749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814889232266046356832499 5722333848399069535248749)
                    ·
                      refine ⟨2145875193149651075718281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5722333848399069535248749 2145875193149651075718281)
                      ·
                        rfl

theorem cell23_4179077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_4179077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179077 prefixEnd_4179077 := by exact prefixLift 4179077
  have htrace : WordTrace (prefixWord ++ tailWord_4179077) baseStart_4179077 baseEnd_4179077 := by
    simpa [prefixWord, tailWord_4179077, baseEnd_4179077] using wordTrace_append hprefix tailTrace_4179077
  have hstable : (prefixWord ++ tailWord_4179077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179077).length < 2 ^ (prefixWord ++ tailWord_4179077).sum := by decide
  have hdescent : baseEnd_4179077 < baseStart_4179077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179083 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 5, 4, 2]
def baseStart_4179083 : Nat := 118140960795 + 4179083 * 2 ^ 59
def prefixEnd_4179083 : Nat := 4983230072969 + 3 ^ 40 * 4179083 * 2
def baseEnd_4179083 : Nat := 2145878274033578052243253

theorem tailTrace_4179083 : CollatzResearch.WordTrace tailWord_4179083 prefixEnd_4179083 2145878274033578052243253 := by
  unfold tailWord_4179083
  simp only [CollatzResearch.WordTrace]
  refine ⟨152423679118903496398517903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101615786079268997599011935 152423679118903496398517903)
  ·
    refine ⟨228635518678355244597776855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152423679118903496398517903 228635518678355244597776855)
    ·
      refine ⟨342953278017532866896665283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228635518678355244597776855 342953278017532866896665283)
      ·
        refine ⟨514429917026299300344997925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342953278017532866896665283 514429917026299300344997925)
        ·
          refine ⟨96455609442431118814687111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514429917026299300344997925 96455609442431118814687111)
          ·
            refine ⟨144683414163646678222030667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96455609442431118814687111 144683414163646678222030667)
            ·
              refine ⟨217025121245470017333046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144683414163646678222030667 217025121245470017333046001)
              ·
                refine ⟨162768840934102512999784501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217025121245470017333046001 162768840934102512999784501)
                ·
                  refine ⟨15259578837572110593729797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162768840934102512999784501 15259578837572110593729797)
                  ·
                    refine ⟨2861171032044770736324337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15259578837572110593729797 2861171032044770736324337)
                    ·
                      refine ⟨2145878274033578052243253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861171032044770736324337 2145878274033578052243253)
                      ·
                        rfl

theorem cell23_4179083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4, 2].length) (baseStart_4179083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179083 prefixEnd_4179083 := by exact prefixLift 4179083
  have htrace : WordTrace (prefixWord ++ tailWord_4179083) baseStart_4179083 baseEnd_4179083 := by
    simpa [prefixWord, tailWord_4179083, baseEnd_4179083] using wordTrace_append hprefix tailTrace_4179083
  have hstable : (prefixWord ++ tailWord_4179083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179083).length < 2 ^ (prefixWord ++ tailWord_4179083).sum := by decide
  have hdescent : baseEnd_4179083 < baseStart_4179083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179100 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4179100 : Nat := 118140960795 + 4179100 * 2 ^ 59
def prefixEnd_4179100 : Nat := 4983230072969 + 3 ^ 40 * 4179100 * 2
def baseEnd_4179100 : Nat := 2145887003204704485730675

theorem tailTrace_4179100 : CollatzResearch.WordTrace tailWord_4179100 prefixEnd_4179100 2145887003204704485730675 := by
  unfold tailWord_4179100
  simp only [CollatzResearch.WordTrace]
  refine ⟨76212149579920954150943377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101616199439894605534591169 76212149579920954150943377)
  ·
    refine ⟨57159112184940715613207533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76212149579920954150943377 57159112184940715613207533)
    ·
      refine ⟨21434667069352768354952825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57159112184940715613207533 21434667069352768354952825)
      ·
        refine ⟨16076000302014576266214619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21434667069352768354952825 16076000302014576266214619)
        ·
          refine ⟨24114000453021864399321929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16076000302014576266214619 24114000453021864399321929)
          ·
            refine ⟨18085500339766398299491447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24114000453021864399321929 18085500339766398299491447)
            ·
              refine ⟨27128250509649597449237171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18085500339766398299491447 27128250509649597449237171)
              ·
                refine ⟨40692375764474396173855757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27128250509649597449237171 40692375764474396173855757)
                ·
                  refine ⟨15259640911677898565195909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40692375764474396173855757 15259640911677898565195909)
                  ·
                    refine ⟨2861182670939605980974233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15259640911677898565195909 2861182670939605980974233)
                    ·
                      refine ⟨2145887003204704485730675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861182670939605980974233 2145887003204704485730675)
                      ·
                        rfl

theorem cell23_4179100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4179100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179100 prefixEnd_4179100 := by exact prefixLift 4179100
  have htrace : WordTrace (prefixWord ++ tailWord_4179100) baseStart_4179100 baseEnd_4179100 := by
    simpa [prefixWord, tailWord_4179100, baseEnd_4179100] using wordTrace_append hprefix tailTrace_4179100
  have hstable : (prefixWord ++ tailWord_4179100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179100).length < 2 ^ (prefixWord ++ tailWord_4179100).sum := by decide
  have hdescent : baseEnd_4179100 < baseStart_4179100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179133 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_4179133 : Nat := 118140960795 + 4179133 * 2 ^ 59
def prefixEnd_4179133 : Nat := 4983230072969 + 3 ^ 40 * 4179133 * 2
def baseEnd_4179133 : Nat := 2145903948066302856618023

theorem tailTrace_4179133 : CollatzResearch.WordTrace tailWord_4179133 prefixEnd_4179133 2145903948066302856618023 := by
  unfold tailWord_4179133
  simp only [CollatzResearch.WordTrace]
  refine ⟨152425502768722354937838053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101617001845814903291892035 152425502768722354937838053)
  ·
    refine ⟨28579781769135441550844635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152425502768722354937838053 28579781769135441550844635)
    ·
      refine ⟨42869672653703162326266953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28579781769135441550844635 42869672653703162326266953)
      ·
        refine ⟨32152254490277371744700215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42869672653703162326266953 32152254490277371744700215)
        ·
          refine ⟨48228381735416057617050323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32152254490277371744700215 48228381735416057617050323)
          ·
            refine ⟨72342572603124086425575485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48228381735416057617050323 72342572603124086425575485)
            ·
              refine ⟨27128464726171532409590807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72342572603124086425575485 27128464726171532409590807)
              ·
                refine ⟨40692697089257298614386211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27128464726171532409590807 40692697089257298614386211)
                ·
                  refine ⟨61039045633885947921579317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40692697089257298614386211 61039045633885947921579317)
                  ·
                    refine ⟨5722410528176807617648061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61039045633885947921579317 5722410528176807617648061)
                    ·
                      refine ⟨2145903948066302856618023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5722410528176807617648061 2145903948066302856618023)
                      ·
                        rfl

theorem cell23_4179133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_4179133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179133 prefixEnd_4179133 := by exact prefixLift 4179133
  have htrace : WordTrace (prefixWord ++ tailWord_4179133) baseStart_4179133 baseEnd_4179133 := by
    simpa [prefixWord, tailWord_4179133, baseEnd_4179133] using wordTrace_append hprefix tailTrace_4179133
  have hstable : (prefixWord ++ tailWord_4179133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179133).length < 2 ^ (prefixWord ++ tailWord_4179133).sum := by decide
  have hdescent : baseEnd_4179133 < baseStart_4179133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179134 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_4179134 : Nat := 118140960795 + 4179134 * 2 ^ 59
def prefixEnd_4179134 : Nat := 4983230072969 + 3 ^ 40 * 4179134 * 2
def baseEnd_4179134 : Nat := 2145904461546957352705519

theorem tailTrace_4179134 : CollatzResearch.WordTrace tailWord_4179134 prefixEnd_4179134 2145904461546957352705519 := by
  unfold tailWord_4179134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053192405214841513578057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101617026161145821405749637 19053192405214841513578057)
  ·
    refine ⟨14289894303911131135183543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19053192405214841513578057 14289894303911131135183543)
    ·
      refine ⟨21434841455866696702775315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289894303911131135183543 21434841455866696702775315)
      ·
        refine ⟨32152262183800045054162973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21434841455866696702775315 32152262183800045054162973)
        ·
          refine ⟨12057098318925016895311115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32152262183800045054162973 12057098318925016895311115)
          ·
            refine ⟨18085647478387525342966673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057098318925016895311115 18085647478387525342966673)
            ·
              refine ⟨13564235608790644007225005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18085647478387525342966673 13564235608790644007225005)
              ·
                refine ⟨5086588353296491502709377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13564235608790644007225005 5086588353296491502709377)
                ·
                  refine ⟨3814941264972368627032033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086588353296491502709377 3814941264972368627032033)
                  ·
                    refine ⟨2861205948729276470274025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3814941264972368627032033 2861205948729276470274025)
                    ·
                      refine ⟨2145904461546957352705519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861205948729276470274025 2145904461546957352705519)
                      ·
                        rfl

theorem cell23_4179134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_4179134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179134 prefixEnd_4179134 := by exact prefixLift 4179134
  have htrace : WordTrace (prefixWord ++ tailWord_4179134) baseStart_4179134 baseEnd_4179134 := by
    simpa [prefixWord, tailWord_4179134, baseEnd_4179134] using wordTrace_append hprefix tailTrace_4179134
  have hstable : (prefixWord ++ tailWord_4179134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179134).length < 2 ^ (prefixWord ++ tailWord_4179134).sum := by decide
  have hdescent : baseEnd_4179134 < baseStart_4179134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179140 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 7]
def baseStart_4179140 : Nat := 118140960795 + 4179140 * 2 ^ 59
def prefixEnd_4179140 : Nat := 4983230072969 + 3 ^ 40 * 4179140 * 2
def baseEnd_4179140 : Nat := 238434171381209369914499

theorem tailTrace_4179140 : CollatzResearch.WordTrace tailWord_4179140 prefixEnd_4179140 238434171381209369914499 := by
  unfold tailWord_4179140
  simp only [CollatzResearch.WordTrace]
  refine ⟨76212879039848497566671437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101617172053131330088895249 76212879039848497566671437)
  ·
    refine ⟨28579829639943186587501789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76212879039848497566671437 28579829639943186587501789)
    ·
      refine ⟨10717436114978694970313171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28579829639943186587501789 10717436114978694970313171)
      ·
        refine ⟨16076154172468042455469757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717436114978694970313171 16076154172468042455469757)
        ·
          refine ⟨6028557814675515920801159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16076154172468042455469757 6028557814675515920801159)
          ·
            refine ⟨9042836722013273881201739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028557814675515920801159 9042836722013273881201739)
            ·
              refine ⟨13564255083019910821802609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042836722013273881201739 13564255083019910821802609)
              ·
                refine ⟨10173191312264933116351957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564255083019910821802609 10173191312264933116351957)
                ·
                  refine ⟨238434171381209369914499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10173191312264933116351957 238434171381209369914499)
                  ·
                    rfl

theorem cell23_4179140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_4179140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179140 prefixEnd_4179140 := by exact prefixLift 4179140
  have htrace : WordTrace (prefixWord ++ tailWord_4179140) baseStart_4179140 baseEnd_4179140 := by
    simpa [prefixWord, tailWord_4179140, baseEnd_4179140] using wordTrace_append hprefix tailTrace_4179140
  have hstable : (prefixWord ++ tailWord_4179140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179140).length < 2 ^ (prefixWord ++ tailWord_4179140).sum := by decide
  have hdescent : baseEnd_4179140 < baseStart_4179140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179157 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 5]
def baseStart_4179157 : Nat := 118140960795 + 4179157 * 2 ^ 59
def prefixEnd_4179157 : Nat := 4983230072969 + 3 ^ 40 * 4179157 * 2
def baseEnd_4179157 : Nat := 238435141289112306968657

theorem tailTrace_4179157 : CollatzResearch.WordTrace tailWord_4179157 prefixEnd_4179157 238435141289112306968657 := by
  unfold tailWord_4179157
  simp only [CollatzResearch.WordTrace]
  refine ⟨152426378120635407036711725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101617585413756938024474483 152426378120635407036711725)
  ·
    refine ⟨57159891795238277638766897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152426378120635407036711725 57159891795238277638766897)
    ·
      refine ⟨42869918846428708229075173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57159891795238277638766897 42869918846428708229075173)
      ·
        refine ⟨8038109783705382792951595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42869918846428708229075173 8038109783705382792951595)
        ·
          refine ⟨12057164675558074189427393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8038109783705382792951595 12057164675558074189427393)
          ·
            refine ⟨9042873506668555642070545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12057164675558074189427393 9042873506668555642070545)
            ·
              refine ⟨6782155130001416731552909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9042873506668555642070545 6782155130001416731552909)
              ·
                refine ⟨2543308173750531274332341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6782155130001416731552909 2543308173750531274332341)
                ·
                  refine ⟨238435141289112306968657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2543308173750531274332341 238435141289112306968657)
                  ·
                    rfl

theorem cell23_4179157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_4179157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179157 prefixEnd_4179157 := by exact prefixLift 4179157
  have htrace : WordTrace (prefixWord ++ tailWord_4179157) baseStart_4179157 baseEnd_4179157 := by
    simpa [prefixWord, tailWord_4179157, baseEnd_4179157] using wordTrace_append hprefix tailTrace_4179157
  have hstable : (prefixWord ++ tailWord_4179157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179157).length < 2 ^ (prefixWord ++ tailWord_4179157).sum := by decide
  have hdescent : baseEnd_4179157 < baseStart_4179157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179193 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_4179193 : Nat := 118140960795 + 4179193 * 2 ^ 59
def prefixEnd_4179193 : Nat := 4983230072969 + 3 ^ 40 * 4179193 * 2
def baseEnd_4179193 : Nat := 2145934756905572621867747

theorem tailTrace_4179193 : CollatzResearch.WordTrace tailWord_4179193 prefixEnd_4179193 2145934756905572621867747 := by
  unfold tailWord_4179193
  simp only [CollatzResearch.WordTrace]
  refine ⟨152427691148504985185022233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101618460765669990123348155 152427691148504985185022233)
  ·
    refine ⟨114320768361378738888766675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152427691148504985185022233 114320768361378738888766675)
    ·
      refine ⟨171481152542068108333150013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114320768361378738888766675 171481152542068108333150013)
      ·
        refine ⟨64305432203275540624931255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171481152542068108333150013 64305432203275540624931255)
        ·
          refine ⟨96458148304913310937396883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64305432203275540624931255 96458148304913310937396883)
          ·
            refine ⟨144687222457369966406095325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96458148304913310937396883 144687222457369966406095325)
            ·
              refine ⟨54257708421513737402285747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144687222457369966406095325 54257708421513737402285747)
              ·
                refine ⟨81386562632270606103428621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54257708421513737402285747 81386562632270606103428621)
                ·
                  refine ⟨30519960987101477288785733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81386562632270606103428621 30519960987101477288785733)
                  ·
                    refine ⟨5722492685081526991647325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30519960987101477288785733 5722492685081526991647325)
                    ·
                      refine ⟨2145934756905572621867747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5722492685081526991647325 2145934756905572621867747)
                      ·
                        rfl

theorem cell23_4179193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_4179193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179193 prefixEnd_4179193 := by exact prefixLift 4179193
  have htrace : WordTrace (prefixWord ++ tailWord_4179193) baseStart_4179193 baseEnd_4179193 := by
    simpa [prefixWord, tailWord_4179193, baseEnd_4179193] using wordTrace_append hprefix tailTrace_4179193
  have hstable : (prefixWord ++ tailWord_4179193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179193).length < 2 ^ (prefixWord ++ tailWord_4179193).sum := by decide
  have hdescent : baseEnd_4179193 < baseStart_4179193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179210 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4179210 : Nat := 118140960795 + 4179210 * 2 ^ 59
def prefixEnd_4179210 : Nat := 4983230072969 + 3 ^ 40 * 4179210 * 2
def baseEnd_4179210 : Nat := 2145943486076699055355169

theorem tailTrace_4179210 : CollatzResearch.WordTrace tailWord_4179210 prefixEnd_4179210 2145943486076699055355169 := by
  unfold tailWord_4179210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107077797360849272097771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101618874126295598058927389 38107077797360849272097771)
  ·
    refine ⟨57160616696041273908146657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38107077797360849272097771 57160616696041273908146657)
    ·
      refine ⟨42870462522030955431109993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57160616696041273908146657 42870462522030955431109993)
      ·
        refine ⟨32152846891523216573332495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42870462522030955431109993 32152846891523216573332495)
        ·
          refine ⟨48229270337284824859998743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32152846891523216573332495 48229270337284824859998743)
          ·
            refine ⟨72343905505927237289998115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48229270337284824859998743 72343905505927237289998115)
            ·
              refine ⟨108515858258890855934997173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72343905505927237289998115 108515858258890855934997173)
              ·
                refine ⟨10173361711771017743905985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108515858258890855934997173 10173361711771017743905985)
                ·
                  refine ⟨7630021283828263307929489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10173361711771017743905985 7630021283828263307929489)
                  ·
                    refine ⟨5722515962871197480947117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7630021283828263307929489 5722515962871197480947117)
                    ·
                      refine ⟨2145943486076699055355169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5722515962871197480947117 2145943486076699055355169)
                      ·
                        rfl

theorem cell23_4179210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4179210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179210 prefixEnd_4179210 := by exact prefixLift 4179210
  have htrace : WordTrace (prefixWord ++ tailWord_4179210) baseStart_4179210 baseEnd_4179210 := by
    simpa [prefixWord, tailWord_4179210, baseEnd_4179210] using wordTrace_append hprefix tailTrace_4179210
  have hstable : (prefixWord ++ tailWord_4179210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179210).length < 2 ^ (prefixWord ++ tailWord_4179210).sum := by decide
  have hdescent : baseEnd_4179210 < baseStart_4179210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179234 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4179234 : Nat := 118140960795 + 4179234 * 2 ^ 59
def prefixEnd_4179234 : Nat := 4983230072969 + 3 ^ 40 * 4179234 * 2
def baseEnd_4179234 : Nat := 715318603204135653818353

theorem tailTrace_4179234 : CollatzResearch.WordTrace tailWord_4179234 prefixEnd_4179234 715318603204135653818353 := by
  unfold tailWord_4179234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107296635339112296816189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101619457694237632791509837 38107296635339112296816189)
  ·
    refine ⟨14290236238252167111306071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38107296635339112296816189 14290236238252167111306071)
    ·
      refine ⟨21435354357378250666959107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290236238252167111306071 21435354357378250666959107)
      ·
        refine ⟨32153031536067376000438661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21435354357378250666959107 32153031536067376000438661)
        ·
          refine ⟨6028693413012633000082249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32153031536067376000438661 6028693413012633000082249)
          ·
            refine ⟨4521520059759474750061687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028693413012633000082249 4521520059759474750061687)
            ·
              refine ⟨6782280089639212125092531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521520059759474750061687 6782280089639212125092531)
              ·
                refine ⟨10173420134458818187638797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782280089639212125092531 10173420134458818187638797)
                ·
                  refine ⟨3815032550422056820364549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10173420134458818187638797 3815032550422056820364549)
                  ·
                    refine ⟨715318603204135653818353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815032550422056820364549 715318603204135653818353)
                    ·
                      rfl

theorem cell23_4179234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4179234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179234 prefixEnd_4179234 := by exact prefixLift 4179234
  have htrace : WordTrace (prefixWord ++ tailWord_4179234) baseStart_4179234 baseEnd_4179234 := by
    simpa [prefixWord, tailWord_4179234, baseEnd_4179234] using wordTrace_append hprefix tailTrace_4179234
  have hstable : (prefixWord ++ tailWord_4179234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179234).length < 2 ^ (prefixWord ++ tailWord_4179234).sum := by decide
  have hdescent : baseEnd_4179234 < baseStart_4179234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179260 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_4179260 : Nat := 118140960795 + 4179260 * 2 ^ 59
def prefixEnd_4179260 : Nat := 4983230072969 + 3 ^ 40 * 4179260 * 2
def baseEnd_4179260 : Nat := 715323053369807953243313

theorem tailTrace_4179260 : CollatzResearch.WordTrace tailWord_4179260 prefixEnd_4179260 715323053369807953243313 := by
  unfold tailWord_4179260
  simp only [CollatzResearch.WordTrace]
  refine ⟨76215067419631127813855617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101620089892841503751807489 76215067419631127813855617)
  ·
    refine ⟨57161300564723345860391713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76215067419631127813855617 57161300564723345860391713)
    ·
      refine ⟨42870975423542509395293785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57161300564723345860391713 42870975423542509395293785)
      ·
        refine ⟨32153231567656882046470339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42870975423542509395293785 32153231567656882046470339)
        ·
          refine ⟨48229847351485323069705509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32153231567656882046470339 48229847351485323069705509)
          ·
            refine ⟨9043096378403498075569783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48229847351485323069705509 9043096378403498075569783)
            ·
              refine ⟨13564644567605247113354675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043096378403498075569783 13564644567605247113354675)
              ·
                refine ⟨20346966851407870670032013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13564644567605247113354675 20346966851407870670032013)
                ·
                  refine ⟨7630112569277951501262005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20346966851407870670032013 7630112569277951501262005)
                  ·
                    refine ⟨715323053369807953243313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7630112569277951501262005 715323053369807953243313)
                    ·
                      rfl

theorem cell23_4179260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_4179260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179260 prefixEnd_4179260 := by exact prefixLift 4179260
  have htrace : WordTrace (prefixWord ++ tailWord_4179260) baseStart_4179260 baseEnd_4179260 := by
    simpa [prefixWord, tailWord_4179260, baseEnd_4179260] using wordTrace_append hprefix tailTrace_4179260
  have hstable : (prefixWord ++ tailWord_4179260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179260).length < 2 ^ (prefixWord ++ tailWord_4179260).sum := by decide
  have hdescent : baseEnd_4179260 < baseStart_4179260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179273 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_4179273 : Nat := 118140960795 + 4179273 * 2 ^ 59
def prefixEnd_4179273 : Nat := 4983230072969 + 3 ^ 40 * 4179273 * 2
def baseEnd_4179273 : Nat := 715325278452644102955793

theorem tailTrace_4179273 : CollatzResearch.WordTrace tailWord_4179273 prefixEnd_4179273 715325278452644102955793 := by
  unfold tailWord_4179273
  simp only [CollatzResearch.WordTrace]
  refine ⟨152430608988215158847934473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101620405992143439231956315 152430608988215158847934473)
  ·
    refine ⟨114322956741161369135950855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152430608988215158847934473 114322956741161369135950855)
    ·
      refine ⟨171484435111742053703926283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114322956741161369135950855 171484435111742053703926283)
      ·
        refine ⟨257226652667613080555889425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171484435111742053703926283 257226652667613080555889425)
        ·
          refine ⟨192919989500709810416917069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257226652667613080555889425 192919989500709810416917069)
          ·
            refine ⟨72344996062766178906343901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192919989500709810416917069 72344996062766178906343901)
            ·
              refine ⟨27129373523537317089878963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72344996062766178906343901 27129373523537317089878963)
              ·
                refine ⟨40694060285305975634818445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27129373523537317089878963 40694060285305975634818445)
                ·
                  refine ⟨15260272606989740863056917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40694060285305975634818445 15260272606989740863056917)
                  ·
                    refine ⟨715325278452644102955793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15260272606989740863056917 715325278452644102955793)
                    ·
                      rfl

theorem cell23_4179273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_4179273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179273 prefixEnd_4179273 := by exact prefixLift 4179273
  have htrace : WordTrace (prefixWord ++ tailWord_4179273) baseStart_4179273 baseEnd_4179273 := by
    simpa [prefixWord, tailWord_4179273, baseEnd_4179273] using wordTrace_append hprefix tailTrace_4179273
  have hstable : (prefixWord ++ tailWord_4179273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179273).length < 2 ^ (prefixWord ++ tailWord_4179273).sum := by decide
  have hdescent : baseEnd_4179273 < baseStart_4179273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179290 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_4179290 : Nat := 118140960795 + 4179290 * 2 ^ 59
def prefixEnd_4179290 : Nat := 4983230072969 + 3 ^ 40 * 4179290 * 2
def baseEnd_4179290 : Nat := 715328188176352914118267

theorem tailTrace_4179290 : CollatzResearch.WordTrace tailWord_4179290 prefixEnd_4179290 715328188176352914118267 := by
  unfold tailWord_4179290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107807257288392687825831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101620819352769047167535549 38107807257288392687825831)
  ·
    refine ⟨57161710885932589031738747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38107807257288392687825831 57161710885932589031738747)
    ·
      refine ⟨85742566328898883547608121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57161710885932589031738747 85742566328898883547608121)
      ·
        refine ⟨64306924746674162660706091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85742566328898883547608121 64306924746674162660706091)
        ·
          refine ⟨96460387120011243991059137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64306924746674162660706091 96460387120011243991059137)
          ·
            refine ⟨72345290340008432993294353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96460387120011243991059137 72345290340008432993294353)
            ·
              refine ⟨54258967755006324744970765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72345290340008432993294353 54258967755006324744970765)
              ·
                refine ⟨20347112908127371779364037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54258967755006324744970765 20347112908127371779364037)
                ·
                  refine ⟨3815083670273882208630757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20347112908127371779364037 3815083670273882208630757)
                  ·
                    refine ⟨715328188176352914118267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815083670273882208630757 715328188176352914118267)
                    ·
                      rfl

theorem cell23_4179290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_4179290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179290 prefixEnd_4179290 := by exact prefixLift 4179290
  have htrace : WordTrace (prefixWord ++ tailWord_4179290) baseStart_4179290 baseEnd_4179290 := by
    simpa [prefixWord, tailWord_4179290, baseEnd_4179290] using wordTrace_append hprefix tailTrace_4179290
  have hstable : (prefixWord ++ tailWord_4179290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179290).length < 2 ^ (prefixWord ++ tailWord_4179290).sum := by decide
  have hdescent : baseEnd_4179290 < baseStart_4179290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179297 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_4179297 : Nat := 118140960795 + 4179297 * 2 ^ 59
def prefixEnd_4179297 : Nat := 4983230072969 + 3 ^ 40 * 4179297 * 2
def baseEnd_4179297 : Nat := 2145988158893640214967269

theorem tailTrace_4179297 : CollatzResearch.WordTrace tailWord_4179297 prefixEnd_4179297 2145988158893640214967269 := by
  unfold tailWord_4179297
  simp only [CollatzResearch.WordTrace]
  refine ⟨152431484340128210946808145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101620989560085473964538763 152431484340128210946808145)
  ·
    refine ⟨114323613255096158210106109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152431484340128210946808145 114323613255096158210106109)
    ·
      refine ⟨42871354970661059328789791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114323613255096158210106109 42871354970661059328789791)
      ·
        refine ⟨64307032455991588993184687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42871354970661059328789791 64307032455991588993184687)
        ·
          refine ⟨96460548683987383489777031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64307032455991588993184687 96460548683987383489777031)
          ·
            refine ⟨144690823025981075234665547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96460548683987383489777031 144690823025981075234665547)
            ·
              refine ⟨217036234538971612851998321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144690823025981075234665547 217036234538971612851998321)
              ·
                refine ⟨162777175904228709638998741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217036234538971612851998321 162777175904228709638998741)
                ·
                  refine ⟨3815090060255360382164033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162777175904228709638998741 3815090060255360382164033)
                  ·
                    refine ⟨2861317545191520286623025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815090060255360382164033 2861317545191520286623025)
                    ·
                      refine ⟨2145988158893640214967269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861317545191520286623025 2145988158893640214967269)
                      ·
                        rfl

theorem cell23_4179297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_4179297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179297 prefixEnd_4179297 := by exact prefixLift 4179297
  have htrace : WordTrace (prefixWord ++ tailWord_4179297) baseStart_4179297 baseEnd_4179297 := by
    simpa [prefixWord, tailWord_4179297, baseEnd_4179297] using wordTrace_append hprefix tailTrace_4179297
  have hstable : (prefixWord ++ tailWord_4179297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179297).length < 2 ^ (prefixWord ++ tailWord_4179297).sum := by decide
  have hdescent : baseEnd_4179297 < baseStart_4179297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179314 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4179314 : Nat := 118140960795 + 4179314 * 2 ^ 59
def prefixEnd_4179314 : Nat := 4983230072969 + 3 ^ 40 * 4179314 * 2
def baseEnd_4179314 : Nat := 2145996888064766648454691

theorem tailTrace_4179314 : CollatzResearch.WordTrace tailWord_4179314 prefixEnd_4179314 2145996888064766648454691 := by
  unfold tailWord_4179314
  simp only [CollatzResearch.WordTrace]
  refine ⟨38108026095266655712544249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101621402920711081900117997 38108026095266655712544249)
  ·
    refine ⟨28581019571449991784408187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38108026095266655712544249 28581019571449991784408187)
    ·
      refine ⟨42871529357174987676612281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28581019571449991784408187 42871529357174987676612281)
      ·
        refine ⟨32153647017881240757459211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42871529357174987676612281 32153647017881240757459211)
        ·
          refine ⟨48230470526821861136188817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32153647017881240757459211 48230470526821861136188817)
          ·
            refine ⟨36172852895116395852141613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48230470526821861136188817 36172852895116395852141613)
            ·
              refine ⟨13564819835668648444553105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36172852895116395852141613 13564819835668648444553105)
              ·
                refine ⟨10173614876751486333414829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564819835668648444553105 10173614876751486333414829)
                ·
                  refine ⟨3815105578781807375030561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10173614876751486333414829 3815105578781807375030561)
                  ·
                    refine ⟨2861329184086355531272921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815105578781807375030561 2861329184086355531272921)
                    ·
                      refine ⟨2145996888064766648454691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861329184086355531272921 2145996888064766648454691)
                      ·
                        rfl

theorem cell23_4179314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4179314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179314 prefixEnd_4179314 := by exact prefixLift 4179314
  have htrace : WordTrace (prefixWord ++ tailWord_4179314) baseStart_4179314 baseEnd_4179314 := by
    simpa [prefixWord, tailWord_4179314, baseEnd_4179314] using wordTrace_append hprefix tailTrace_4179314
  have hstable : (prefixWord ++ tailWord_4179314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179314).length < 2 ^ (prefixWord ++ tailWord_4179314).sum := by decide
  have hdescent : baseEnd_4179314 < baseStart_4179314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179331 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 1, 2, 2]
def baseStart_4179331 : Nat := 118140960795 + 4179331 * 2 ^ 59
def prefixEnd_4179331 : Nat := 4983230072969 + 3 ^ 40 * 4179331 * 2
def baseEnd_4179331 : Nat := 2146005617235893081942113

theorem tailTrace_4179331 : CollatzResearch.WordTrace tailWord_4179331 prefixEnd_4179331 2146005617235893081942113 := by
  unfold tailWord_4179331
  simp only [CollatzResearch.WordTrace]
  refine ⟨152432724422005034753545847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101621816281336689835697231 152432724422005034753545847)
  ·
    refine ⟨228649086633007552130318771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152432724422005034753545847 228649086633007552130318771)
    ·
      refine ⟨342973629949511328195478157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228649086633007552130318771 342973629949511328195478157)
      ·
        refine ⟨128615111231066748073304309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342973629949511328195478157 128615111231066748073304309)
        ·
          refine ⟨12057666677912507631872279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128615111231066748073304309 12057666677912507631872279)
          ·
            refine ⟨18086500016868761447808419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057666677912507631872279 18086500016868761447808419)
            ·
              refine ⟨27129750025303142171712629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18086500016868761447808419 27129750025303142171712629)
              ·
                refine ⟨2543414064872169578598059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27129750025303142171712629 2543414064872169578598059)
                ·
                  refine ⟨3815121097308254367897089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543414064872169578598059 3815121097308254367897089)
                  ·
                    refine ⟨2861340822981190775922817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815121097308254367897089 2861340822981190775922817)
                    ·
                      refine ⟨2146005617235893081942113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861340822981190775922817 2146005617235893081942113)
                      ·
                        rfl

theorem cell23_4179331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_4179331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179331 prefixEnd_4179331 := by exact prefixLift 4179331
  have htrace : WordTrace (prefixWord ++ tailWord_4179331) baseStart_4179331 baseEnd_4179331 := by
    simpa [prefixWord, tailWord_4179331, baseEnd_4179331] using wordTrace_append hprefix tailTrace_4179331
  have hstable : (prefixWord ++ tailWord_4179331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179331).length < 2 ^ (prefixWord ++ tailWord_4179331).sum := by decide
  have hdescent : baseEnd_4179331 < baseStart_4179331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179348 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4179348 : Nat := 118140960795 + 4179348 * 2 ^ 59
def prefixEnd_4179348 : Nat := 4983230072969 + 3 ^ 40 * 4179348 * 2
def baseEnd_4179348 : Nat := 2146014346407019515429535

theorem tailTrace_4179348 : CollatzResearch.WordTrace tailWord_4179348 prefixEnd_4179348 2146014346407019515429535 := by
  unfold tailWord_4179348
  simp only [CollatzResearch.WordTrace]
  refine ⟨76216672231471723328457349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101622229641962297771276465 76216672231471723328457349)
  ·
    refine ⟨14290626043400948124085753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76216672231471723328457349 14290626043400948124085753)
    ·
      refine ⟨10717969532550711093064315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14290626043400948124085753 10717969532550711093064315)
      ·
        refine ⟨16076954298826066639596473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717969532550711093064315 16076954298826066639596473)
        ·
          refine ⟨12057715724119549979697355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16076954298826066639596473 12057715724119549979697355)
          ·
            refine ⟨18086573586179324969546033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057715724119549979697355 18086573586179324969546033)
            ·
              refine ⟨13564930189634493727159525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18086573586179324969546033 13564930189634493727159525)
              ·
                refine ⟨2543424410556467573842411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13564930189634493727159525 2543424410556467573842411)
                ·
                  refine ⟨3815136615834701360763617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543424410556467573842411 3815136615834701360763617)
                  ·
                    refine ⟨2861352461876026020572713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815136615834701360763617 2861352461876026020572713)
                    ·
                      refine ⟨2146014346407019515429535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861352461876026020572713 2146014346407019515429535)
                      ·
                        rfl

theorem cell23_4179348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4179348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179348 prefixEnd_4179348 := by exact prefixLift 4179348
  have htrace : WordTrace (prefixWord ++ tailWord_4179348) baseStart_4179348 baseEnd_4179348 := by
    simpa [prefixWord, tailWord_4179348, baseEnd_4179348] using wordTrace_append hprefix tailTrace_4179348
  have hstable : (prefixWord ++ tailWord_4179348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179348).length < 2 ^ (prefixWord ++ tailWord_4179348).sum := by decide
  have hdescent : baseEnd_4179348 < baseStart_4179348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179358 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4179358 : Nat := 118140960795 + 4179358 * 2 ^ 59
def prefixEnd_4179358 : Nat := 4983230072969 + 3 ^ 40 * 4179358 * 2
def baseEnd_4179358 : Nat := 715339827071188158768163

theorem tailTrace_4179358 : CollatzResearch.WordTrace tailWord_4179358 prefixEnd_4179358 715339827071188158768163 := by
  unfold tailWord_4179358
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054213649113402295597341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101622472795271478909852485 19054213649113402295597341)
  ·
    refine ⟨7145330118417525860849003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19054213649113402295597341 7145330118417525860849003)
    ·
      refine ⟨10717995177626288791273505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7145330118417525860849003 10717995177626288791273505)
      ·
        refine ⟨8038496383219716593455129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10717995177626288791273505 8038496383219716593455129)
        ·
          refine ⟨6028872287414787445091347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8038496383219716593455129 6028872287414787445091347)
          ·
            refine ⟨9043308431122181167637021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028872287414787445091347 9043308431122181167637021)
            ·
              refine ⟨3391240661670817937863883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9043308431122181167637021 3391240661670817937863883)
              ·
                refine ⟨5086860992506226906795825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391240661670817937863883 5086860992506226906795825)
                ·
                  refine ⟨3815145744379670180096869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086860992506226906795825 3815145744379670180096869)
                  ·
                    refine ⟨715339827071188158768163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815145744379670180096869 715339827071188158768163)
                    ·
                      rfl

theorem cell23_4179358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4179358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179358 prefixEnd_4179358 := by exact prefixLift 4179358
  have htrace : WordTrace (prefixWord ++ tailWord_4179358) baseStart_4179358 baseEnd_4179358 := by
    simpa [prefixWord, tailWord_4179358, baseEnd_4179358] using wordTrace_append hprefix tailTrace_4179358
  have hstable : (prefixWord ++ tailWord_4179358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179358).length < 2 ^ (prefixWord ++ tailWord_4179358).sum := by decide
  have hdescent : baseEnd_4179358 < baseStart_4179358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179450 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_4179450 : Nat := 118140960795 + 4179450 * 2 ^ 59
def prefixEnd_4179450 : Nat := 4983230072969 + 3 ^ 40 * 4179450 * 2
def baseEnd_4179450 : Nat := 2146066721433778116354065

theorem tailTrace_4179450 : CollatzResearch.WordTrace tailWord_4179450 prefixEnd_4179450 2146066721433778116354065 := by
  unfold tailWord_4179450
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109266177143479519281951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101624709805715945384751869 38109266177143479519281951)
  ·
    refine ⟨57163899265715219278922927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38109266177143479519281951 57163899265715219278922927)
    ·
      refine ⟨85745848898572828918384391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57163899265715219278922927 85745848898572828918384391)
      ·
        refine ⟨128618773347859243377576587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85745848898572828918384391 128618773347859243377576587)
        ·
          refine ⟨192928160021788865066364881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128618773347859243377576587 192928160021788865066364881)
          ·
            refine ⟨144696120016341648799773661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192928160021788865066364881 144696120016341648799773661)
            ·
              refine ⟨54261045006128118299915123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144696120016341648799773661 54261045006128118299915123)
              ·
                refine ⟨81391567509192177449872685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54261045006128118299915123 81391567509192177449872685)
                ·
                  refine ⟨30521837815947066543702257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81391567509192177449872685 30521837815947066543702257)
                  ·
                    refine ⟨22891378361960299907776693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30521837815947066543702257 22891378361960299907776693)
                    ·
                      refine ⟨2146066721433778116354065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22891378361960299907776693 2146066721433778116354065)
                      ·
                        rfl

theorem cell23_4179450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_4179450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179450 prefixEnd_4179450 := by exact prefixLift 4179450
  have htrace : WordTrace (prefixWord ++ tailWord_4179450) baseStart_4179450 baseEnd_4179450 := by
    simpa [prefixWord, tailWord_4179450, baseEnd_4179450] using wordTrace_append hprefix tailTrace_4179450
  have hstable : (prefixWord ++ tailWord_4179450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179450).length < 2 ^ (prefixWord ++ tailWord_4179450).sum := by decide
  have hdescent : baseEnd_4179450 < baseStart_4179450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179487 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 5, 4]
def baseStart_4179487 : Nat := 118140960795 + 4179487 * 2 ^ 59
def prefixEnd_4179487 : Nat := 4983230072969 + 3 ^ 40 * 4179487 * 2
def baseEnd_4179487 : Nat := 715361906739331490530465

theorem tailTrace_4179487 : CollatzResearch.WordTrace tailWord_4179487 prefixEnd_4179487 715361906739331490530465 := by
  unfold tailWord_4179487
  simp only [CollatzResearch.WordTrace]
  refine ⟨152438414209439873396224715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101625609472959915597483143 152438414209439873396224715)
  ·
    refine ⟨228657621314159810094337073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152438414209439873396224715 228657621314159810094337073)
    ·
      refine ⟨171493215985619857570752805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228657621314159810094337073 171493215985619857570752805)
      ·
        refine ⟨32154977997303723294516151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171493215985619857570752805 32154977997303723294516151)
        ·
          refine ⟨48232466995955584941774227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32154977997303723294516151 48232466995955584941774227)
          ·
            refine ⟨72348700493933377412661341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48232466995955584941774227 72348700493933377412661341)
            ·
              refine ⟨27130762685225016529748003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72348700493933377412661341 27130762685225016529748003)
              ·
                refine ⟨40696144027837524794622005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27130762685225016529748003 40696144027837524794622005)
                ·
                  refine ⟨3815263502609767949495813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40696144027837524794622005 3815263502609767949495813)
                  ·
                    refine ⟨715361906739331490530465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815263502609767949495813 715361906739331490530465)
                    ·
                      rfl

theorem cell23_4179487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_4179487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179487 prefixEnd_4179487 := by exact prefixLift 4179487
  have htrace : WordTrace (prefixWord ++ tailWord_4179487) baseStart_4179487 baseEnd_4179487 := by
    simpa [prefixWord, tailWord_4179487, baseEnd_4179487] using wordTrace_append hprefix tailTrace_4179487
  have hstable : (prefixWord ++ tailWord_4179487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179487).length < 2 ^ (prefixWord ++ tailWord_4179487).sum := by decide
  have hdescent : baseEnd_4179487 < baseStart_4179487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179491 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 2, 5]
def baseStart_4179491 : Nat := 118140960795 + 4179491 * 2 ^ 59
def prefixEnd_4179491 : Nat := 4983230072969 + 3 ^ 40 * 4179491 * 2
def baseEnd_4179491 : Nat := 715362591380204151980459

theorem tailTrace_4179491 : CollatzResearch.WordTrace tailWord_4179491 prefixEnd_4179491 715362591380204151980459 := by
  unfold tailWord_4179491
  simp only [CollatzResearch.WordTrace]
  refine ⟨152438560101425382079370327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101625706734283588052913551 152438560101425382079370327)
  ·
    refine ⟨228657840152138073119055491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152438560101425382079370327 228657840152138073119055491)
    ·
      refine ⟨342986760228207109678583237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228657840152138073119055491 342986760228207109678583237)
      ·
        refine ⟨64310017542788833064734357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342986760228207109678583237 64310017542788833064734357)
        ·
          refine ⟨3014532072318226549909423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64310017542788833064734357 3014532072318226549909423)
          ·
            refine ⟨4521798108477339824864135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014532072318226549909423 4521798108477339824864135)
            ·
              refine ⟨6782697162716009737296203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521798108477339824864135 6782697162716009737296203)
              ·
                refine ⟨10174045744074014605944305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782697162716009737296203 10174045744074014605944305)
                ·
                  refine ⟨7630534308055510954458229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10174045744074014605944305 7630534308055510954458229)
                  ·
                    refine ⟨715362591380204151980459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7630534308055510954458229 715362591380204151980459)
                    ·
                      rfl

theorem cell23_4179491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 5].length) (baseStart_4179491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179491 prefixEnd_4179491 := by exact prefixLift 4179491
  have htrace : WordTrace (prefixWord ++ tailWord_4179491) baseStart_4179491 baseEnd_4179491 := by
    simpa [prefixWord, tailWord_4179491, baseEnd_4179491] using wordTrace_append hprefix tailTrace_4179491
  have hstable : (prefixWord ++ tailWord_4179491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179491).length < 2 ^ (prefixWord ++ tailWord_4179491).sum := by decide
  have hdescent : baseEnd_4179491 < baseStart_4179491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179521 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4179521 : Nat := 118140960795 + 4179521 * 2 ^ 59
def prefixEnd_4179521 : Nat := 4983230072969 + 3 ^ 40 * 4179521 * 2
def baseEnd_4179521 : Nat := 715367726186749112855413

theorem tailTrace_4179521 : CollatzResearch.WordTrace tailWord_4179521 prefixEnd_4179521 715367726186749112855413 := by
  unfold tailWord_4179521
  simp only [CollatzResearch.WordTrace]
  refine ⟨152439654291316697202962417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101626436194211131468641611 152439654291316697202962417)
  ·
    refine ⟨114329740718487522902221813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152439654291316697202962417 114329740718487522902221813)
    ·
      refine ⟨10718413192358205272083295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114329740718487522902221813 10718413192358205272083295)
      ·
        refine ⟨16077619788537307908124943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10718413192358205272083295 16077619788537307908124943)
        ·
          refine ⟨24116429682805961862187415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16077619788537307908124943 24116429682805961862187415)
          ·
            refine ⟨36174644524208942793281123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24116429682805961862187415 36174644524208942793281123)
            ·
              refine ⟨54261966786313414189921685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36174644524208942793281123 54261966786313414189921685)
              ·
                refine ⟨2543529693108441290152579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54261966786313414189921685 2543529693108441290152579)
                ·
                  refine ⟨3815294539662661935228869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543529693108441290152579 3815294539662661935228869)
                  ·
                    refine ⟨715367726186749112855413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815294539662661935228869 715367726186749112855413)
                    ·
                      rfl

theorem cell23_4179521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4179521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179521 prefixEnd_4179521 := by exact prefixLift 4179521
  have htrace : WordTrace (prefixWord ++ tailWord_4179521) baseStart_4179521 baseEnd_4179521 := by
    simpa [prefixWord, tailWord_4179521, baseEnd_4179521] using wordTrace_append hprefix tailTrace_4179521
  have hstable : (prefixWord ++ tailWord_4179521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179521).length < 2 ^ (prefixWord ++ tailWord_4179521).sum := by decide
  have hdescent : baseEnd_4179521 < baseStart_4179521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179567 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_4179567 : Nat := 118140960795 + 4179567 * 2 ^ 59
def prefixEnd_4179567 : Nat := 4983230072969 + 3 ^ 40 * 4179567 * 2
def baseEnd_4179567 : Nat := 2146126798670354158591027

theorem tailTrace_4179567 : CollatzResearch.WordTrace tailWord_4179567 prefixEnd_4179567 2146126798670354158591027 := by
  unfold tailWord_4179567
  simp only [CollatzResearch.WordTrace]
  refine ⟨152441332049150047059136955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101627554699433364706091303 152441332049150047059136955)
  ·
    refine ⟨228661998073725070588705433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152441332049150047059136955 228661998073725070588705433)
    ·
      refine ⟨171496498555293802941529075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228661998073725070588705433 171496498555293802941529075)
      ·
        refine ⟨257244747832940704412293613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171496498555293802941529075 257244747832940704412293613)
        ·
          refine ⟨96466780437352764154610105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257244747832940704412293613 96466780437352764154610105)
          ·
            refine ⟨72350085328014573115957579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96466780437352764154610105 72350085328014573115957579)
            ·
              refine ⟨108525127992021859673936369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72350085328014573115957579 108525127992021859673936369)
              ·
                refine ⟨81393845994016394755452277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108525127992021859673936369 81393845994016394755452277)
                ·
                  refine ⟨7630673061939037008323651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81393845994016394755452277 7630673061939037008323651)
                  ·
                    refine ⟨11446009592908555512485477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7630673061939037008323651 11446009592908555512485477)
                    ·
                      refine ⟨2146126798670354158591027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11446009592908555512485477 2146126798670354158591027)
                      ·
                        rfl

theorem cell23_4179567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_4179567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179567 prefixEnd_4179567 := by exact prefixLift 4179567
  have htrace : WordTrace (prefixWord ++ tailWord_4179567) baseStart_4179567 baseEnd_4179567 := by
    simpa [prefixWord, tailWord_4179567, baseEnd_4179567] using wordTrace_append hprefix tailTrace_4179567
  have hstable : (prefixWord ++ tailWord_4179567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179567).length < 2 ^ (prefixWord ++ tailWord_4179567).sum := by decide
  have hdescent : baseEnd_4179567 < baseStart_4179567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179587 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3]
def baseStart_4179587 : Nat := 118140960795 + 4179587 * 2 ^ 59
def prefixEnd_4179587 : Nat := 4983230072969 + 3 ^ 40 * 4179587 * 2
def baseEnd_4179587 : Nat := 2146137068283444080340935

theorem tailTrace_4179587 : CollatzResearch.WordTrace tailWord_4179587 prefixEnd_4179587 2146137068283444080340935 := by
  unfold tailWord_4179587
  simp only [CollatzResearch.WordTrace]
  refine ⟨152442061509077590474865015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101628041006051726983243343 152442061509077590474865015)
  ·
    refine ⟨228663092263616385712297523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152442061509077590474865015 228663092263616385712297523)
    ·
      refine ⟨342994638395424578568446285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228663092263616385712297523 342994638395424578568446285)
      ·
        refine ⟨128622989398284216963167357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342994638395424578568446285 128622989398284216963167357)
        ·
          refine ⟨48233621024356581361187759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128622989398284216963167357 48233621024356581361187759)
          ·
            refine ⟨72350431536534872041781639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48233621024356581361187759 72350431536534872041781639)
            ·
              refine ⟨108525647304802308062672459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72350431536534872041781639 108525647304802308062672459)
              ·
                refine ⟨162788470957203462094008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108525647304802308062672459 162788470957203462094008689)
                ·
                  refine ⟨122091353217902596570506517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162788470957203462094008689 122091353217902596570506517)
                  ·
                    refine ⟨5723032182089184214242493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122091353217902596570506517 5723032182089184214242493)
                    ·
                      refine ⟨2146137068283444080340935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723032182089184214242493 2146137068283444080340935)
                      ·
                        rfl

theorem cell23_4179587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_4179587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179587 prefixEnd_4179587 := by exact prefixLift 4179587
  have htrace : WordTrace (prefixWord ++ tailWord_4179587) baseStart_4179587 baseEnd_4179587 := by
    simpa [prefixWord, tailWord_4179587, baseEnd_4179587] using wordTrace_append hprefix tailTrace_4179587
  have hstable : (prefixWord ++ tailWord_4179587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179587).length < 2 ^ (prefixWord ++ tailWord_4179587).sum := by decide
  have hdescent : baseEnd_4179587 < baseStart_4179587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179607 : List Nat := [1, 1, 3, 3, 2, 2, 2, 9]
def baseStart_4179607 : Nat := 118140960795 + 4179607 * 2 ^ 59
def prefixEnd_4179607 : Nat := 4983230072969 + 3 ^ 40 * 4179607 * 2
def baseEnd_4179607 : Nat := 79486938440612370447809

theorem tailTrace_4179607 : CollatzResearch.WordTrace tailWord_4179607 prefixEnd_4179607 79486938440612370447809 := by
  unfold tailWord_4179607
  simp only [CollatzResearch.WordTrace]
  refine ⟨152442790969005133890593075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101628527312670089260395383 152442790969005133890593075)
  ·
    refine ⟨228664186453507700835889613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152442790969005133890593075 228664186453507700835889613)
    ·
      refine ⟨85749069920065387813458605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228664186453507700835889613 85749069920065387813458605)
      ·
        refine ⟨32155901220024520430046977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85749069920065387813458605 32155901220024520430046977)
        ·
          refine ⟨24116925915018390322535233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32155901220024520430046977 24116925915018390322535233)
          ·
            refine ⟨18087694436263792741901425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24116925915018390322535233 18087694436263792741901425)
            ·
              refine ⟨13565770827197844556426069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18087694436263792741901425 13565770827197844556426069)
              ·
                refine ⟨79486938440612370447809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13565770827197844556426069 79486938440612370447809)
                ·
                  rfl

theorem cell23_4179607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 9].length) (baseStart_4179607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179607 prefixEnd_4179607 := by exact prefixLift 4179607
  have htrace : WordTrace (prefixWord ++ tailWord_4179607) baseStart_4179607 baseEnd_4179607 := by
    simpa [prefixWord, tailWord_4179607, baseEnd_4179607] using wordTrace_append hprefix tailTrace_4179607
  have hstable : (prefixWord ++ tailWord_4179607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179607).length < 2 ^ (prefixWord ++ tailWord_4179607).sum := by decide
  have hdescent : baseEnd_4179607 < baseStart_4179607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179638 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4179638 : Nat := 118140960795 + 4179638 * 2 ^ 59
def prefixEnd_4179638 : Nat := 4983230072969 + 3 ^ 40 * 4179638 * 2
def baseEnd_4179638 : Nat := 2146163255796823380803201

theorem tailTrace_4179638 : CollatzResearch.WordTrace tailWord_4179638 prefixEnd_4179638 2146163255796823380803201 := by
  unfold tailWord_4179638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527745101993301636560723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101629281087928550789981045 9527745101993301636560723)
  ·
    refine ⟨14291617652989952454841085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9527745101993301636560723 14291617652989952454841085)
    ·
      refine ⟨5359356619871232170565407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14291617652989952454841085 5359356619871232170565407)
      ·
        refine ⟨8039034929806848255848111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5359356619871232170565407 8039034929806848255848111)
        ·
          refine ⟨12058552394710272383772167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039034929806848255848111 12058552394710272383772167)
          ·
            refine ⟨18087828592065408575658251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12058552394710272383772167 18087828592065408575658251)
            ·
              refine ⟨27131742888098112863487377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18087828592065408575658251 27131742888098112863487377)
              ·
                refine ⟨20348807166073584647615533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27131742888098112863487377 20348807166073584647615533)
                ·
                  refine ⟨7630802687277594242855825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20348807166073584647615533 7630802687277594242855825)
                  ·
                    refine ⟨5723102015458195682141869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7630802687277594242855825 5723102015458195682141869)
                    ·
                      refine ⟨2146163255796823380803201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723102015458195682141869 2146163255796823380803201)
                      ·
                        rfl

theorem cell23_4179638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4179638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179638 prefixEnd_4179638 := by exact prefixLift 4179638
  have htrace : WordTrace (prefixWord ++ tailWord_4179638) baseStart_4179638 baseEnd_4179638 := by
    simpa [prefixWord, tailWord_4179638, baseEnd_4179638] using wordTrace_append hprefix tailTrace_4179638
  have hstable : (prefixWord ++ tailWord_4179638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179638).length < 2 ^ (prefixWord ++ tailWord_4179638).sum := by decide
  have hdescent : baseEnd_4179638 < baseStart_4179638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179724 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_4179724 : Nat := 118140960795 + 4179724 * 2 ^ 59
def prefixEnd_4179724 : Nat := 4983230072969 + 3 ^ 40 * 4179724 * 2
def baseEnd_4179724 : Nat := 2146207415133110044327805

theorem tailTrace_4179724 : CollatzResearch.WordTrace tailWord_4179724 prefixEnd_4179724 2146207415133110044327805 := by
  unfold tailWord_4179724
  simp only [CollatzResearch.WordTrace]
  refine ⟨76223529154790631436301113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101631372206387508581734817 76223529154790631436301113)
  ·
    refine ⟨57167646866092973577225835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76223529154790631436301113 57167646866092973577225835)
    ·
      refine ⟨85751470299139460365838753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57167646866092973577225835 85751470299139460365838753)
      ·
        refine ⟨64313602724354595274379065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85751470299139460365838753 64313602724354595274379065)
        ·
          refine ⟨48235202043265946455784299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64313602724354595274379065 48235202043265946455784299)
          ·
            refine ⟨72352803064898919683676449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48235202043265946455784299 72352803064898919683676449)
            ·
              refine ⟨54264602298674189762757337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72352803064898919683676449 54264602298674189762757337)
              ·
                refine ⟨40698451724005642322068003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54264602298674189762757337 40698451724005642322068003)
                ·
                  refine ⟨61047677586008463483102005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40698451724005642322068003 61047677586008463483102005)
                  ·
                    refine ⟨5723219773688293451540813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61047677586008463483102005 5723219773688293451540813)
                    ·
                      refine ⟨2146207415133110044327805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723219773688293451540813 2146207415133110044327805)
                      ·
                        rfl

theorem cell23_4179724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_4179724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179724 prefixEnd_4179724 := by exact prefixLift 4179724
  have htrace : WordTrace (prefixWord ++ tailWord_4179724) baseStart_4179724 baseEnd_4179724 := by
    simpa [prefixWord, tailWord_4179724, baseEnd_4179724] using wordTrace_append hprefix tailTrace_4179724
  have hstable : (prefixWord ++ tailWord_4179724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179724).length < 2 ^ (prefixWord ++ tailWord_4179724).sum := by decide
  have hdescent : baseEnd_4179724 < baseStart_4179724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179781 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_4179781 : Nat := 118140960795 + 4179781 * 2 ^ 59
def prefixEnd_4179781 : Nat := 4983230072969 + 3 ^ 40 * 4179781 * 2
def baseEnd_4179781 : Nat := 2146236683530416321315043

theorem tailTrace_4179781 : CollatzResearch.WordTrace tailWord_4179781 prefixEnd_4179781 2146236683530416321315043 := by
  unfold tailWord_4179781
  simp only [CollatzResearch.WordTrace]
  refine ⟨152449137270374761607427197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101632758180249841071618131 152449137270374761607427197)
  ·
    refine ⟨57168426476390535602785199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152449137270374761607427197 57168426476390535602785199)
    ·
      refine ⟨85752639714585803404177799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57168426476390535602785199 85752639714585803404177799)
      ·
        refine ⟨128628959571878705106266699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85752639714585803404177799 128628959571878705106266699)
        ·
          refine ⟨192943439357818057659400049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128628959571878705106266699 192943439357818057659400049)
          ·
            refine ⟨144707579518363543244550037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192943439357818057659400049 144707579518363543244550037)
            ·
              refine ⟨6783167789923291089588283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144707579518363543244550037 6783167789923291089588283)
              ·
                refine ⟨10174751684884936634382425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783167789923291089588283 10174751684884936634382425)
                ·
                  refine ⟨7631063763663702475786819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10174751684884936634382425 7631063763663702475786819)
                  ·
                    refine ⟨11446595645495553713680229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7631063763663702475786819 11446595645495553713680229)
                    ·
                      refine ⟨2146236683530416321315043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11446595645495553713680229 2146236683530416321315043)
                      ·
                        rfl

theorem cell23_4179781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_4179781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179781 prefixEnd_4179781 := by exact prefixLift 4179781
  have htrace : WordTrace (prefixWord ++ tailWord_4179781) baseStart_4179781 baseEnd_4179781 := by
    simpa [prefixWord, tailWord_4179781, baseEnd_4179781] using wordTrace_append hprefix tailTrace_4179781
  have hstable : (prefixWord ++ tailWord_4179781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179781).length < 2 ^ (prefixWord ++ tailWord_4179781).sum := by decide
  have hdescent : baseEnd_4179781 < baseStart_4179781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179801 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_4179801 : Nat := 118140960795 + 4179801 * 2 ^ 59
def prefixEnd_4179801 : Nat := 4983230072969 + 3 ^ 40 * 4179801 * 2
def baseEnd_4179801 : Nat := 2146246953143506243064951

theorem tailTrace_4179801 : CollatzResearch.WordTrace tailWord_4179801 prefixEnd_4179801 2146246953143506243064951 := by
  unfold tailWord_4179801
  simp only [CollatzResearch.WordTrace]
  refine ⟨152449866730302305023155257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101633244486868203348770171 152449866730302305023155257)
  ·
    refine ⟨114337400047726728767366443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152449866730302305023155257 114337400047726728767366443)
    ·
      refine ⟨171506100071590093151049665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114337400047726728767366443 171506100071590093151049665)
      ·
        refine ⟨128629575053692569863287249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171506100071590093151049665 128629575053692569863287249)
        ·
          refine ⟨96472181290269427397465437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128629575053692569863287249 96472181290269427397465437)
          ·
            refine ⟨36177067983851035274049539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96472181290269427397465437 36177067983851035274049539)
            ·
              refine ⟨54265601975776552911074309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36177067983851035274049539 54265601975776552911074309)
              ·
                refine ⟨10174800370458103670826433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54265601975776552911074309 10174800370458103670826433)
                ·
                  refine ⟨7631100277843577753119825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10174800370458103670826433 7631100277843577753119825)
                  ·
                    refine ⟨5723325208382683314839869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7631100277843577753119825 5723325208382683314839869)
                    ·
                      refine ⟨2146246953143506243064951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723325208382683314839869 2146246953143506243064951)
                      ·
                        rfl

theorem cell23_4179801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_4179801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179801 prefixEnd_4179801 := by exact prefixLift 4179801
  have htrace : WordTrace (prefixWord ++ tailWord_4179801) baseStart_4179801 baseEnd_4179801 := by
    simpa [prefixWord, tailWord_4179801, baseEnd_4179801] using wordTrace_append hprefix tailTrace_4179801
  have hstable : (prefixWord ++ tailWord_4179801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179801).length < 2 ^ (prefixWord ++ tailWord_4179801).sum := by decide
  have hdescent : baseEnd_4179801 < baseStart_4179801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179821 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 6]
def baseStart_4179821 : Nat := 118140960795 + 4179821 * 2 ^ 59
def prefixEnd_4179821 : Nat := 4983230072969 + 3 ^ 40 * 4179821 * 2
def baseEnd_4179821 : Nat := 238473024750732907201651

theorem tailTrace_4179821 : CollatzResearch.WordTrace tailWord_4179821 prefixEnd_4179821 238473024750732907201651 := by
  unfold tailWord_4179821
  simp only [CollatzResearch.WordTrace]
  refine ⟨152450596190229848438883317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101633730793486565625922211 152450596190229848438883317)
  ·
    refine ⟨14292243392834048291145311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152450596190229848438883317 14292243392834048291145311)
    ·
      refine ⟨21438365089251072436717967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14292243392834048291145311 21438365089251072436717967)
      ·
        refine ⟨32157547633876608655076951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21438365089251072436717967 32157547633876608655076951)
        ·
          refine ⟨48236321450814912982615427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32157547633876608655076951 48236321450814912982615427)
          ·
            refine ⟨72354482176222369473923141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48236321450814912982615427 72354482176222369473923141)
            ·
              refine ⟨13566465408041694276360589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72354482176222369473923141 13566465408041694276360589)
              ·
                refine ⟨5087424528015635353635221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13566465408041694276360589 5087424528015635353635221)
                ·
                  refine ⟨238473024750732907201651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5087424528015635353635221 238473024750732907201651)
                  ·
                    rfl

theorem cell23_4179821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_4179821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179821 prefixEnd_4179821 := by exact prefixLift 4179821
  have htrace : WordTrace (prefixWord ++ tailWord_4179821) baseStart_4179821 baseEnd_4179821 := by
    simpa [prefixWord, tailWord_4179821, baseEnd_4179821] using wordTrace_append hprefix tailTrace_4179821
  have hstable : (prefixWord ++ tailWord_4179821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179821).length < 2 ^ (prefixWord ++ tailWord_4179821).sum := by decide
  have hdescent : baseEnd_4179821 < baseStart_4179821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179865 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 1, 1, 3]
def baseStart_4179865 : Nat := 118140960795 + 4179865 * 2 ^ 59
def prefixEnd_4179865 : Nat := 4983230072969 + 3 ^ 40 * 4179865 * 2
def baseEnd_4179865 : Nat := 2146279815905393992664657

theorem tailTrace_4179865 : CollatzResearch.WordTrace tailWord_4179865 prefixEnd_4179865 2146279815905393992664657 := by
  unfold tailWord_4179865
  simp only [CollatzResearch.WordTrace]
  refine ⟨152452201002070443953485049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101634800668046962635656699 152452201002070443953485049)
  ·
    refine ⟨114339150751552832965113787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152452201002070443953485049 114339150751552832965113787)
    ·
      refine ⟨171508726127329249447670681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114339150751552832965113787 171508726127329249447670681)
      ·
        refine ⟨128631544595496937085753011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171508726127329249447670681 128631544595496937085753011)
        ·
          refine ⟨192947316893245405628629517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128631544595496937085753011 192947316893245405628629517)
          ·
            refine ⟨72355243834967027110736069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192947316893245405628629517 72355243834967027110736069)
            ·
              refine ⟨13566608219056317583263013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72355243834967027110736069 13566608219056317583263013)
              ·
                refine ⟨2543739041073059546861815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13566608219056317583263013 2543739041073059546861815)
                ·
                  refine ⟨3815608561609589320292723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543739041073059546861815 3815608561609589320292723)
                  ·
                    refine ⟨5723412842414383980439085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3815608561609589320292723 5723412842414383980439085)
                    ·
                      refine ⟨2146279815905393992664657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723412842414383980439085 2146279815905393992664657)
                      ·
                        rfl

theorem cell23_4179865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_4179865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179865 prefixEnd_4179865 := by exact prefixLift 4179865
  have htrace : WordTrace (prefixWord ++ tailWord_4179865) baseStart_4179865 baseEnd_4179865 := by
    simpa [prefixWord, tailWord_4179865, baseEnd_4179865] using wordTrace_append hprefix tailTrace_4179865
  have hstable : (prefixWord ++ tailWord_4179865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179865).length < 2 ^ (prefixWord ++ tailWord_4179865).sum := by decide
  have hdescent : baseEnd_4179865 < baseStart_4179865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179921 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_4179921 : Nat := 118140960795 + 4179921 * 2 ^ 59
def prefixEnd_4179921 : Nat := 4983230072969 + 3 ^ 40 * 4179921 * 2
def baseEnd_4179921 : Nat := 2146308570822045773564399

theorem tailTrace_4179921 : CollatzResearch.WordTrace tailWord_4179921 prefixEnd_4179921 2146308570822045773564399 := by
  unfold tailWord_4179921
  simp only [CollatzResearch.WordTrace]
  refine ⟨152454243489867565517523617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101636162326578377011682411 152454243489867565517523617)
  ·
    refine ⟨114340682617400674138142713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152454243489867565517523617 114340682617400674138142713)
    ·
      refine ⟨85755511963050505603607035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114340682617400674138142713 85755511963050505603607035)
      ·
        refine ⟨128633267944575758405410553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85755511963050505603607035 128633267944575758405410553)
        ·
          refine ⟨96474950958431818804057915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128633267944575758405410553 96474950958431818804057915)
          ·
            refine ⟨144712426437647728206086873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96474950958431818804057915 144712426437647728206086873)
            ·
              refine ⟨108534319828235796154565155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144712426437647728206086873 108534319828235796154565155)
              ·
                refine ⟨162801479742353694231847733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108534319828235796154565155 162801479742353694231847733)
                ·
                  refine ⟨15262638725845658834235725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162801479742353694231847733 15262638725845658834235725)
                  ·
                    refine ⟨5723489522192122062838397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15262638725845658834235725 5723489522192122062838397)
                    ·
                      refine ⟨2146308570822045773564399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723489522192122062838397 2146308570822045773564399)
                      ·
                        rfl

theorem cell23_4179921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_4179921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179921 prefixEnd_4179921 := by exact prefixLift 4179921
  have htrace : WordTrace (prefixWord ++ tailWord_4179921) baseStart_4179921 baseEnd_4179921 := by
    simpa [prefixWord, tailWord_4179921, baseEnd_4179921] using wordTrace_append hprefix tailTrace_4179921
  have hstable : (prefixWord ++ tailWord_4179921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179921).length < 2 ^ (prefixWord ++ tailWord_4179921).sum := by decide
  have hdescent : baseEnd_4179921 < baseStart_4179921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179965 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_4179965 : Nat := 118140960795 + 4179965 * 2 ^ 59
def prefixEnd_4179965 : Nat := 4983230072969 + 3 ^ 40 * 4179965 * 2
def baseEnd_4179965 : Nat := 2146331163970843601414197

theorem tailTrace_4179965 : CollatzResearch.WordTrace tailWord_4179965 prefixEnd_4179965 2146331163970843601414197 := by
  unfold tailWord_4179965
  simp only [CollatzResearch.WordTrace]
  refine ⟨152455848301708161032125349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101637232201138774021416899 152455848301708161032125349)
  ·
    refine ⟨28585471556570280193523503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152455848301708161032125349 28585471556570280193523503)
    ·
      refine ⟨42878207334855420290285255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585471556570280193523503 42878207334855420290285255)
      ·
        refine ⟨64317311002283130435427883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42878207334855420290285255 64317311002283130435427883)
        ·
          refine ⟨96475966503424695653141825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64317311002283130435427883 96475966503424695653141825)
          ·
            refine ⟨72356974877568521739856369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96475966503424695653141825 72356974877568521739856369)
            ·
              refine ⟨54267731158176391304892277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72356974877568521739856369 54267731158176391304892277)
              ·
                refine ⟨5087599796079036684833651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54267731158176391304892277 5087599796079036684833651)
                ·
                  refine ⟨7631399694118555027250477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087599796079036684833651 7631399694118555027250477)
                  ·
                    refine ⟨2861774885294458135218929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7631399694118555027250477 2861774885294458135218929)
                    ·
                      refine ⟨2146331163970843601414197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861774885294458135218929 2146331163970843601414197)
                      ·
                        rfl

theorem cell23_4179965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_4179965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4179965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4179965 prefixEnd_4179965 := by exact prefixLift 4179965
  have htrace : WordTrace (prefixWord ++ tailWord_4179965) baseStart_4179965 baseEnd_4179965 := by
    simpa [prefixWord, tailWord_4179965, baseEnd_4179965] using wordTrace_append hprefix tailTrace_4179965
  have hstable : (prefixWord ++ tailWord_4179965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179965).length < 2 ^ (prefixWord ++ tailWord_4179965).sum := by decide
  have hdescent : baseEnd_4179965 < baseStart_4179965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180028 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_4180028 : Nat := 118140960795 + 4180028 * 2 ^ 59
def prefixEnd_4180028 : Nat := 4983230072969 + 3 ^ 40 * 4180028 * 2
def baseEnd_4180028 : Nat := 2146363513252076854926407

theorem tailTrace_4180028 : CollatzResearch.WordTrace tailWord_4180028 prefixEnd_4180028 2146363513252076854926407 := by
  unfold tailWord_4180028
  simp only [CollatzResearch.WordTrace]
  refine ⟨76229073050239961395834369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101638764066986615194445825 76229073050239961395834369)
  ·
    refine ⟨57171804787679971046875777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76229073050239961395834369 57171804787679971046875777)
    ·
      refine ⟨42878853590759978285156833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57171804787679971046875777 42878853590759978285156833)
      ·
        refine ⟨32159140193069983713867625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42878853590759978285156833 32159140193069983713867625)
        ·
          refine ⟨24119355144802487785400719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32159140193069983713867625 24119355144802487785400719)
          ·
            refine ⟨36179032717203731678101079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24119355144802487785400719 36179032717203731678101079)
            ·
              refine ⟨54268549075805597517151619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36179032717203731678101079 54268549075805597517151619)
              ·
                refine ⟨81402823613708396275727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54268549075805597517151619 81402823613708396275727429)
                ·
                  refine ⟨15263029427570324301698893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81402823613708396275727429 15263029427570324301698893)
                  ·
                    refine ⟨5723636035338871613137085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15263029427570324301698893 5723636035338871613137085)
                    ·
                      refine ⟨2146363513252076854926407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723636035338871613137085 2146363513252076854926407)
                      ·
                        rfl

theorem cell23_4180028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_4180028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180028 prefixEnd_4180028 := by exact prefixLift 4180028
  have htrace : WordTrace (prefixWord ++ tailWord_4180028) baseStart_4180028 baseEnd_4180028 := by
    simpa [prefixWord, tailWord_4180028, baseEnd_4180028] using wordTrace_append hprefix tailTrace_4180028
  have hstable : (prefixWord ++ tailWord_4180028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180028).length < 2 ^ (prefixWord ++ tailWord_4180028).sum := by decide
  have hdescent : baseEnd_4180028 < baseStart_4180028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180041 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_4180041 : Nat := 118140960795 + 4180041 * 2 ^ 59
def prefixEnd_4180041 : Nat := 4983230072969 + 3 ^ 40 * 4180041 * 2
def baseEnd_4180041 : Nat := 2146370188500585304063847

theorem tailTrace_4180041 : CollatzResearch.WordTrace tailWord_4180041 prefixEnd_4180041 2146370188500585304063847 := by
  unfold tailWord_4180041
  simp only [CollatzResearch.WordTrace]
  refine ⟨152458620249432826011891977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101639080166288550674594651 152458620249432826011891977)
  ·
    refine ⟨114343965187074619508918983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152458620249432826011891977 114343965187074619508918983)
    ·
      refine ⟨171515947780611929263378475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114343965187074619508918983 171515947780611929263378475)
      ·
        refine ⟨257273921670917893895067713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171515947780611929263378475 257273921670917893895067713)
        ·
          refine ⟨192955441253188420421300785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257273921670917893895067713 192955441253188420421300785)
          ·
            refine ⟨144716580939891315315975589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192955441253188420421300785 144716580939891315315975589)
            ·
              refine ⟨27134358926229621621745423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144716580939891315315975589 27134358926229621621745423)
              ·
                refine ⟨40701538389344432432618135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27134358926229621621745423 40701538389344432432618135)
                ·
                  refine ⟨61052307584016648648927203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40701538389344432432618135 61052307584016648648927203)
                  ·
                    refine ⟨91578461376024972973390805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61052307584016648648927203 91578461376024972973390805)
                    ·
                      refine ⟨2146370188500585304063847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91578461376024972973390805 2146370188500585304063847)
                      ·
                        rfl

theorem cell23_4180041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_4180041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180041 prefixEnd_4180041 := by exact prefixLift 4180041
  have htrace : WordTrace (prefixWord ++ tailWord_4180041) baseStart_4180041 baseEnd_4180041 := by
    simpa [prefixWord, tailWord_4180041, baseEnd_4180041] using wordTrace_append hprefix tailTrace_4180041
  have hstable : (prefixWord ++ tailWord_4180041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180041).length < 2 ^ (prefixWord ++ tailWord_4180041).sum := by decide
  have hdescent : baseEnd_4180041 < baseStart_4180041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180045 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_4180045 : Nat := 118140960795 + 4180045 * 2 ^ 59
def prefixEnd_4180045 : Nat := 4983230072969 + 3 ^ 40 * 4180045 * 2
def baseEnd_4180045 : Nat := 2146372242423203288413829

theorem tailTrace_4180045 : CollatzResearch.WordTrace tailWord_4180045 prefixEnd_4180045 2146372242423203288413829 := by
  unfold tailWord_4180045
  simp only [CollatzResearch.WordTrace]
  refine ⟨152458766141418334695037589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101639177427612223130025059 152458766141418334695037589)
  ·
    refine ⟨7146504662878984438829887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152458766141418334695037589 7146504662878984438829887)
    ·
      refine ⟨10719756994318476658244831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146504662878984438829887 10719756994318476658244831)
      ·
        refine ⟨16079635491477714987367247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10719756994318476658244831 16079635491477714987367247)
        ·
          refine ⟨24119453237216572481050871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16079635491477714987367247 24119453237216572481050871)
          ·
            refine ⟨36179179855824858721576307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24119453237216572481050871 36179179855824858721576307)
            ·
              refine ⟨54268769783737288082364461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36179179855824858721576307 54268769783737288082364461)
              ·
                refine ⟨20350788668901483030886673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54268769783737288082364461 20350788668901483030886673)
                ·
                  refine ⟨15263091501676112273165005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20350788668901483030886673 15263091501676112273165005)
                  ·
                    refine ⟨5723659313128542102436877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15263091501676112273165005 5723659313128542102436877)
                    ·
                      refine ⟨2146372242423203288413829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723659313128542102436877 2146372242423203288413829)
                      ·
                        rfl

theorem cell23_4180045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_4180045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180045 prefixEnd_4180045 := by exact prefixLift 4180045
  have htrace : WordTrace (prefixWord ++ tailWord_4180045) baseStart_4180045 baseEnd_4180045 := by
    simpa [prefixWord, tailWord_4180045, baseEnd_4180045] using wordTrace_append hprefix tailTrace_4180045
  have hstable : (prefixWord ++ tailWord_4180045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180045).length < 2 ^ (prefixWord ++ tailWord_4180045).sum := by decide
  have hdescent : baseEnd_4180045 < baseStart_4180045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180068 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4180068 : Nat := 118140960795 + 4180068 * 2 ^ 59
def prefixEnd_4180068 : Nat := 4983230072969 + 3 ^ 40 * 4180068 * 2
def baseEnd_4180068 : Nat := 2146384052478256698426223

theorem tailTrace_4180068 : CollatzResearch.WordTrace tailWord_4180068 prefixEnd_4180068 2146384052478256698426223 := by
  unfold tailWord_4180068
  simp only [CollatzResearch.WordTrace]
  refine ⟨76229802510167504811562429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101639736680223339748749905 76229802510167504811562429)
  ·
    refine ⟨28586175941312814304335911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76229802510167504811562429 28586175941312814304335911)
    ·
      refine ⟨42879263911969221456503867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28586175941312814304335911 42879263911969221456503867)
      ·
        refine ⟨64318895867953832184755801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42879263911969221456503867 64318895867953832184755801)
        ·
          refine ⟨48239171900965374138566851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64318895867953832184755801 48239171900965374138566851)
          ·
            refine ⟨72358757851448061207850277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48239171900965374138566851 72358757851448061207850277)
            ·
              refine ⟨13567267097146511476471927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72358757851448061207850277 13567267097146511476471927)
              ·
                refine ⟨20350900645719767214707891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13567267097146511476471927 20350900645719767214707891)
                ·
                  refine ⟨30526350968579650822061837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20350900645719767214707891 30526350968579650822061837)
                  ·
                    refine ⟨11447381613217369058273189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30526350968579650822061837 11447381613217369058273189)
                    ·
                      refine ⟨2146384052478256698426223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11447381613217369058273189 2146384052478256698426223)
                      ·
                        rfl

theorem cell23_4180068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4180068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180068 prefixEnd_4180068 := by exact prefixLift 4180068
  have htrace : WordTrace (prefixWord ++ tailWord_4180068) baseStart_4180068 baseEnd_4180068 := by
    simpa [prefixWord, tailWord_4180068, baseEnd_4180068] using wordTrace_append hprefix tailTrace_4180068
  have hstable : (prefixWord ++ tailWord_4180068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180068).length < 2 ^ (prefixWord ++ tailWord_4180068).sum := by decide
  have hdescent : baseEnd_4180068 < baseStart_4180068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180175 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_4180175 : Nat := 118140960795 + 4180175 * 2 ^ 59
def prefixEnd_4180175 : Nat := 4983230072969 + 3 ^ 40 * 4180175 * 2
def baseEnd_4180175 : Nat := 2146438994908287779788231

theorem tailTrace_4180175 : CollatzResearch.WordTrace tailWord_4180175 prefixEnd_4180175 2146438994908287779788231 := by
  unfold tailWord_4180175
  simp only [CollatzResearch.WordTrace]
  refine ⟨152463507630947366897269979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101642338420631577931513319 152463507630947366897269979)
  ·
    refine ⟨228695261446421050345904969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152463507630947366897269979 228695261446421050345904969)
    ·
      refine ⟨171521446084815787759428727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228695261446421050345904969 171521446084815787759428727)
      ·
        refine ⟨257282169127223681639143091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171521446084815787759428727 257282169127223681639143091)
        ·
          refine ⟨385923253690835522458714637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257282169127223681639143091 385923253690835522458714637)
          ·
            refine ⟨144721220134063320922017989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385923253690835522458714637 144721220134063320922017989)
            ·
              refine ⟨27135228775136872672878373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144721220134063320922017989 27135228775136872672878373)
              ·
                refine ⟨5087855395338163626164695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27135228775136872672878373 5087855395338163626164695)
                ·
                  refine ⟨7631783093007245439247043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087855395338163626164695 7631783093007245439247043)
                  ·
                    refine ⟨11447674639510868158870565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7631783093007245439247043 11447674639510868158870565)
                    ·
                      refine ⟨2146438994908287779788231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11447674639510868158870565 2146438994908287779788231)
                      ·
                        rfl

theorem cell23_4180175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_4180175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180175 prefixEnd_4180175 := by exact prefixLift 4180175
  have htrace : WordTrace (prefixWord ++ tailWord_4180175) baseStart_4180175 baseEnd_4180175 := by
    simpa [prefixWord, tailWord_4180175, baseEnd_4180175] using wordTrace_append hprefix tailTrace_4180175
  have hstable : (prefixWord ++ tailWord_4180175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180175).length < 2 ^ (prefixWord ++ tailWord_4180175).sum := by decide
  have hdescent : baseEnd_4180175 < baseStart_4180175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180189 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_4180189 : Nat := 118140960795 + 4180189 * 2 ^ 59
def prefixEnd_4180189 : Nat := 4983230072969 + 3 ^ 40 * 4180189 * 2
def baseEnd_4180189 : Nat := 715482061212483575004389

theorem tailTrace_4180189 : CollatzResearch.WordTrace tailWord_4180189 prefixEnd_4180189 715482061212483575004389 := by
  unfold tailWord_4180189
  simp only [CollatzResearch.WordTrace]
  refine ⟨152464018252896647288279621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101642678835264431525519747 152464018252896647288279621)
  ·
    refine ⟨28587003422418121366552429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152464018252896647288279621 28587003422418121366552429)
    ·
      refine ⟨10720126283406795512457161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28587003422418121366552429 10720126283406795512457161)
      ·
        refine ⟨8040094712555096634342871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10720126283406795512457161 8040094712555096634342871)
        ·
          refine ⟨12060142068832644951514307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040094712555096634342871 12060142068832644951514307)
          ·
            refine ⟨18090213103248967427271461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12060142068832644951514307 18090213103248967427271461)
            ·
              refine ⟨3391914956859181392613399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18090213103248967427271461 3391914956859181392613399)
              ·
                refine ⟨5087872435288772088920099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391914956859181392613399 5087872435288772088920099)
                ·
                  refine ⟨7631808652933158133380149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087872435288772088920099 7631808652933158133380149)
                  ·
                    refine ⟨715482061212483575004389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7631808652933158133380149 715482061212483575004389)
                    ·
                      rfl

theorem cell23_4180189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_4180189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180189 prefixEnd_4180189 := by exact prefixLift 4180189
  have htrace : WordTrace (prefixWord ++ tailWord_4180189) baseStart_4180189 baseEnd_4180189 := by
    simpa [prefixWord, tailWord_4180189, baseEnd_4180189] using wordTrace_append hprefix tailTrace_4180189
  have hstable : (prefixWord ++ tailWord_4180189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180189).length < 2 ^ (prefixWord ++ tailWord_4180189).sum := by decide
  have hdescent : baseEnd_4180189 < baseStart_4180189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180192 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2]
def baseStart_4180192 : Nat := 118140960795 + 4180192 * 2 ^ 59
def prefixEnd_4180192 : Nat := 4983230072969 + 3 ^ 40 * 4180192 * 2
def baseEnd_4180192 : Nat := 2146447724079414213275653

theorem tailTrace_4180192 : CollatzResearch.WordTrace tailWord_4180192 prefixEnd_4180192 2146447724079414213275653 := by
  unfold tailWord_4180192
  simp only [CollatzResearch.WordTrace]
  refine ⟨76232063835942889400319415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101642751781257185867092553 76232063835942889400319415)
  ·
    refine ⟨114348095753914334100479123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76232063835942889400319415 114348095753914334100479123)
    ·
      refine ⟨171522143630871501150718685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114348095753914334100479123 171522143630871501150718685)
      ·
        refine ⟨64320803861576812931519507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171522143630871501150718685 64320803861576812931519507)
        ·
          refine ⟨96481205792365219397279261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64320803861576812931519507 96481205792365219397279261)
          ·
            refine ⟨36180452172136957273979723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96481205792365219397279261 36180452172136957273979723)
            ·
              refine ⟨54270678258205435910969585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36180452172136957273979723 54270678258205435910969585)
              ·
                refine ⟨40703008693654076933227189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54270678258205435910969585 40703008693654076933227189)
                ·
                  refine ⟨3815907065030069712490049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40703008693654076933227189 3815907065030069712490049)
                  ·
                    refine ⟨2861930298772552284367537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815907065030069712490049 2861930298772552284367537)
                    ·
                      refine ⟨2146447724079414213275653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861930298772552284367537 2146447724079414213275653)
                      ·
                        rfl

theorem cell23_4180192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_4180192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180192 prefixEnd_4180192 := by exact prefixLift 4180192
  have htrace : WordTrace (prefixWord ++ tailWord_4180192) baseStart_4180192 baseEnd_4180192 := by
    simpa [prefixWord, tailWord_4180192, baseEnd_4180192] using wordTrace_append hprefix tailTrace_4180192
  have hstable : (prefixWord ++ tailWord_4180192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180192).length < 2 ^ (prefixWord ++ tailWord_4180192).sum := by decide
  have hdescent : baseEnd_4180192 < baseStart_4180192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180226 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4180226 : Nat := 118140960795 + 4180226 * 2 ^ 59
def prefixEnd_4180226 : Nat := 4983230072969 + 3 ^ 40 * 4180226 * 2
def baseEnd_4180226 : Nat := 2146465182421667080250497

theorem tailTrace_4180226 : CollatzResearch.WordTrace tailWord_4180226 prefixEnd_4180226 2146465182421667080250497 := by
  unfold tailWord_4180226
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116341938440650651844133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101643578502508401738251021 38116341938440650651844133)
  ·
    refine ⟨7146814113457621997220775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38116341938440650651844133 7146814113457621997220775)
    ·
      refine ⟨10720221170186432995831163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146814113457621997220775 10720221170186432995831163)
      ·
        refine ⟨16080331755279649493746745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720221170186432995831163 16080331755279649493746745)
        ·
          refine ⟨12060248816459737120310059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16080331755279649493746745 12060248816459737120310059)
          ·
            refine ⟨18090373224689605680465089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12060248816459737120310059 18090373224689605680465089)
            ·
              refine ⟨13567779918517204260348817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18090373224689605680465089 13567779918517204260348817)
              ·
                refine ⟨10175834938887903195261613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13567779918517204260348817 10175834938887903195261613)
                ·
                  refine ⟨3815938102082963698223105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10175834938887903195261613 3815938102082963698223105)
                  ·
                    refine ⟨2861953576562222773667329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815938102082963698223105 2861953576562222773667329)
                    ·
                      refine ⟨2146465182421667080250497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861953576562222773667329 2146465182421667080250497)
                      ·
                        rfl

theorem cell23_4180226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4180226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180226 prefixEnd_4180226 := by exact prefixLift 4180226
  have htrace : WordTrace (prefixWord ++ tailWord_4180226) baseStart_4180226 baseEnd_4180226 := by
    simpa [prefixWord, tailWord_4180226, baseEnd_4180226] using wordTrace_append hprefix tailTrace_4180226
  have hstable : (prefixWord ++ tailWord_4180226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180226).length < 2 ^ (prefixWord ++ tailWord_4180226).sum := by decide
  have hdescent : baseEnd_4180226 < baseStart_4180226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180232 : List Nat := [2, 1, 3, 2, 3, 3, 2, 7]
def baseStart_4180232 : Nat := 118140960795 + 4180232 * 2 ^ 59
def prefixEnd_4180232 : Nat := 4983230072969 + 3 ^ 40 * 4180232 * 2
def baseEnd_4180232 : Nat := 79498824566873853954647

theorem tailTrace_4180232 : CollatzResearch.WordTrace tailWord_4180232 prefixEnd_4180232 79498824566873853954647 := by
  unfold tailWord_4180232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76232793295870432816047475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101643724394493910421396633 76232793295870432816047475)
  ·
    refine ⟨114349189943805649224071213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76232793295870432816047475 114349189943805649224071213)
    ·
      refine ⟨42880946228927118459026705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114349189943805649224071213 42880946228927118459026705)
      ·
        refine ⟨32160709671695338844270029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42880946228927118459026705 32160709671695338844270029)
        ·
          refine ⟨12060266126885752066601261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32160709671695338844270029 12060266126885752066601261)
          ·
            refine ⟨4522599797582157024975473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12060266126885752066601261 4522599797582157024975473)
            ·
              refine ⟨3391949848186617768731605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522599797582157024975473 3391949848186617768731605)
              ·
                refine ⟨79498824566873853954647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3391949848186617768731605 79498824566873853954647)
                ·
                  rfl

theorem cell23_4180232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 7].length) (baseStart_4180232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180232 prefixEnd_4180232 := by exact prefixLift 4180232
  have htrace : WordTrace (prefixWord ++ tailWord_4180232) baseStart_4180232 baseEnd_4180232 := by
    simpa [prefixWord, tailWord_4180232, baseEnd_4180232] using wordTrace_append hprefix tailTrace_4180232
  have hstable : (prefixWord ++ tailWord_4180232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180232).length < 2 ^ (prefixWord ++ tailWord_4180232).sum := by decide
  have hdescent : baseEnd_4180232 < baseStart_4180232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180252 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_4180252 : Nat := 118140960795 + 4180252 * 2 ^ 59
def prefixEnd_4180252 : Nat := 4983230072969 + 3 ^ 40 * 4180252 * 2
def baseEnd_4180252 : Nat := 2146478532918683978525377

theorem tailTrace_4180252 : CollatzResearch.WordTrace tailWord_4180252 prefixEnd_4180252 2146478532918683978525377 := by
  unfold tailWord_4180252
  simp only [CollatzResearch.WordTrace]
  refine ⟨76233158025834204523911505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101644210701112272698548673 76233158025834204523911505)
  ·
    refine ⟨57174868519375653392933629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76233158025834204523911505 57174868519375653392933629)
    ·
      refine ⟨21440575694765870022350111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57174868519375653392933629 21440575694765870022350111)
      ·
        refine ⟨32160863542148805033525167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21440575694765870022350111 32160863542148805033525167)
        ·
          refine ⟨48241295313223207550287751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32160863542148805033525167 48241295313223207550287751)
          ·
            refine ⟨72361942969834811325431627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48241295313223207550287751 72361942969834811325431627)
            ·
              refine ⟨108542914454752216988147441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72361942969834811325431627 108542914454752216988147441)
              ·
                refine ⟨81407185841064162741110581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108542914454752216988147441 81407185841064162741110581)
                ·
                  refine ⟨7631923672599765256979117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81407185841064162741110581 7631923672599765256979117)
                  ·
                    refine ⟨2861971377224911971367169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7631923672599765256979117 2861971377224911971367169)
                    ·
                      refine ⟨2146478532918683978525377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861971377224911971367169 2146478532918683978525377)
                      ·
                        rfl

theorem cell23_4180252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_4180252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180252 prefixEnd_4180252 := by exact prefixLift 4180252
  have htrace : WordTrace (prefixWord ++ tailWord_4180252) baseStart_4180252 baseEnd_4180252 := by
    simpa [prefixWord, tailWord_4180252, baseEnd_4180252] using wordTrace_append hprefix tailTrace_4180252
  have hstable : (prefixWord ++ tailWord_4180252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180252).length < 2 ^ (prefixWord ++ tailWord_4180252).sum := by decide
  have hdescent : baseEnd_4180252 < baseStart_4180252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180270 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4180270 : Nat := 118140960795 + 4180270 * 2 ^ 59
def prefixEnd_4180270 : Nat := 4983230072969 + 3 ^ 40 * 4180270 * 2
def baseEnd_4180270 : Nat := 715495925190154969366765

theorem tailTrace_4180270 : CollatzResearch.WordTrace tailWord_4180270 prefixEnd_4180270 715495925190154969366765 := by
  unfold tailWord_4180270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19058371570700399765247283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101644648377068798747985509 19058371570700399765247283)
  ·
    refine ⟨28587557356050599647870925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19058371570700399765247283 28587557356050599647870925)
    ·
      refine ⟨10720334008518974867951597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28587557356050599647870925 10720334008518974867951597)
      ·
        refine ⟨4020125253194615575481849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10720334008518974867951597 4020125253194615575481849)
        ·
          refine ⟨3015093939895961681611387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4020125253194615575481849 3015093939895961681611387)
          ·
            refine ⟨4522640909843942522417081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015093939895961681611387 4522640909843942522417081)
            ·
              refine ⟨3391980682382956891812811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522640909843942522417081 3391980682382956891812811)
              ·
                refine ⟨5087971023574435337719217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391980682382956891812811 5087971023574435337719217)
                ·
                  refine ⟨3815978267680826503289413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5087971023574435337719217 3815978267680826503289413)
                  ·
                    refine ⟨715495925190154969366765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815978267680826503289413 715495925190154969366765)
                    ·
                      rfl

theorem cell23_4180270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4180270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180270 prefixEnd_4180270 := by exact prefixLift 4180270
  have htrace : WordTrace (prefixWord ++ tailWord_4180270) baseStart_4180270 baseEnd_4180270 := by
    simpa [prefixWord, tailWord_4180270, baseEnd_4180270] using wordTrace_append hprefix tailTrace_4180270
  have hstable : (prefixWord ++ tailWord_4180270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180270).length < 2 ^ (prefixWord ++ tailWord_4180270).sum := by decide
  have hdescent : baseEnd_4180270 < baseStart_4180270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180276 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4180276 : Nat := 118140960795 + 4180276 * 2 ^ 59
def prefixEnd_4180276 : Nat := 4983230072969 + 3 ^ 40 * 4180276 * 2
def baseEnd_4180276 : Nat := 2146490856454391884625267

theorem tailTrace_4180276 : CollatzResearch.WordTrace tailWord_4180276 prefixEnd_4180276 2146490856454391884625267 := by
  unfold tailWord_4180276
  simp only [CollatzResearch.WordTrace]
  refine ⟨76233595701790730573348341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101644794269054307431131121 76233595701790730573348341)
  ·
    refine ⟨7146899597042880991251407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76233595701790730573348341 7146899597042880991251407)
    ·
      refine ⟨10720349395564321486877111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146899597042880991251407 10720349395564321486877111)
      ·
        refine ⟨16080524093346482230315667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720349395564321486877111 16080524093346482230315667)
        ·
          refine ⟨24120786140019723345473501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080524093346482230315667 24120786140019723345473501)
          ·
            refine ⟨9045294802507396254552563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24120786140019723345473501 9045294802507396254552563)
            ·
              refine ⟨13567942203761094381828845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045294802507396254552563 13567942203761094381828845)
              ·
                refine ⟨5087978326410410393185817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13567942203761094381828845 5087978326410410393185817)
                ·
                  refine ⟨3815983744807807794889363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5087978326410410393185817 3815983744807807794889363)
                  ·
                    refine ⟨5723975617211711692334045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3815983744807807794889363 5723975617211711692334045)
                    ·
                      refine ⟨2146490856454391884625267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5723975617211711692334045 2146490856454391884625267)
                      ·
                        rfl

theorem cell23_4180276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4180276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180276 prefixEnd_4180276 := by exact prefixLift 4180276
  have htrace : WordTrace (prefixWord ++ tailWord_4180276) baseStart_4180276 baseEnd_4180276 := by
    simpa [prefixWord, tailWord_4180276, baseEnd_4180276] using wordTrace_append hprefix tailTrace_4180276
  have hstable : (prefixWord ++ tailWord_4180276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180276).length < 2 ^ (prefixWord ++ tailWord_4180276).sum := by decide
  have hdescent : baseEnd_4180276 < baseStart_4180276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180286 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_4180286 : Nat := 118140960795 + 4180286 * 2 ^ 59
def prefixEnd_4180286 : Nat := 4983230072969 + 3 ^ 40 * 4180286 * 2
def baseEnd_4180286 : Nat := 2146495991260936845500221

theorem tailTrace_4180286 : CollatzResearch.WordTrace tailWord_4180286 prefixEnd_4180286 2146495991260936845500221 := by
  unfold tailWord_4180286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19058444516693154106820089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101645037422363488569707141 19058444516693154106820089)
  ·
    refine ⟨14293833387519865580115067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19058444516693154106820089 14293833387519865580115067)
    ·
      refine ⟨21440750081279798370172601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14293833387519865580115067 21440750081279798370172601)
      ·
        refine ⟨16080562560959848777629451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21440750081279798370172601 16080562560959848777629451)
        ·
          refine ⟨24120843841439773166444177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080562560959848777629451 24120843841439773166444177)
          ·
            refine ⟨18090632881079829874833133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24120843841439773166444177 18090632881079829874833133)
            ·
              refine ⟨6783987330404936203062425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18090632881079829874833133 6783987330404936203062425)
              ·
                refine ⟨5087990497803702152296819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6783987330404936203062425 5087990497803702152296819)
                ·
                  refine ⟨7631985746705553228445229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087990497803702152296819 7631985746705553228445229)
                  ·
                    refine ⟨2861994655014582460666961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7631985746705553228445229 2861994655014582460666961)
                    ·
                      refine ⟨2146495991260936845500221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2861994655014582460666961 2146495991260936845500221)
                      ·
                        rfl

theorem cell23_4180286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_4180286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180286 prefixEnd_4180286 := by exact prefixLift 4180286
  have htrace : WordTrace (prefixWord ++ tailWord_4180286) baseStart_4180286 baseEnd_4180286 := by
    simpa [prefixWord, tailWord_4180286, baseEnd_4180286] using wordTrace_append hprefix tailTrace_4180286
  have hstable : (prefixWord ++ tailWord_4180286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180286).length < 2 ^ (prefixWord ++ tailWord_4180286).sum := by decide
  have hdescent : baseEnd_4180286 < baseStart_4180286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180375 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_4180375 : Nat := 118140960795 + 4180375 * 2 ^ 59
def prefixEnd_4180375 : Nat := 4983230072969 + 3 ^ 40 * 4180375 * 2
def baseEnd_4180375 : Nat := 2146541691039186997287311

theorem tailTrace_4180375 : CollatzResearch.WordTrace tailWord_4180375 prefixEnd_4180375 2146541691039186997287311 := by
  unfold tailWord_4180375
  simp only [CollatzResearch.WordTrace]
  refine ⟨152470802230222801054550579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101647201486815200703033719 152470802230222801054550579)
  ·
    refine ⟨228706203345334201581825869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152470802230222801054550579 228706203345334201581825869)
    ·
      refine ⟨85764826254500325593184701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228706203345334201581825869 85764826254500325593184701)
      ·
        refine ⟨32161809845437622097444263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85764826254500325593184701 32161809845437622097444263)
        ·
          refine ⟨48242714768156433146166395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32161809845437622097444263 48242714768156433146166395)
          ·
            refine ⟨72364072152234649719249593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48242714768156433146166395 72364072152234649719249593)
            ·
              refine ⟨54273054114175987289437195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72364072152234649719249593 54273054114175987289437195)
              ·
                refine ⟨81409581171263980934155793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54273054114175987289437195 81409581171263980934155793)
                ·
                  refine ⟨61057185878447985700616845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81409581171263980934155793 61057185878447985700616845)
                  ·
                    refine ⟨22896444704417994637731317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61057185878447985700616845 22896444704417994637731317)
                    ·
                      refine ⟨2146541691039186997287311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22896444704417994637731317 2146541691039186997287311)
                      ·
                        rfl

theorem cell23_4180375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_4180375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180375 prefixEnd_4180375 := by exact prefixLift 4180375
  have htrace : WordTrace (prefixWord ++ tailWord_4180375) baseStart_4180375 baseEnd_4180375 := by
    simpa [prefixWord, tailWord_4180375, baseEnd_4180375] using wordTrace_append hprefix tailTrace_4180375
  have hstable : (prefixWord ++ tailWord_4180375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180375).length < 2 ^ (prefixWord ++ tailWord_4180375).sum := by decide
  have hdescent : baseEnd_4180375 < baseStart_4180375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180412 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 8]
def baseStart_4180412 : Nat := 118140960795 + 4180412 * 2 ^ 59
def prefixEnd_4180412 : Nat := 4983230072969 + 3 ^ 40 * 4180412 * 2
def baseEnd_4180412 : Nat := 238506743313711483613849

theorem tailTrace_4180412 : CollatzResearch.WordTrace tailWord_4180412 prefixEnd_4180412 238506743313711483613849 := by
  unfold tailWord_4180412
  simp only [CollatzResearch.WordTrace]
  refine ⟨76236075865544378186823745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101648101154059170915764993 76236075865544378186823745)
  ·
    refine ⟨57177056899158283640117809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76236075865544378186823745 57177056899158283640117809)
    ·
      refine ⟨42882792674368712730088357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57177056899158283640117809 42882792674368712730088357)
      ·
        refine ⟨8040523626444133636891567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42882792674368712730088357 8040523626444133636891567)
        ·
          refine ⟨12060785439666200455337351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040523626444133636891567 12060785439666200455337351)
          ·
            refine ⟨18091178159499300683006027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12060785439666200455337351 18091178159499300683006027)
            ·
              refine ⟨27136767239248951024509041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091178159499300683006027 27136767239248951024509041)
              ·
                refine ⟨20352575429436713268381781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27136767239248951024509041 20352575429436713268381781)
                ·
                  refine ⟨238506743313711483613849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20352575429436713268381781 238506743313711483613849)
                  ·
                    rfl

theorem cell23_4180412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_4180412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180412 prefixEnd_4180412 := by exact prefixLift 4180412
  have htrace : WordTrace (prefixWord ++ tailWord_4180412) baseStart_4180412 baseEnd_4180412 := by
    simpa [prefixWord, tailWord_4180412, baseEnd_4180412] using wordTrace_append hprefix tailTrace_4180412
  have hstable : (prefixWord ++ tailWord_4180412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180412).length < 2 ^ (prefixWord ++ tailWord_4180412).sum := by decide
  have hdescent : baseEnd_4180412 < baseStart_4180412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180442 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_4180442 : Nat := 118140960795 + 4180442 * 2 ^ 59
def prefixEnd_4180442 : Nat := 4983230072969 + 3 ^ 40 * 4180442 * 2
def baseEnd_4180442 : Nat := 715525364747679411716501

theorem tailTrace_4180442 : CollatzResearch.WordTrace tailWord_4180442 prefixEnd_4180442 715525364747679411716501 := by
  unfold tailWord_4180442
  simp only [CollatzResearch.WordTrace]
  refine ⟨38118311480245017874309895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101648830613986714331493053 38118311480245017874309895)
  ·
    refine ⟨57177467220367526811464843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38118311480245017874309895 57177467220367526811464843)
    ·
      refine ⟨85766200830551290217197265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57177467220367526811464843 85766200830551290217197265)
      ·
        refine ⟨64324650622913467662897949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85766200830551290217197265 64324650622913467662897949)
        ·
          refine ⟨24121743983592550373586731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64324650622913467662897949 24121743983592550373586731)
          ·
            refine ⟨36182615975388825560380097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24121743983592550373586731 36182615975388825560380097)
            ·
              refine ⟨27136961981541619170285073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36182615975388825560380097 27136961981541619170285073)
              ·
                refine ⟨20352721486156214377713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27136961981541619170285073 20352721486156214377713805)
                ·
                  refine ⟨7632270557308580391642677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20352721486156214377713805 7632270557308580391642677)
                  ·
                    refine ⟨715525364747679411716501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632270557308580391642677 715525364747679411716501)
                    ·
                      rfl

theorem cell23_4180442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_4180442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180442 prefixEnd_4180442 := by exact prefixLift 4180442
  have htrace : WordTrace (prefixWord ++ tailWord_4180442) baseStart_4180442 baseEnd_4180442 := by
    simpa [prefixWord, tailWord_4180442, baseEnd_4180442] using wordTrace_append hprefix tailTrace_4180442
  have hstable : (prefixWord ++ tailWord_4180442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180442).length < 2 ^ (prefixWord ++ tailWord_4180442).sum := by decide
  have hdescent : baseEnd_4180442 < baseStart_4180442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180449 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_4180449 : Nat := 118140960795 + 4180449 * 2 ^ 59
def prefixEnd_4180449 : Nat := 4983230072969 + 3 ^ 40 * 4180449 * 2
def baseEnd_4180449 : Nat := 2146579688607619707761971

theorem tailTrace_4180449 : CollatzResearch.WordTrace tailWord_4180449 prefixEnd_4180449 2146579688607619707761971 := by
  unfold tailWord_4180449
  simp only [CollatzResearch.WordTrace]
  refine ⟨152473501231954711692744401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101649000821303141128496267 152473501231954711692744401)
  ·
    refine ⟨114355125923966033769558301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152473501231954711692744401 114355125923966033769558301)
    ·
      refine ⟨42883172221487262663584363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114355125923966033769558301 42883172221487262663584363)
      ·
        refine ⟨64324758332230893995376545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42883172221487262663584363 64324758332230893995376545)
        ·
          refine ⟨48243568749173170496532409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64324758332230893995376545 48243568749173170496532409)
          ·
            refine ⟨36182676561879877872399307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48243568749173170496532409 36182676561879877872399307)
            ·
              refine ⟨54274014842819816808598961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36182676561879877872399307 54274014842819816808598961)
              ·
                refine ⟨40705511132114862606449221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54274014842819816808598961 40705511132114862606449221)
                ·
                  refine ⟨7632283337271536738709229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40705511132114862606449221 7632283337271536738709229)
                  ·
                    refine ⟨2862106251476826277015961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7632283337271536738709229 2862106251476826277015961)
                    ·
                      refine ⟨2146579688607619707761971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862106251476826277015961 2146579688607619707761971)
                      ·
                        rfl

theorem cell23_4180449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_4180449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180449 prefixEnd_4180449 := by exact prefixLift 4180449
  have htrace : WordTrace (prefixWord ++ tailWord_4180449) baseStart_4180449 baseEnd_4180449 := by
    simpa [prefixWord, tailWord_4180449, baseEnd_4180449] using wordTrace_append hprefix tailTrace_4180449
  have hstable : (prefixWord ++ tailWord_4180449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180449).length < 2 ^ (prefixWord ++ tailWord_4180449).sum := by decide
  have hdescent : baseEnd_4180449 < baseStart_4180449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180472 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_4180472 : Nat := 118140960795 + 4180472 * 2 ^ 59
def prefixEnd_4180472 : Nat := 4983230072969 + 3 ^ 40 * 4180472 * 2
def baseEnd_4180472 : Nat := 715530499554224372591455

theorem tailTrace_4180472 : CollatzResearch.WordTrace tailWord_4180472 prefixEnd_4180472 715530499554224372591455 := by
  unfold tailWord_4180472
  simp only [CollatzResearch.WordTrace]
  refine ⟨76237170055435693310415835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101649560073914257747221113 76237170055435693310415835)
  ·
    refine ⟨114355755083153539965623753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76237170055435693310415835 114355755083153539965623753)
    ·
      refine ⟨85766816312365154974217815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114355755083153539965623753 85766816312365154974217815)
      ·
        refine ⟨128650224468547732461326723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85766816312365154974217815 128650224468547732461326723)
        ·
          refine ⟨192975336702821598691990085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128650224468547732461326723 192975336702821598691990085)
          ·
            refine ⟨36182875631779049754748141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192975336702821598691990085 36182875631779049754748141)
            ·
              refine ⟨13568578361917143658030553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36182875631779049754748141 13568578361917143658030553)
              ·
                refine ⟨10176433771437857743522915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13568578361917143658030553 10176433771437857743522915)
                ·
                  refine ⟨15264650657156786615284373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10176433771437857743522915 15264650657156786615284373)
                  ·
                    refine ⟨715530499554224372591455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15264650657156786615284373 715530499554224372591455)
                    ·
                      rfl

theorem cell23_4180472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_4180472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180472 prefixEnd_4180472 := by exact prefixLift 4180472
  have htrace : WordTrace (prefixWord ++ tailWord_4180472) baseStart_4180472 baseEnd_4180472 := by
    simpa [prefixWord, tailWord_4180472, baseEnd_4180472] using wordTrace_append hprefix tailTrace_4180472
  have hstable : (prefixWord ++ tailWord_4180472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180472).length < 2 ^ (prefixWord ++ tailWord_4180472).sum := by decide
  have hdescent : baseEnd_4180472 < baseStart_4180472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180509 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4180509 : Nat := 118140960795 + 4180509 * 2 ^ 59
def prefixEnd_4180509 : Nat := 4983230072969 + 3 ^ 40 * 4180509 * 2
def baseEnd_4180509 : Nat := 2146610497446889473011695

theorem tailTrace_4180509 : CollatzResearch.WordTrace tailWord_4180509 prefixEnd_4180509 2146610497446889473011695 := by
  unfold tailWord_4180509
  simp only [CollatzResearch.WordTrace]
  refine ⟨152475689611737341939928581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101650459741158227959952387 152475689611737341939928581)
  ·
    refine ⟨28589191802200751613736609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152475689611737341939928581 28589191802200751613736609)
    ·
      refine ⟨21441893851650563710302457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28589191802200751613736609 21441893851650563710302457)
      ·
        refine ⟨16081420388737922782726843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21441893851650563710302457 16081420388737922782726843)
        ·
          refine ⟨24122130583106884174090265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081420388737922782726843 24122130583106884174090265)
          ·
            refine ⟨18091597937330163130567699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24122130583106884174090265 18091597937330163130567699)
            ·
              refine ⟨27137396905995244695851549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091597937330163130567699 27137396905995244695851549)
              ·
                refine ⟨10176523839748216760944331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27137396905995244695851549 10176523839748216760944331)
                ·
                  refine ⟨15264785759622325141416497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10176523839748216760944331 15264785759622325141416497)
                  ·
                    refine ⟨11448589319716743856062373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15264785759622325141416497 11448589319716743856062373)
                    ·
                      refine ⟨2146610497446889473011695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11448589319716743856062373 2146610497446889473011695)
                      ·
                        rfl

theorem cell23_4180509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4180509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180509 prefixEnd_4180509 := by exact prefixLift 4180509
  have htrace : WordTrace (prefixWord ++ tailWord_4180509) baseStart_4180509 baseEnd_4180509 := by
    simpa [prefixWord, tailWord_4180509, baseEnd_4180509] using wordTrace_append hprefix tailTrace_4180509
  have hstable : (prefixWord ++ tailWord_4180509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180509).length < 2 ^ (prefixWord ++ tailWord_4180509).sum := by decide
  have hdescent : baseEnd_4180509 < baseStart_4180509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
