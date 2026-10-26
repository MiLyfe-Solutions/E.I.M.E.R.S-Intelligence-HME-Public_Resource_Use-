import V185TrunkScan23Chunk0746

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4417261 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4417261 : Nat := 118140960795 + 4417261 * 2 ^ 59
def prefixEnd_4417261 : Nat := 4983230072969 + 3 ^ 40 * 4417261 * 2
def baseEnd_4417261 : Nat := 2268178069360147179722893

theorem tailTrace_4417261 : CollatzResearch.WordTrace tailWord_4417261 prefixEnd_4417261 2268178069360147179722893 := by
  unfold tailWord_4417261
  simp only [CollatzResearch.WordTrace]
  refine ⟨161110744450025279962411637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107407162966683519974941091 161110744450025279962411637)
  ·
    refine ⟨15104132292189869996476091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161110744450025279962411637 15104132292189869996476091)
    ·
      refine ⟨22656198438284804994714137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15104132292189869996476091 22656198438284804994714137)
      ·
        refine ⟨16992148828713603746035603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22656198438284804994714137 16992148828713603746035603)
        ·
          refine ⟨25488223243070405619053405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16992148828713603746035603 25488223243070405619053405)
          ·
            refine ⟨9558083716151402107145027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25488223243070405619053405 9558083716151402107145027)
            ·
              refine ⟨14337125574227103160717541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9558083716151402107145027 14337125574227103160717541)
              ·
                refine ⟨2688211045167581842634539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14337125574227103160717541 2688211045167581842634539)
                ·
                  refine ⟨4032316567751372763951809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688211045167581842634539 4032316567751372763951809)
                  ·
                    refine ⟨3024237425813529572963857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4032316567751372763951809 3024237425813529572963857)
                    ·
                      refine ⟨2268178069360147179722893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024237425813529572963857 2268178069360147179722893)
                      ·
                        rfl

theorem cell23_4417261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4417261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417261 prefixEnd_4417261 := by exact prefixLift 4417261
  have htrace : WordTrace (prefixWord ++ tailWord_4417261) baseStart_4417261 baseEnd_4417261 := by
    simpa [prefixWord, tailWord_4417261, baseEnd_4417261] using wordTrace_append hprefix tailTrace_4417261
  have hstable : (prefixWord ++ tailWord_4417261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417261).length < 2 ^ (prefixWord ++ tailWord_4417261).sum := by decide
  have hdescent : baseEnd_4417261 < baseStart_4417261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417304 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4417304 : Nat := 118140960795 + 4417304 * 2 ^ 59
def prefixEnd_4417304 : Nat := 4983230072969 + 3 ^ 40 * 4417304 * 2
def baseEnd_4417304 : Nat := 2268200149028290511485195

theorem tailTrace_4417304 : CollatzResearch.WordTrace tailWord_4417304 prefixEnd_4417304 2268200149028290511485195 := by
  unfold tailWord_4417304
  simp only [CollatzResearch.WordTrace]
  refine ⟨80556156394434749153113483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107408208525912998870817977 80556156394434749153113483)
  ·
    refine ⟨120834234591652123729670225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80556156394434749153113483 120834234591652123729670225)
    ·
      refine ⟨90625675943739092797252669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120834234591652123729670225 90625675943739092797252669)
      ·
        refine ⟨33984628478902159798969751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90625675943739092797252669 33984628478902159798969751)
        ·
          refine ⟨50976942718353239698454627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33984628478902159798969751 50976942718353239698454627)
          ·
            refine ⟨76465414077529859547681941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50976942718353239698454627 76465414077529859547681941)
            ·
              refine ⟨3584316284884212166297591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76465414077529859547681941 3584316284884212166297591)
              ·
                refine ⟨5376474427326318249446387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584316284884212166297591 5376474427326318249446387)
                ·
                  refine ⟨8064711640989477374169581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5376474427326318249446387 8064711640989477374169581)
                  ·
                    refine ⟨3024266865371054015313593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8064711640989477374169581 3024266865371054015313593)
                    ·
                      refine ⟨2268200149028290511485195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024266865371054015313593 2268200149028290511485195)
                      ·
                        rfl

theorem cell23_4417304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4417304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417304 prefixEnd_4417304 := by exact prefixLift 4417304
  have htrace : WordTrace (prefixWord ++ tailWord_4417304) baseStart_4417304 baseEnd_4417304 := by
    simpa [prefixWord, tailWord_4417304, baseEnd_4417304] using wordTrace_append hprefix tailTrace_4417304
  have hstable : (prefixWord ++ tailWord_4417304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417304).length < 2 ^ (prefixWord ++ tailWord_4417304).sum := by decide
  have hdescent : baseEnd_4417304 < baseStart_4417304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417330 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4417330 : Nat := 118140960795 + 4417330 * 2 ^ 59
def prefixEnd_4417330 : Nat := 4983230072969 + 3 ^ 40 * 4417330 * 2
def baseEnd_4417330 : Nat := 2268213499525307409760075

theorem tailTrace_4417330 : CollatzResearch.WordTrace tailWord_4417330 prefixEnd_4417330 2268213499525307409760075 := by
  unfold tailWord_4417330
  simp only [CollatzResearch.WordTrace]
  refine ⟨40278315271693826186668361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107408840724516869831115629 40278315271693826186668361)
  ·
    refine ⟨30208736453770369640001271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40278315271693826186668361 30208736453770369640001271)
    ·
      refine ⟨45313104680655554460001907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30208736453770369640001271 45313104680655554460001907)
      ·
        refine ⟨67969657020983331690002861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45313104680655554460001907 67969657020983331690002861)
        ·
          refine ⟨25488621382868749383751073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67969657020983331690002861 25488621382868749383751073)
          ·
            refine ⟨19116466037151562037813305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25488621382868749383751073 19116466037151562037813305)
            ·
              refine ⟨14337349527863671528359979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19116466037151562037813305 14337349527863671528359979)
              ·
                refine ⟨21506024291795507292539969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14337349527863671528359979 21506024291795507292539969)
                ·
                  refine ⟨16129518218846630469404977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21506024291795507292539969 16129518218846630469404977)
                  ·
                    refine ⟨12097138664134972852053733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16129518218846630469404977 12097138664134972852053733)
                    ·
                      refine ⟨2268213499525307409760075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12097138664134972852053733 2268213499525307409760075)
                      ·
                        rfl

theorem cell23_4417330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4417330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417330 prefixEnd_4417330 := by exact prefixLift 4417330
  have htrace : WordTrace (prefixWord ++ tailWord_4417330) baseStart_4417330 baseEnd_4417330 := by
    simpa [prefixWord, tailWord_4417330, baseEnd_4417330] using wordTrace_append hprefix tailTrace_4417330
  have hstable : (prefixWord ++ tailWord_4417330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417330).length < 2 ^ (prefixWord ++ tailWord_4417330).sum := by decide
  have hdescent : baseEnd_4417330 < baseStart_4417330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417353 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_4417353 : Nat := 118140960795 + 4417353 * 2 ^ 59
def prefixEnd_4417353 : Nat := 4983230072969 + 3 ^ 40 * 4417353 * 2
def baseEnd_4417353 : Nat := 756075103193453606590823

theorem tailTrace_4417353 : CollatzResearch.WordTrace tailWord_4417353 prefixEnd_4417353 756075103193453606590823 := by
  unfold tailWord_4417353
  simp only [CollatzResearch.WordTrace]
  refine ⟨161114099965691979674760713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107409399977127986449840475 161114099965691979674760713)
  ·
    refine ⟨120835574974268984756070535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161114099965691979674760713 120835574974268984756070535)
    ·
      refine ⟨181253362461403477134105803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120835574974268984756070535 181253362461403477134105803)
      ·
        refine ⟨271880043692105215701158705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181253362461403477134105803 271880043692105215701158705)
        ·
          refine ⟨203910032769078911775869029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271880043692105215701158705 203910032769078911775869029)
          ·
            refine ⟨38233131144202295957975443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203910032769078911775869029 38233131144202295957975443)
            ·
              refine ⟨57349696716303443936963165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38233131144202295957975443 57349696716303443936963165)
              ·
                refine ⟨21506136268613791476361187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57349696716303443936963165 21506136268613791476361187)
                ·
                  refine ⟨32259204402920687214541781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21506136268613791476361187 32259204402920687214541781)
                  ·
                    refine ⟨756075103193453606590823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32259204402920687214541781 756075103193453606590823)
                    ·
                      rfl

theorem cell23_4417353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_4417353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417353 prefixEnd_4417353 := by exact prefixLift 4417353
  have htrace : WordTrace (prefixWord ++ tailWord_4417353) baseStart_4417353 baseEnd_4417353 := by
    simpa [prefixWord, tailWord_4417353, baseEnd_4417353] using wordTrace_append hprefix tailTrace_4417353
  have hstable : (prefixWord ++ tailWord_4417353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417353).length < 2 ^ (prefixWord ++ tailWord_4417353).sum := by decide
  have hdescent : baseEnd_4417353 < baseStart_4417353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417360 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2]
def baseStart_4417360 : Nat := 118140960795 + 4417360 * 2 ^ 59
def prefixEnd_4417360 : Nat := 4983230072969 + 3 ^ 40 * 4417360 * 2
def baseEnd_4417360 : Nat := 2268228903944942292384937

theorem tailTrace_4417360 : CollatzResearch.WordTrace tailWord_4417360 prefixEnd_4417360 2268228903944942292384937 := by
  unfold tailWord_4417360
  simp only [CollatzResearch.WordTrace]
  refine ⟨80557177638333309935132767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107409570184444413246843689 80557177638333309935132767)
  ·
    refine ⟨120835766457499964902699151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80557177638333309935132767 120835766457499964902699151)
    ·
      refine ⟨181253649686249947354048727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120835766457499964902699151 181253649686249947354048727)
      ·
        refine ⟨271880474529374921031073091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181253649686249947354048727 271880474529374921031073091)
        ·
          refine ⟨407820711794062381546609637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271880474529374921031073091 407820711794062381546609637)
          ·
            refine ⟨76466383461386696539989307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 407820711794062381546609637 76466383461386696539989307)
            ·
              refine ⟨114699575192080044809983961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76466383461386696539989307 114699575192080044809983961)
              ·
                refine ⟨86024681394060033607487971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114699575192080044809983961 86024681394060033607487971)
                ·
                  refine ⟨129037022091090050411231957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86024681394060033607487971 129037022091090050411231957)
                  ·
                    refine ⟨3024305205259923056513249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129037022091090050411231957 3024305205259923056513249)
                    ·
                      refine ⟨2268228903944942292384937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024305205259923056513249 2268228903944942292384937)
                      ·
                        rfl

theorem cell23_4417360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2].length) (baseStart_4417360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417360 prefixEnd_4417360 := by exact prefixLift 4417360
  have htrace : WordTrace (prefixWord ++ tailWord_4417360) baseStart_4417360 baseEnd_4417360 := by
    simpa [prefixWord, tailWord_4417360, baseEnd_4417360] using wordTrace_append hprefix tailTrace_4417360
  have hstable : (prefixWord ++ tailWord_4417360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417360).length < 2 ^ (prefixWord ++ tailWord_4417360).sum := by decide
  have hdescent : baseEnd_4417360 < baseStart_4417360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417370 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_4417370 : Nat := 118140960795 + 4417370 * 2 ^ 59
def prefixEnd_4417370 : Nat := 4983230072969 + 3 ^ 40 * 4417370 * 2
def baseEnd_4417370 : Nat := 756078012917162417753297

theorem tailTrace_4417370 : CollatzResearch.WordTrace tailWord_4417370 prefixEnd_4417370 756078012917162417753297 := by
  unfold tailWord_4417370
  simp only [CollatzResearch.WordTrace]
  refine ⟨40278680001657597894532391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107409813337753594385419709 40278680001657597894532391)
  ·
    refine ⟨60418020002486396841798587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40278680001657597894532391 60418020002486396841798587)
    ·
      refine ⟨90627030003729595262697881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60418020002486396841798587 90627030003729595262697881)
      ·
        refine ⟨67970272502797196447023411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90627030003729595262697881 67970272502797196447023411)
        ·
          refine ⟨101955408754195794670535117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67970272502797196447023411 101955408754195794670535117)
          ·
            refine ⟨38233278282823423001450669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101955408754195794670535117 38233278282823423001450669)
            ·
              refine ⟨14337479356058783625544001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38233278282823423001450669 14337479356058783625544001)
              ·
                refine ⟨10753109517044087719158001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14337479356058783625544001 10753109517044087719158001)
                ·
                  refine ⟨8064832137783065789368501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10753109517044087719158001 8064832137783065789368501)
                  ·
                    refine ⟨756078012917162417753297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8064832137783065789368501 756078012917162417753297)
                    ·
                      rfl

theorem cell23_4417370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_4417370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417370 prefixEnd_4417370 := by exact prefixLift 4417370
  have htrace : WordTrace (prefixWord ++ tailWord_4417370) baseStart_4417370 baseEnd_4417370 := by
    simpa [prefixWord, tailWord_4417370, baseEnd_4417370] using wordTrace_append hprefix tailTrace_4417370
  have hstable : (prefixWord ++ tailWord_4417370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417370).length < 2 ^ (prefixWord ++ tailWord_4417370).sum := by decide
  have hdescent : baseEnd_4417370 < baseStart_4417370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417403 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_4417403 : Nat := 118140960795 + 4417403 * 2 ^ 59
def prefixEnd_4417403 : Nat := 4983230072969 + 3 ^ 40 * 4417403 * 2
def baseEnd_4417403 : Nat := 2268250983613085624147239

theorem tailTrace_4417403 : CollatzResearch.WordTrace tailWord_4417403 prefixEnd_4417403 2268250983613085624147239 := by
  unfold tailWord_4417403
  simp only [CollatzResearch.WordTrace]
  refine ⟨161115923615510838214080863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107410615743673892142720575 161115923615510838214080863)
  ·
    refine ⟨241673885423266257321121295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161115923615510838214080863 241673885423266257321121295)
    ·
      refine ⟨362510828134899385981681943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241673885423266257321121295 362510828134899385981681943)
      ·
        refine ⟨543766242202349078972522915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362510828134899385981681943 543766242202349078972522915)
        ·
          refine ⟨815649363303523618458784373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543766242202349078972522915 815649363303523618458784373)
          ·
            refine ⟨76467127809705339230511035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 815649363303523618458784373 76467127809705339230511035)
            ·
              refine ⟨114700691714558008845766553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76467127809705339230511035 114700691714558008845766553)
              ·
                refine ⟨86025518785918506634324915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114700691714558008845766553 86025518785918506634324915)
                ·
                  refine ⟨129038278178877759951487373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86025518785918506634324915 129038278178877759951487373)
                  ·
                    refine ⟨48389354317079159981807765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129038278178877759951487373 48389354317079159981807765)
                    ·
                      refine ⟨2268250983613085624147239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48389354317079159981807765 2268250983613085624147239)
                      ·
                        rfl

theorem cell23_4417403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_4417403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417403 prefixEnd_4417403 := by exact prefixLift 4417403
  have htrace : WordTrace (prefixWord ++ tailWord_4417403) baseStart_4417403 baseEnd_4417403 := by
    simpa [prefixWord, tailWord_4417403, baseEnd_4417403] using wordTrace_append hprefix tailTrace_4417403
  have hstable : (prefixWord ++ tailWord_4417403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417403).length < 2 ^ (prefixWord ++ tailWord_4417403).sum := by decide
  have hdescent : baseEnd_4417403 < baseStart_4417403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417440 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_4417440 : Nat := 118140960795 + 4417440 * 2 ^ 59
def prefixEnd_4417440 : Nat := 4983230072969 + 3 ^ 40 * 4417440 * 2
def baseEnd_4417440 : Nat := 2268269982397301979384569

theorem tailTrace_4417440 : CollatzResearch.WordTrace tailWord_4417440 prefixEnd_4417440 2268269982397301979384569 := by
  unfold tailWord_4417440
  simp only [CollatzResearch.WordTrace]
  refine ⟨80558636558188396766588887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107411515410917862355451849 80558636558188396766588887)
  ·
    refine ⟨120837954837282595149883331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80558636558188396766588887 120837954837282595149883331)
    ·
      refine ⟨181256932255923892724824997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120837954837282595149883331 181256932255923892724824997)
      ·
        refine ⟨33985674797985729885904687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181256932255923892724824997 33985674797985729885904687)
        ·
          refine ⟨50978512196978594828857031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33985674797985729885904687 50978512196978594828857031)
          ·
            refine ⟨76467768295467892243285547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50978512196978594828857031 76467768295467892243285547)
            ·
              refine ⟨114701652443201838364928321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76467768295467892243285547 114701652443201838364928321)
              ·
                refine ⟨86026239332401378773696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114701652443201838364928321 86026239332401378773696241)
                ·
                  refine ⟨64519679499301034080272181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86026239332401378773696241 64519679499301034080272181)
                  ·
                    refine ⟨6048719953059471945025517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64519679499301034080272181 6048719953059471945025517)
                    ·
                      refine ⟨2268269982397301979384569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048719953059471945025517 2268269982397301979384569)
                      ·
                        rfl

theorem cell23_4417440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_4417440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417440 prefixEnd_4417440 := by exact prefixLift 4417440
  have htrace : WordTrace (prefixWord ++ tailWord_4417440) baseStart_4417440 baseEnd_4417440 := by
    simpa [prefixWord, tailWord_4417440, baseEnd_4417440] using wordTrace_append hprefix tailTrace_4417440
  have hstable : (prefixWord ++ tailWord_4417440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417440).length < 2 ^ (prefixWord ++ tailWord_4417440).sum := by decide
  have hdescent : baseEnd_4417440 < baseStart_4417440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417447 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 6]
def baseStart_4417447 : Nat := 118140960795 + 4417447 * 2 ^ 59
def prefixEnd_4417447 : Nat := 4983230072969 + 3 ^ 40 * 4417447 * 2
def baseEnd_4417447 : Nat := 252030397417987050221893

theorem tailTrace_4417447 : CollatzResearch.WordTrace tailWord_4417447 prefixEnd_4417447 252030397417987050221893 := by
  unfold tailWord_4417447
  simp only [CollatzResearch.WordTrace]
  refine ⟨161117528427351433728682595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107411685618234289152455063 161117528427351433728682595)
  ·
    refine ⟨241676292641027150593023893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161117528427351433728682595 241676292641027150593023893)
    ·
      refine ⟨11328576217548147684047995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 241676292641027150593023893 11328576217548147684047995)
      ·
        refine ⟨16992864326322221526071993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11328576217548147684047995 16992864326322221526071993)
        ·
          refine ⟨12744648244741666144553995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16992864326322221526071993 12744648244741666144553995)
          ·
            refine ⟨19116972367112499216830993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12744648244741666144553995 19116972367112499216830993)
            ·
              refine ⟨14337729275334374412623245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19116972367112499216830993 14337729275334374412623245)
              ·
                refine ⟨5376648478250390404733717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14337729275334374412623245 5376648478250390404733717)
                ·
                  refine ⟨252030397417987050221893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5376648478250390404733717 252030397417987050221893)
                  ·
                    rfl

theorem cell23_4417447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 6].length) (baseStart_4417447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417447 prefixEnd_4417447 := by exact prefixLift 4417447
  have htrace : WordTrace (prefixWord ++ tailWord_4417447) baseStart_4417447 baseEnd_4417447 := by
    simpa [prefixWord, tailWord_4417447, baseEnd_4417447] using wordTrace_append hprefix tailTrace_4417447
  have hstable : (prefixWord ++ tailWord_4417447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417447).length < 2 ^ (prefixWord ++ tailWord_4417447).sum := by decide
  have hdescent : baseEnd_4417447 < baseStart_4417447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417468 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_4417468 : Nat := 118140960795 + 4417468 * 2 ^ 59
def prefixEnd_4417468 : Nat := 4983230072969 + 3 ^ 40 * 4417468 * 2
def baseEnd_4417468 : Nat := 756094786618542623278147

theorem tailTrace_4417468 : CollatzResearch.WordTrace tailWord_4417468 prefixEnd_4417468 756094786618542623278147 := by
  unfold tailWord_4417468
  simp only [CollatzResearch.WordTrace]
  refine ⟨80559147180137677157598529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107412196240183569543464705 80559147180137677157598529)
  ·
    refine ⟨60419360385103257868198897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80559147180137677157598529 60419360385103257868198897)
    ·
      refine ⟨45314520288827443401149173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60419360385103257868198897 45314520288827443401149173)
      ·
        refine ⟨4248236277077572818857735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45314520288827443401149173 4248236277077572818857735)
        ·
          refine ⟨6372354415616359228286603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248236277077572818857735 6372354415616359228286603)
          ·
            refine ⟨9558531623424538842429905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372354415616359228286603 9558531623424538842429905)
            ·
              refine ⟨7168898717568404131822429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9558531623424538842429905 7168898717568404131822429)
              ·
                refine ⟨2688337019088151549433411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7168898717568404131822429 2688337019088151549433411)
                ·
                  refine ⟨4032505528632227324150117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688337019088151549433411 4032505528632227324150117)
                  ·
                    refine ⟨756094786618542623278147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4032505528632227324150117 756094786618542623278147)
                    ·
                      rfl

theorem cell23_4417468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_4417468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417468 prefixEnd_4417468 := by exact prefixLift 4417468
  have htrace : WordTrace (prefixWord ++ tailWord_4417468) baseStart_4417468 baseEnd_4417468 := by
    simpa [prefixWord, tailWord_4417468, baseEnd_4417468] using wordTrace_append hprefix tailTrace_4417468
  have hstable : (prefixWord ++ tailWord_4417468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417468).length < 2 ^ (prefixWord ++ tailWord_4417468).sum := by decide
  have hdescent : baseEnd_4417468 < baseStart_4417468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417507 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 1, 6]
def baseStart_4417507 : Nat := 118140960795 + 4417507 * 2 ^ 59
def prefixEnd_4417507 : Nat := 4983230072969 + 3 ^ 40 * 4417507 * 2
def baseEnd_4417507 : Nat := 756101461867051072415587

theorem tailTrace_4417507 : CollatzResearch.WordTrace tailWord_4417507 prefixEnd_4417507 756101461867051072415587 := by
  unfold tailWord_4417507
  simp only [CollatzResearch.WordTrace]
  refine ⟨161119716807134063975866775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107413144538089375983911183 161119716807134063975866775)
  ·
    refine ⟨241679575210701095963800163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161119716807134063975866775 241679575210701095963800163)
    ·
      refine ⟨362519362816051643945700245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241679575210701095963800163 362519362816051643945700245)
      ·
        refine ⟨16993095132002420809954699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 362519362816051643945700245 16993095132002420809954699)
        ·
          refine ⟨25489642698003631214932049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16993095132002420809954699 25489642698003631214932049)
          ·
            refine ⟨19117232023502723411199037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25489642698003631214932049 19117232023502723411199037)
            ·
              refine ⟨7168962008813521279199639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19117232023502723411199037 7168962008813521279199639)
              ·
                refine ⟨10753443013220281918799459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7168962008813521279199639 10753443013220281918799459)
                ·
                  refine ⟨16130164519830422878199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10753443013220281918799459 16130164519830422878199189)
                  ·
                    refine ⟨756101461867051072415587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16130164519830422878199189 756101461867051072415587)
                    ·
                      rfl

theorem cell23_4417507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 6].length) (baseStart_4417507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417507 prefixEnd_4417507 := by exact prefixLift 4417507
  have htrace : WordTrace (prefixWord ++ tailWord_4417507) baseStart_4417507 baseEnd_4417507 := by
    simpa [prefixWord, tailWord_4417507, baseEnd_4417507] using wordTrace_append hprefix tailTrace_4417507
  have hstable : (prefixWord ++ tailWord_4417507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417507).length < 2 ^ (prefixWord ++ tailWord_4417507).sum := by decide
  have hdescent : baseEnd_4417507 < baseStart_4417507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417514 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_4417514 : Nat := 118140960795 + 4417514 * 2 ^ 59
def prefixEnd_4417514 : Nat := 4983230072969 + 3 ^ 40 * 4417514 * 2
def baseEnd_4417514 : Nat := 2268307979965734689859229

theorem tailTrace_4417514 : CollatzResearch.WordTrace tailWord_4417514 prefixEnd_4417514 2268307979965734689859229 := by
  unfold tailWord_4417514
  simp only [CollatzResearch.WordTrace]
  refine ⟨40279993029527176042842899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107413314745405802780914397 40279993029527176042842899)
  ·
    refine ⟨60419989544290764064264349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40279993029527176042842899 60419989544290764064264349)
    ·
      refine ⟨22657496079109036524099131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60419989544290764064264349 22657496079109036524099131)
      ·
        refine ⟨33986244118663554786148697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22657496079109036524099131 33986244118663554786148697)
        ·
          refine ⟨25489683088997666089611523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33986244118663554786148697 25489683088997666089611523)
          ·
            refine ⟨38234524633496499134417285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25489683088997666089611523 38234524633496499134417285)
            ·
              refine ⟨7168973368780593587703241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38234524633496499134417285 7168973368780593587703241)
              ·
                refine ⟨5376730026585445190777431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7168973368780593587703241 5376730026585445190777431)
                ·
                  refine ⟨8065095039878167786166147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5376730026585445190777431 8065095039878167786166147)
                  ·
                    refine ⟨12097642559817251679249221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8065095039878167786166147 12097642559817251679249221)
                    ·
                      refine ⟨2268307979965734689859229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12097642559817251679249221 2268307979965734689859229)
                      ·
                        rfl

theorem cell23_4417514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_4417514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417514 prefixEnd_4417514 := by exact prefixLift 4417514
  have htrace : WordTrace (prefixWord ++ tailWord_4417514) baseStart_4417514 baseEnd_4417514 := by
    simpa [prefixWord, tailWord_4417514, baseEnd_4417514] using wordTrace_append hprefix tailTrace_4417514
  have hstable : (prefixWord ++ tailWord_4417514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417514).length < 2 ^ (prefixWord ++ tailWord_4417514).sum := by decide
  have hdescent : baseEnd_4417514 < baseStart_4417514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417534 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4417534 : Nat := 118140960795 + 4417534 * 2 ^ 59
def prefixEnd_4417534 : Nat := 4983230072969 + 3 ^ 40 * 4417534 * 2
def baseEnd_4417534 : Nat := 2268318249578824611609137

theorem tailTrace_4417534 : CollatzResearch.WordTrace tailWord_4417534 prefixEnd_4417534 2268318249578824611609137 := by
  unfold tailWord_4417534
  simp only [CollatzResearch.WordTrace]
  refine ⟨20140087697254530948387457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107413801052024165058066437 20140087697254530948387457)
  ·
    refine ⟨15105065772940898211290593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20140087697254530948387457 15105065772940898211290593)
    ·
      refine ⟨11328799329705673658467945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15105065772940898211290593 11328799329705673658467945)
      ·
        refine ⟨8496599497279255243850959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11328799329705673658467945 8496599497279255243850959)
        ·
          refine ⟨12744899245918882865776439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8496599497279255243850959 12744899245918882865776439)
          ·
            refine ⟨19117348868878324298664659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12744899245918882865776439 19117348868878324298664659)
            ·
              refine ⟨28676023303317486447996989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19117348868878324298664659 28676023303317486447996989)
              ·
                refine ⟨10753508738744057417998871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28676023303317486447996989 10753508738744057417998871)
                ·
                  refine ⟨16130263108116086126998307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10753508738744057417998871 16130263108116086126998307)
                  ·
                    refine ⟨24195394662174129190497461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16130263108116086126998307 24195394662174129190497461)
                    ·
                      refine ⟨2268318249578824611609137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24195394662174129190497461 2268318249578824611609137)
                      ·
                        rfl

theorem cell23_4417534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4417534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417534 prefixEnd_4417534 := by exact prefixLift 4417534
  have htrace : WordTrace (prefixWord ++ tailWord_4417534) baseStart_4417534 baseEnd_4417534 := by
    simpa [prefixWord, tailWord_4417534, baseEnd_4417534] using wordTrace_append hprefix tailTrace_4417534
  have hstable : (prefixWord ++ tailWord_4417534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417534).length < 2 ^ (prefixWord ++ tailWord_4417534).sum := by decide
  have hdescent : baseEnd_4417534 < baseStart_4417534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417580 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_4417580 : Nat := 118140960795 + 4417580 * 2 ^ 59
def prefixEnd_4417580 : Nat := 4983230072969 + 3 ^ 40 * 4417580 * 2
def baseEnd_4417580 : Nat := 756113956562977143877975

theorem tailTrace_4417580 : CollatzResearch.WordTrace tailWord_4417580 prefixEnd_4417580 756113956562977143877975 := by
  unfold tailWord_4417580
  simp only [CollatzResearch.WordTrace]
  refine ⟨80561189667934798721637097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107414919557246398295516129 80561189667934798721637097)
  ·
    refine ⟨60420892250951099041227823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80561189667934798721637097 60420892250951099041227823)
    ·
      refine ⟨90631338376426648561841735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60420892250951099041227823 90631338376426648561841735)
      ·
        refine ⟨135947007564639972842762603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90631338376426648561841735 135947007564639972842762603)
        ·
          refine ⟨203920511346959959264143905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135947007564639972842762603 203920511346959959264143905)
          ·
            refine ⟨152940383510219969448107929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203920511346959959264143905 152940383510219969448107929)
            ·
              refine ⟨114705287632664977086080947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152940383510219969448107929 114705287632664977086080947)
              ·
                refine ⟨172057931448997465629121421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114705287632664977086080947 172057931448997465629121421)
                ·
                  refine ⟨64521724293374049610920533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172057931448997465629121421 64521724293374049610920533)
                  ·
                    refine ⟨756113956562977143877975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64521724293374049610920533 756113956562977143877975)
                    ·
                      rfl

theorem cell23_4417580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_4417580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417580 prefixEnd_4417580 := by exact prefixLift 4417580
  have htrace : WordTrace (prefixWord ++ tailWord_4417580) baseStart_4417580 baseEnd_4417580 := by
    simpa [prefixWord, tailWord_4417580, baseEnd_4417580] using wordTrace_append hprefix tailTrace_4417580
  have hstable : (prefixWord ++ tailWord_4417580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417580).length < 2 ^ (prefixWord ++ tailWord_4417580).sum := by decide
  have hdescent : baseEnd_4417580 < baseStart_4417580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417597 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_4417597 : Nat := 118140960795 + 4417597 * 2 ^ 59
def prefixEnd_4417597 : Nat := 4983230072969 + 3 ^ 40 * 4417597 * 2
def baseEnd_4417597 : Nat := 756116866286685955040449

theorem tailTrace_4417597 : CollatzResearch.WordTrace tailWord_4417597 prefixEnd_4417597 756116866286685955040449 := by
  unfold tailWord_4417597
  simp only [CollatzResearch.WordTrace]
  refine ⟨161122999376808009346643045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107415332917872006231095363 161122999376808009346643045)
  ·
    refine ⟨30210562383151501752495571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161122999376808009346643045 30210562383151501752495571)
    ·
      refine ⟨45315843574727252628743357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30210562383151501752495571 45315843574727252628743357)
      ·
        refine ⟨16993441340522719735778759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45315843574727252628743357 16993441340522719735778759)
        ·
          refine ⟨25490162010784079603668139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16993441340522719735778759 25490162010784079603668139)
          ·
            refine ⟨38235243016176119405502209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25490162010784079603668139 38235243016176119405502209)
            ·
              refine ⟨28676432262132089554126657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38235243016176119405502209 28676432262132089554126657)
              ·
                refine ⟨21507324196599067165594993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28676432262132089554126657 21507324196599067165594993)
                ·
                  refine ⟨16130493147449300374196245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21507324196599067165594993 16130493147449300374196245)
                  ·
                    refine ⟨756116866286685955040449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16130493147449300374196245 756116866286685955040449)
                    ·
                      rfl

theorem cell23_4417597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_4417597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417597 prefixEnd_4417597 := by exact prefixLift 4417597
  have htrace : WordTrace (prefixWord ++ tailWord_4417597) baseStart_4417597 baseEnd_4417597 := by
    simpa [prefixWord, tailWord_4417597, baseEnd_4417597] using wordTrace_append hprefix tailTrace_4417597
  have hstable : (prefixWord ++ tailWord_4417597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417597).length < 2 ^ (prefixWord ++ tailWord_4417597).sum := by decide
  have hdescent : baseEnd_4417597 < baseStart_4417597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417607 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_4417607 : Nat := 118140960795 + 4417607 * 2 ^ 59
def prefixEnd_4417607 : Nat := 4983230072969 + 3 ^ 40 * 4417607 * 2
def baseEnd_4417607 : Nat := 2268355733666602825996301

theorem tailTrace_4417607 : CollatzResearch.WordTrace tailWord_4417607 prefixEnd_4417607 2268355733666602825996301 := by
  unfold tailWord_4417607
  simp only [CollatzResearch.WordTrace]
  refine ⟨161123364106771781054507075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107415576071181187369671383 161123364106771781054507075)
  ·
    refine ⟨241685046160157671581760613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161123364106771781054507075 241685046160157671581760613)
    ·
      refine ⟨45315946155029563421580115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241685046160157671581760613 45315946155029563421580115)
      ·
        refine ⟨67973919232544345132370173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45315946155029563421580115 67973919232544345132370173)
        ·
          refine ⟨25490219712204129424638815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67973919232544345132370173 25490219712204129424638815)
          ·
            refine ⟨38235329568306194136958223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25490219712204129424638815 38235329568306194136958223)
            ·
              refine ⟨57352994352459291205437335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38235329568306194136958223 57352994352459291205437335)
              ·
                refine ⟨86029491528688936808156003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57352994352459291205437335 86029491528688936808156003)
                ·
                  refine ⟨129044237293033405212234005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86029491528688936808156003 129044237293033405212234005)
                  ·
                    refine ⟨6048948623110940869323469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 129044237293033405212234005 6048948623110940869323469)
                    ·
                      refine ⟨2268355733666602825996301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048948623110940869323469 2268355733666602825996301)
                      ·
                        rfl

theorem cell23_4417607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_4417607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417607 prefixEnd_4417607 := by exact prefixLift 4417607
  have htrace : WordTrace (prefixWord ++ tailWord_4417607) baseStart_4417607 baseEnd_4417607 := by
    simpa [prefixWord, tailWord_4417607, baseEnd_4417607] using wordTrace_append hprefix tailTrace_4417607
  have hstable : (prefixWord ++ tailWord_4417607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417607).length < 2 ^ (prefixWord ++ tailWord_4417607).sum := by decide
  have hdescent : baseEnd_4417607 < baseStart_4417607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417621 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4417621 : Nat := 118140960795 + 4417621 * 2 ^ 59
def prefixEnd_4417621 : Nat := 4983230072969 + 3 ^ 40 * 4417621 * 2
def baseEnd_4417621 : Nat := 2268362922395765771221237

theorem tailTrace_4417621 : CollatzResearch.WordTrace tailWord_4417621 prefixEnd_4417621 2268362922395765771221237 := by
  unfold tailWord_4417621
  simp only [CollatzResearch.WordTrace]
  refine ⟨161123874728721061445516717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107415916485814040963677811 161123874728721061445516717)
  ·
    refine ⟨60421453023270398042068769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161123874728721061445516717 60421453023270398042068769)
    ·
      refine ⟨45316089767452798531551577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60421453023270398042068769 45316089767452798531551577)
      ·
        refine ⟨33987067325589598898663683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45316089767452798531551577 33987067325589598898663683)
        ·
          refine ⟨50980600988384398347995525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33987067325589598898663683 50980600988384398347995525)
          ·
            refine ⟨9558862685322074690249161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50980600988384398347995525 9558862685322074690249161)
            ·
              refine ⟨7169147013991556017686871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9558862685322074690249161 7169147013991556017686871)
              ·
                refine ⟨10753720520987334026530307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7169147013991556017686871 10753720520987334026530307)
                ·
                  refine ⟨16130580781481001039795461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10753720520987334026530307 16130580781481001039795461)
                  ·
                    refine ⟨3024483896527687694961649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16130580781481001039795461 3024483896527687694961649)
                    ·
                      refine ⟨2268362922395765771221237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024483896527687694961649 2268362922395765771221237)
                      ·
                        rfl

theorem cell23_4417621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4417621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417621 prefixEnd_4417621 := by exact prefixLift 4417621
  have htrace : WordTrace (prefixWord ++ tailWord_4417621) baseStart_4417621 baseEnd_4417621 := by
    simpa [prefixWord, tailWord_4417621, baseEnd_4417621] using wordTrace_append hprefix tailTrace_4417621
  have hstable : (prefixWord ++ tailWord_4417621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417621).length < 2 ^ (prefixWord ++ tailWord_4417621).sum := by decide
  have hdescent : baseEnd_4417621 < baseStart_4417621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417642 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_4417642 : Nat := 118140960795 + 4417642 * 2 ^ 59
def prefixEnd_4417642 : Nat := 4983230072969 + 3 ^ 40 * 4417642 * 2
def baseEnd_4417642 : Nat := 2268373705489510189058641

theorem tailTrace_4417642 : CollatzResearch.WordTrace tailWord_4417642 prefixEnd_4417642 2268373705489510189058641 := by
  unfold tailWord_4417642
  simp only [CollatzResearch.WordTrace]
  refine ⟨40281160165411245508007795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107416427107763321354687453 40281160165411245508007795)
  ·
    refine ⟨60421740248116868262011693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40281160165411245508007795 60421740248116868262011693)
    ·
      refine ⟨22658152593043825598254385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60421740248116868262011693 22658152593043825598254385)
      ·
        refine ⟨16993614444782869198690789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22658152593043825598254385 16993614444782869198690789)
        ·
          refine ⟨3186302708396787974754523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16993614444782869198690789 3186302708396787974754523)
          ·
            refine ⟨4779454062595181962131785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3186302708396787974754523 4779454062595181962131785)
            ·
              refine ⟨3584590546946386471598839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4779454062595181962131785 3584590546946386471598839)
              ·
                refine ⟨5376885820419579707398259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584590546946386471598839 5376885820419579707398259)
                ·
                  refine ⟨8065328730629369561097389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5376885820419579707398259 8065328730629369561097389)
                  ·
                    refine ⟨3024498273986013585411521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8065328730629369561097389 3024498273986013585411521)
                    ·
                      refine ⟨2268373705489510189058641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024498273986013585411521 2268373705489510189058641)
                      ·
                        rfl

theorem cell23_4417642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_4417642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417642 prefixEnd_4417642 := by exact prefixLift 4417642
  have htrace : WordTrace (prefixWord ++ tailWord_4417642) baseStart_4417642 baseEnd_4417642 := by
    simpa [prefixWord, tailWord_4417642, baseEnd_4417642] using wordTrace_append hprefix tailTrace_4417642
  have hstable : (prefixWord ++ tailWord_4417642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417642).length < 2 ^ (prefixWord ++ tailWord_4417642).sum := by decide
  have hdescent : baseEnd_4417642 < baseStart_4417642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417644 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 5]
def baseStart_4417644 : Nat := 118140960795 + 4417644 * 2 ^ 59
def prefixEnd_4417644 : Nat := 4983230072969 + 3 ^ 40 * 4417644 * 2
def baseEnd_4417644 : Nat := 252041636938979909025959

theorem tailTrace_4417644 : CollatzResearch.WordTrace tailWord_4417644 prefixEnd_4417644 252041636938979909025959 := by
  unfold tailWord_4417644
  simp only [CollatzResearch.WordTrace]
  refine ⟨80562356803818868186801993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107416475738425157582402657 80562356803818868186801993)
  ·
    refine ⟨60421767602864151140101495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80562356803818868186801993 60421767602864151140101495)
    ·
      refine ⟨90632651404296226710152243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60421767602864151140101495 90632651404296226710152243)
      ·
        refine ⟨135948977106444340065228365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90632651404296226710152243 135948977106444340065228365)
        ·
          refine ⟨50980866414916627524460637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135948977106444340065228365 50980866414916627524460637)
          ·
            refine ⟨19117824905593735321672739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50980866414916627524460637 19117824905593735321672739)
            ·
              refine ⟨28676737358390602982509109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19117824905593735321672739 28676737358390602982509109)
              ·
                refine ⟨2688444127349119029610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28676737358390602982509109 2688444127349119029610229)
                ·
                  refine ⟨252041636938979909025959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688444127349119029610229 252041636938979909025959)
                  ·
                    rfl

theorem cell23_4417644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_4417644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417644 prefixEnd_4417644 := by exact prefixLift 4417644
  have htrace : WordTrace (prefixWord ++ tailWord_4417644) baseStart_4417644 baseEnd_4417644 := by
    simpa [prefixWord, tailWord_4417644, baseEnd_4417644] using wordTrace_append hprefix tailTrace_4417644
  have hstable : (prefixWord ++ tailWord_4417644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417644).length < 2 ^ (prefixWord ++ tailWord_4417644).sum := by decide
  have hdescent : baseEnd_4417644 < baseStart_4417644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417771 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 2, 3, 2]
def baseStart_4417771 : Nat := 118140960795 + 4417771 * 2 ^ 59
def prefixEnd_4417771 : Nat := 4983230072969 + 3 ^ 40 * 4417771 * 2
def baseEnd_4417771 : Nat := 2268439944493940184345547

theorem tailTrace_4417771 : CollatzResearch.WordTrace tailWord_4417771 prefixEnd_4417771 2268439944493940184345547 := by
  unfold tailWord_4417771
  simp only [CollatzResearch.WordTrace]
  refine ⟨161129345678177637063477167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107419563785451758042318111 161129345678177637063477167)
  ·
    refine ⟨241694018517266455595215751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161129345678177637063477167 241694018517266455595215751)
    ·
      refine ⟨362541027775899683392823627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241694018517266455595215751 362541027775899683392823627)
      ·
        refine ⟨543811541663849525089235441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362541027775899683392823627 543811541663849525089235441)
        ·
          refine ⟨407858656247887143816926581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543811541663849525089235441 407858656247887143816926581)
          ·
            refine ⟨38236749023239419732836867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 407858656247887143816926581 38236749023239419732836867)
            ·
              refine ⟨57355123534859129599255301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38236749023239419732836867 57355123534859129599255301)
              ·
                refine ⟨10754085662786086799860369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57355123534859129599255301 10754085662786086799860369)
                ·
                  refine ⟨8065564247089565099895277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10754085662786086799860369 8065564247089565099895277)
                  ·
                    refine ⟨3024586592658586912460729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8065564247089565099895277 3024586592658586912460729)
                    ·
                      refine ⟨2268439944493940184345547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024586592658586912460729 2268439944493940184345547)
                      ·
                        rfl

theorem cell23_4417771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3, 2].length) (baseStart_4417771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417771 prefixEnd_4417771 := by exact prefixLift 4417771
  have htrace : WordTrace (prefixWord ++ tailWord_4417771) baseStart_4417771 baseEnd_4417771 := by
    simpa [prefixWord, tailWord_4417771, baseEnd_4417771] using wordTrace_append hprefix tailTrace_4417771
  have hstable : (prefixWord ++ tailWord_4417771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417771).length < 2 ^ (prefixWord ++ tailWord_4417771).sum := by decide
  have hdescent : baseEnd_4417771 < baseStart_4417771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417807 : List Nat := [1, 1, 2, 1, 1, 1, 3, 13]
def baseStart_4417807 : Nat := 118140960795 + 4417807 * 2 ^ 59
def prefixEnd_4417807 : Nat := 4983230072969 + 3 ^ 40 * 4417807 * 2
def baseEnd_4417807 : Nat := 84016978881388964573903

theorem tailTrace_4417807 : CollatzResearch.WordTrace tailWord_4417807 prefixEnd_4417807 84016978881388964573903 := by
  unfold tailWord_4417807
  simp only [CollatzResearch.WordTrace]
  refine ⟨161130658706047215211787675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107420439137364810141191783 161130658706047215211787675)
  ·
    refine ⟨241695988059070822817681513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161130658706047215211787675 241695988059070822817681513)
    ·
      refine ⟨181271991044303117113261135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241695988059070822817681513 181271991044303117113261135)
      ·
        refine ⟨271907986566454675669891703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181271991044303117113261135 271907986566454675669891703)
        ·
          refine ⟨407861979849682013504837555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271907986566454675669891703 407861979849682013504837555)
          ·
            refine ⟨611792969774523020257256333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407861979849682013504837555 611792969774523020257256333)
            ·
              refine ⟨229422363665446132596471125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611792969774523020257256333 229422363665446132596471125)
              ·
                refine ⟨84016978881388964573903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 229422363665446132596471125 84016978881388964573903)
                ·
                  rfl

theorem cell23_4417807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 13].length) (baseStart_4417807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417807 prefixEnd_4417807 := by exact prefixLift 4417807
  have htrace : WordTrace (prefixWord ++ tailWord_4417807) baseStart_4417807 baseEnd_4417807 := by
    simpa [prefixWord, tailWord_4417807, baseEnd_4417807] using wordTrace_append hprefix tailTrace_4417807
  have hstable : (prefixWord ++ tailWord_4417807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417807).length < 2 ^ (prefixWord ++ tailWord_4417807).sum := by decide
  have hdescent : baseEnd_4417807 < baseStart_4417807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417818 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_4417818 : Nat := 118140960795 + 4417818 * 2 ^ 59
def prefixEnd_4417818 : Nat := 4983230072969 + 3 ^ 40 * 4417818 * 2
def baseEnd_4417818 : Nat := 2268464078084701500457831

theorem tailTrace_4417818 : CollatzResearch.WordTrace tailWord_4417818 prefixEnd_4417818 2268464078084701500457831 := by
  unfold tailWord_4417818
  simp only [CollatzResearch.WordTrace]
  refine ⟨40282764977251841022609527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107420706606004909393625405 40282764977251841022609527)
  ·
    refine ⟨60424147465877761533914291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40282764977251841022609527 60424147465877761533914291)
    ·
      refine ⟨90636221198816642300871437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60424147465877761533914291 90636221198816642300871437)
      ·
        refine ⟨33988582949556240862826789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90636221198816642300871437 33988582949556240862826789)
        ·
          refine ⟨6372859303041795161780023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33988582949556240862826789 6372859303041795161780023)
          ·
            refine ⟨9559288954562692742670035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372859303041795161780023 9559288954562692742670035)
            ·
              refine ⟨14338933431844039114005053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9559288954562692742670035 14338933431844039114005053)
              ·
                refine ⟨5377100036941514667751895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14338933431844039114005053 5377100036941514667751895)
                ·
                  refine ⟨8065650055412272001627843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5377100036941514667751895 8065650055412272001627843)
                  ·
                    refine ⟨12098475083118408002441765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8065650055412272001627843 12098475083118408002441765)
                    ·
                      refine ⟨2268464078084701500457831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12098475083118408002441765 2268464078084701500457831)
                      ·
                        rfl

theorem cell23_4417818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_4417818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417818 prefixEnd_4417818 := by exact prefixLift 4417818
  have htrace : WordTrace (prefixWord ++ tailWord_4417818) baseStart_4417818 baseEnd_4417818 := by
    simpa [prefixWord, tailWord_4417818, baseEnd_4417818] using wordTrace_append hprefix tailTrace_4417818
  have hstable : (prefixWord ++ tailWord_4417818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417818).length < 2 ^ (prefixWord ++ tailWord_4417818).sum := by decide
  have hdescent : baseEnd_4417818 < baseStart_4417818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417824 : List Nat := [2, 1, 1, 5, 2, 2, 10]
def baseStart_4417824 : Nat := 118140960795 + 4417824 * 2 ^ 59
def prefixEnd_4417824 : Nat := 4983230072969 + 3 ^ 40 * 4417824 * 2
def baseEnd_4417824 : Nat := 28005767394674425641763

theorem tailTrace_4417824 : CollatzResearch.WordTrace tailWord_4417824 prefixEnd_4417824 28005767394674425641763 := by
  unfold tailWord_4417824
  simp only [CollatzResearch.WordTrace]
  refine ⟨80565639373492813557578263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107420852497990418076771017 80565639373492813557578263)
  ·
    refine ⟨120848459060239220336367395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80565639373492813557578263 120848459060239220336367395)
    ·
      refine ⟨181272688590358830504551093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120848459060239220336367395 181272688590358830504551093)
      ·
        refine ⟨16994314555346140359801665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181272688590358830504551093 16994314555346140359801665)
        ·
          refine ⟨12745735916509605269851249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16994314555346140359801665 12745735916509605269851249)
          ·
            refine ⟨9559301937382203952388437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12745735916509605269851249 9559301937382203952388437)
            ·
              refine ⟨28005767394674425641763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9559301937382203952388437 28005767394674425641763)
              ·
                rfl

theorem cell23_4417824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 10].length) (baseStart_4417824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417824 prefixEnd_4417824 := by exact prefixLift 4417824
  have htrace : WordTrace (prefixWord ++ tailWord_4417824) baseStart_4417824 baseEnd_4417824 := by
    simpa [prefixWord, tailWord_4417824, baseEnd_4417824] using wordTrace_append hprefix tailTrace_4417824
  have hstable : (prefixWord ++ tailWord_4417824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417824).length < 2 ^ (prefixWord ++ tailWord_4417824).sum := by decide
  have hdescent : baseEnd_4417824 < baseStart_4417824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417828 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_4417828 : Nat := 118140960795 + 4417828 * 2 ^ 59
def prefixEnd_4417828 : Nat := 4983230072969 + 3 ^ 40 * 4417828 * 2
def baseEnd_4417828 : Nat := 756156404297082153777595

theorem tailTrace_4417828 : CollatzResearch.WordTrace tailWord_4417828 prefixEnd_4417828 756156404297082153777595 := by
  unfold tailWord_4417828
  simp only [CollatzResearch.WordTrace]
  refine ⟨80565712319485567899151069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107420949759314090532201425 80565712319485567899151069)
  ·
    refine ⟨30212142119807087962181651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80565712319485567899151069 30212142119807087962181651)
    ·
      refine ⟨45318213179710631943272477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30212142119807087962181651 45318213179710631943272477)
      ·
        refine ⟨16994329942391486978727179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45318213179710631943272477 16994329942391486978727179)
        ·
          refine ⟨25491494913587230468090769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16994329942391486978727179 25491494913587230468090769)
          ·
            refine ⟨19118621185190422851068077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25491494913587230468090769 19118621185190422851068077)
            ·
              refine ⟨7169482944446408569150529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19118621185190422851068077 7169482944446408569150529)
              ·
                refine ⟨5377112208334806426862897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7169482944446408569150529 5377112208334806426862897)
                ·
                  refine ⟨4032834156251104820147173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5377112208334806426862897 4032834156251104820147173)
                  ·
                    refine ⟨756156404297082153777595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4032834156251104820147173 756156404297082153777595)
                    ·
                      rfl

theorem cell23_4417828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_4417828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417828 prefixEnd_4417828 := by exact prefixLift 4417828
  have htrace : WordTrace (prefixWord ++ tailWord_4417828) baseStart_4417828 baseEnd_4417828 := by
    simpa [prefixWord, tailWord_4417828, baseEnd_4417828] using wordTrace_append hprefix tailTrace_4417828
  have hstable : (prefixWord ++ tailWord_4417828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417828).length < 2 ^ (prefixWord ++ tailWord_4417828).sum := by decide
  have hdescent : baseEnd_4417828 < baseStart_4417828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417864 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_4417864 : Nat := 118140960795 + 4417864 * 2 ^ 59
def prefixEnd_4417864 : Nat := 4983230072969 + 3 ^ 40 * 4417864 * 2
def baseEnd_4417864 : Nat := 2268487698194808320482619

theorem tailTrace_4417864 : CollatzResearch.WordTrace tailWord_4417864 prefixEnd_4417864 2268487698194808320482619 := by
  unfold tailWord_4417864
  simp only [CollatzResearch.WordTrace]
  refine ⟨80566368833420356973306323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107421825111227142631075097 80566368833420356973306323)
  ·
    refine ⟨120849553250130535459959485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80566368833420356973306323 120849553250130535459959485)
    ·
      refine ⟨45318582468798950797484807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120849553250130535459959485 45318582468798950797484807)
      ·
        refine ⟨67977873703198426196227211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45318582468798950797484807 67977873703198426196227211)
        ·
          refine ⟨101966810554797639294340817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67977873703198426196227211 101966810554797639294340817)
          ·
            refine ⟨76475107916098229470755613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101966810554797639294340817 76475107916098229470755613)
            ·
              refine ⟨28678165468536836051533355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76475107916098229470755613 28678165468536836051533355)
              ·
                refine ⟨43017248202805254077300033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28678165468536836051533355 43017248202805254077300033)
                ·
                  refine ⟨32262936152103940557975025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43017248202805254077300033 32262936152103940557975025)
                  ·
                    refine ⟨24197202114077955418481269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32262936152103940557975025 24197202114077955418481269)
                    ·
                      refine ⟨2268487698194808320482619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24197202114077955418481269 2268487698194808320482619)
                      ·
                        rfl

theorem cell23_4417864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_4417864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417864 prefixEnd_4417864 := by exact prefixLift 4417864
  have htrace : WordTrace (prefixWord ++ tailWord_4417864) baseStart_4417864 baseEnd_4417864 := by
    simpa [prefixWord, tailWord_4417864, baseEnd_4417864] using wordTrace_append hprefix tailTrace_4417864
  have hstable : (prefixWord ++ tailWord_4417864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417864).length < 2 ^ (prefixWord ++ tailWord_4417864).sum := by decide
  have hdescent : baseEnd_4417864 < baseStart_4417864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417941 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_4417941 : Nat := 118140960795 + 4417941 * 2 ^ 59
def prefixEnd_4417941 : Nat := 4983230072969 + 3 ^ 40 * 4417941 * 2
def baseEnd_4417941 : Nat := 2268527236205204519219765

theorem tailTrace_4417941 : CollatzResearch.WordTrace tailWord_4417941 prefixEnd_4417941 2268527236205204519219765 := by
  unfold tailWord_4417941
  simp only [CollatzResearch.WordTrace]
  refine ⟨161135546087561756097165677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107423697391707837398110451 161135546087561756097165677)
  ·
    refine ⟨60425829782835658536437129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161135546087561756097165677 60425829782835658536437129)
    ·
      refine ⟨45319372337126743902327847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60425829782835658536437129 45319372337126743902327847)
      ·
        refine ⟨67979058505690115853491771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45319372337126743902327847 67979058505690115853491771)
        ·
          refine ⟨101968587758535173780237657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67979058505690115853491771 101968587758535173780237657)
          ·
            refine ⟨76476440818901380335178243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101968587758535173780237657 76476440818901380335178243)
            ·
              refine ⟨114714661228352070502767365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76476440818901380335178243 114714661228352070502767365)
              ·
                refine ⟨21508998980316013219268881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114714661228352070502767365 21508998980316013219268881)
                ·
                  refine ⟨16131749235237009914451661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21508998980316013219268881 16131749235237009914451661)
                  ·
                    refine ⟨6049405963213878717919373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16131749235237009914451661 6049405963213878717919373)
                    ·
                      refine ⟨2268527236205204519219765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6049405963213878717919373 2268527236205204519219765)
                      ·
                        rfl

theorem cell23_4417941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_4417941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417941 prefixEnd_4417941 := by exact prefixLift 4417941
  have htrace : WordTrace (prefixWord ++ tailWord_4417941) baseStart_4417941 baseEnd_4417941 := by
    simpa [prefixWord, tailWord_4417941, baseEnd_4417941] using wordTrace_append hprefix tailTrace_4417941
  have hstable : (prefixWord ++ tailWord_4417941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417941).length < 2 ^ (prefixWord ++ tailWord_4417941).sum := by decide
  have hdescent : baseEnd_4417941 < baseStart_4417941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418031 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_4418031 : Nat := 118140960795 + 4418031 * 2 ^ 59
def prefixEnd_4418031 : Nat := 4983230072969 + 3 ^ 40 * 4418031 * 2
def baseEnd_4418031 : Nat := 2268573449464109167094351

theorem tailTrace_4418031 : CollatzResearch.WordTrace tailWord_4418031 prefixEnd_4418031 2268573449464109167094351 := by
  unfold tailWord_4418031
  simp only [CollatzResearch.WordTrace]
  refine ⟨161138828657235701467941947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107425885771490467645294631 161138828657235701467941947)
  ·
    refine ⟨241708242985853552201912921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161138828657235701467941947 241708242985853552201912921)
    ·
      refine ⟨181281182239390164151434691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241708242985853552201912921 181281182239390164151434691)
      ·
        refine ⟨271921773359085246227152037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181281182239390164151434691 271921773359085246227152037)
        ·
          refine ⟨50985332504828483667591007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271921773359085246227152037 50985332504828483667591007)
          ·
            refine ⟨76477998757242725501386511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50985332504828483667591007 76477998757242725501386511)
            ·
              refine ⟨114716998135864088252079767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76477998757242725501386511 114716998135864088252079767)
              ·
                refine ⟨172075497203796132378119651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114716998135864088252079767 172075497203796132378119651)
                ·
                  refine ⟨258113245805694198567179477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172075497203796132378119651 258113245805694198567179477)
                  ·
                    refine ⟨6049529198570957778918269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 258113245805694198567179477 6049529198570957778918269)
                    ·
                      refine ⟨2268573449464109167094351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6049529198570957778918269 2268573449464109167094351)
                      ·
                        rfl

theorem cell23_4418031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_4418031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418031 prefixEnd_4418031 := by exact prefixLift 4418031
  have htrace : WordTrace (prefixWord ++ tailWord_4418031) baseStart_4418031 baseEnd_4418031 := by
    simpa [prefixWord, tailWord_4418031, baseEnd_4418031] using wordTrace_append hprefix tailTrace_4418031
  have hstable : (prefixWord ++ tailWord_4418031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418031).length < 2 ^ (prefixWord ++ tailWord_4418031).sum := by decide
  have hdescent : baseEnd_4418031 < baseStart_4418031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418091 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_4418091 : Nat := 118140960795 + 4418091 * 2 ^ 59
def prefixEnd_4418091 : Nat := 4983230072969 + 3 ^ 40 * 4418091 * 2
def baseEnd_4418091 : Nat := 2268604258303378932344075

theorem tailTrace_4418091 : CollatzResearch.WordTrace tailWord_4418091 prefixEnd_4418091 2268604258303378932344075 := by
  unfold tailWord_4418091
  simp only [CollatzResearch.WordTrace]
  refine ⟨161141017037018331715126127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107427344691345554476750751 161141017037018331715126127)
  ·
    refine ⟨241711525555527497572689191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161141017037018331715126127 241711525555527497572689191)
    ·
      refine ⟨362567288333291246359033787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241711525555527497572689191 362567288333291246359033787)
      ·
        refine ⟨543850932499936869538550681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362567288333291246359033787 543850932499936869538550681)
        ·
          refine ⟨407888199374952652153913011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543850932499936869538550681 407888199374952652153913011)
          ·
            refine ⟨611832299062428978230869517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407888199374952652153913011 611832299062428978230869517)
            ·
              refine ⟨229437112148410866836576069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611832299062428978230869517 229437112148410866836576069)
              ·
                refine ⟨43019458527827037531858013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229437112148410866836576069 43019458527827037531858013)
                ·
                  refine ⟨16132296947935139074446755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43019458527827037531858013 16132296947935139074446755)
                  ·
                    refine ⟨24198445421902708611670133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16132296947935139074446755 24198445421902708611670133)
                    ·
                      refine ⟨2268604258303378932344075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24198445421902708611670133 2268604258303378932344075)
                      ·
                        rfl

theorem cell23_4418091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_4418091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418091 prefixEnd_4418091 := by exact prefixLift 4418091
  have htrace : WordTrace (prefixWord ++ tailWord_4418091) baseStart_4418091 baseEnd_4418091 := by
    simpa [prefixWord, tailWord_4418091, baseEnd_4418091] using wordTrace_append hprefix tailTrace_4418091
  have hstable : (prefixWord ++ tailWord_4418091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418091).length < 2 ^ (prefixWord ++ tailWord_4418091).sum := by decide
  have hdescent : baseEnd_4418091 < baseStart_4418091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418098 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_4418098 : Nat := 118140960795 + 4418098 * 2 ^ 59
def prefixEnd_4418098 : Nat := 4983230072969 + 3 ^ 40 * 4418098 * 2
def baseEnd_4418098 : Nat := 756202617555986801652181

theorem tailTrace_4418098 : CollatzResearch.WordTrace tailWord_4418098 prefixEnd_4418098 756202617555986801652181 := by
  unfold tailWord_4418098
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285318086998242977657737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107427514898661981273753965 40285318086998242977657737)
  ·
    refine ⟨30213988565248682233243303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40285318086998242977657737 30213988565248682233243303)
    ·
      refine ⟨45320982847873023349864955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30213988565248682233243303 45320982847873023349864955)
      ·
        refine ⟨67981474271809535024797433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45320982847873023349864955 67981474271809535024797433)
        ·
          refine ⟨50986105703857151268598075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67981474271809535024797433 50986105703857151268598075)
          ·
            refine ⟨76479158555785726902897113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50986105703857151268598075 76479158555785726902897113)
            ·
              refine ⟨57359368916839295177172835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76479158555785726902897113 57359368916839295177172835)
              ·
                refine ⟨86039053375258942765759253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57359368916839295177172835 86039053375258942765759253)
                ·
                  refine ⟨4033080626965262942144965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86039053375258942765759253 4033080626965262942144965)
                  ·
                    refine ⟨756202617555986801652181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033080626965262942144965 756202617555986801652181)
                    ·
                      rfl

theorem cell23_4418098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_4418098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418098 prefixEnd_4418098 := by exact prefixLift 4418098
  have htrace : WordTrace (prefixWord ++ tailWord_4418098) baseStart_4418098 baseEnd_4418098 := by
    simpa [prefixWord, tailWord_4418098, baseEnd_4418098] using wordTrace_append hprefix tailTrace_4418098
  have hstable : (prefixWord ++ tailWord_4418098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418098).length < 2 ^ (prefixWord ++ tailWord_4418098).sum := by decide
  have hdescent : baseEnd_4418098 < baseStart_4418098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418166 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_4418166 : Nat := 118140960795 + 4418166 * 2 ^ 59
def prefixEnd_4418166 : Nat := 4983230072969 + 3 ^ 40 * 4418166 * 2
def baseEnd_4418166 : Nat := 756214256450822046302077

theorem tailTrace_4418166 : CollatzResearch.WordTrace tailWord_4418166 prefixEnd_4418166 756214256450822046302077 := by
  unfold tailWord_4418166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071484531984163720256647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107429168341164413016070901 10071484531984163720256647)
  ·
    refine ⟨15107226797976245580384971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10071484531984163720256647 15107226797976245580384971)
    ·
      refine ⟨22660840196964368370577457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15107226797976245580384971 22660840196964368370577457)
      ·
        refine ⟨16995630147723276277933093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22660840196964368370577457 16995630147723276277933093)
        ·
          refine ⟨3186680652698114302112455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16995630147723276277933093 3186680652698114302112455)
          ·
            refine ⟨4780020979047171453168683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3186680652698114302112455 4780020979047171453168683)
            ·
              refine ⟨7170031468570757179753025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780020979047171453168683 7170031468570757179753025)
              ·
                refine ⟨5377523601428067884814769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7170031468570757179753025 5377523601428067884814769)
                ·
                  refine ⟨4033142701071050913611077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5377523601428067884814769 4033142701071050913611077)
                  ·
                    refine ⟨756214256450822046302077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033142701071050913611077 756214256450822046302077)
                    ·
                      rfl

theorem cell23_4418166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_4418166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418166 prefixEnd_4418166 := by exact prefixLift 4418166
  have htrace : WordTrace (prefixWord ++ tailWord_4418166) baseStart_4418166 baseEnd_4418166 := by
    simpa [prefixWord, tailWord_4418166, baseEnd_4418166] using wordTrace_append hprefix tailTrace_4418166
  have hstable : (prefixWord ++ tailWord_4418166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418166).length < 2 ^ (prefixWord ++ tailWord_4418166).sum := by decide
  have hdescent : baseEnd_4418166 < baseStart_4418166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418172 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_4418172 : Nat := 118140960795 + 4418172 * 2 ^ 59
def prefixEnd_4418172 : Nat := 4983230072969 + 3 ^ 40 * 4418172 * 2
def baseEnd_4418172 : Nat := 2268645850236393115431203

theorem tailTrace_4418172 : CollatzResearch.WordTrace tailWord_4418172 prefixEnd_4418172 2268645850236393115431203 := by
  unfold tailWord_4418172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80571985674862441274412385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107429314233149921699216513 80571985674862441274412385)
  ·
    refine ⟨60428989256146830955809289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80571985674862441274412385 60428989256146830955809289)
    ·
      refine ⟨45321741942110123216856967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60428989256146830955809289 45321741942110123216856967)
      ·
        refine ⟨67982612913165184825285451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45321741942110123216856967 67982612913165184825285451)
        ·
          refine ⟨101973919369747777237928177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67982612913165184825285451 101973919369747777237928177)
          ·
            refine ⟨76480439527310832928446133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101973919369747777237928177 76480439527310832928446133)
            ·
              refine ⟨7170041205685390587041825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76480439527310832928446133 7170041205685390587041825)
              ·
                refine ⟨5377530904264042940281369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7170041205685390587041825 5377530904264042940281369)
                ·
                  refine ⟨4033148178198032205211027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5377530904264042940281369 4033148178198032205211027)
                  ·
                    refine ⟨6049722267297048307816541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4033148178198032205211027 6049722267297048307816541)
                    ·
                      refine ⟨2268645850236393115431203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6049722267297048307816541 2268645850236393115431203)
                      ·
                        rfl

theorem cell23_4418172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_4418172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418172 prefixEnd_4418172 := by exact prefixLift 4418172
  have htrace : WordTrace (prefixWord ++ tailWord_4418172) baseStart_4418172 baseEnd_4418172 := by
    simpa [prefixWord, tailWord_4418172, baseEnd_4418172] using wordTrace_append hprefix tailTrace_4418172
  have hstable : (prefixWord ++ tailWord_4418172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418172).length < 2 ^ (prefixWord ++ tailWord_4418172).sum := by decide
  have hdescent : baseEnd_4418172 < baseStart_4418172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418212 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_4418212 : Nat := 118140960795 + 4418212 * 2 ^ 59
def prefixEnd_4418212 : Nat := 4983230072969 + 3 ^ 40 * 4418212 * 2
def baseEnd_4418212 : Nat := 2268666389462572958931019

theorem tailTrace_4418212 : CollatzResearch.WordTrace tailWord_4418212 prefixEnd_4418212 2268666389462572958931019 := by
  unfold tailWord_4418212
  simp only [CollatzResearch.WordTrace]
  refine ⟨80572715134789984690140445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107430286846386646253520593 80572715134789984690140445)
  ·
    refine ⟨30214768175546244258802667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80572715134789984690140445 30214768175546244258802667)
    ·
      refine ⟨45322152263319366388204001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30214768175546244258802667 45322152263319366388204001)
      ·
        refine ⟨33991614197489524791153001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45322152263319366388204001 33991614197489524791153001)
        ·
          refine ⟨25493710648117143593364751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33991614197489524791153001 25493710648117143593364751)
          ·
            refine ⟨38240565972175715390047127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25493710648117143593364751 38240565972175715390047127)
            ·
              refine ⟨57360848958263573085070691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38240565972175715390047127 57360848958263573085070691)
              ·
                refine ⟨86041273437395359627606037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57360848958263573085070691 86041273437395359627606037)
                ·
                  refine ⟨4033184692377907482544033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86041273437395359627606037 4033184692377907482544033)
                  ·
                    refine ⟨3024888519283430611908025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033184692377907482544033 3024888519283430611908025)
                    ·
                      refine ⟨2268666389462572958931019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024888519283430611908025 2268666389462572958931019)
                      ·
                        rfl

theorem cell23_4418212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_4418212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418212 prefixEnd_4418212 := by exact prefixLift 4418212
  have htrace : WordTrace (prefixWord ++ tailWord_4418212) baseStart_4418212 baseEnd_4418212 := by
    simpa [prefixWord, tailWord_4418212, baseEnd_4418212] using wordTrace_append hprefix tailTrace_4418212
  have hstable : (prefixWord ++ tailWord_4418212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418212).length < 2 ^ (prefixWord ++ tailWord_4418212).sum := by decide
  have hdescent : baseEnd_4418212 < baseStart_4418212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418229 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4418229 : Nat := 118140960795 + 4418229 * 2 ^ 59
def prefixEnd_4418229 : Nat := 4983230072969 + 3 ^ 40 * 4418229 * 2
def baseEnd_4418229 : Nat := 2268675118633699392418441

theorem tailTrace_4418229 : CollatzResearch.WordTrace tailWord_4418229 prefixEnd_4418229 2268675118633699392418441 := by
  unfold tailWord_4418229
  simp only [CollatzResearch.WordTrace]
  refine ⟨161146050310518381283649741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107430700207012254189099827 161146050310518381283649741)
  ·
    refine ⟨60429768866444392981368653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161146050310518381283649741 60429768866444392981368653)
    ·
      refine ⟨22661163324916647368013245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60429768866444392981368653 22661163324916647368013245)
      ·
        refine ⟨8497936246843742763004967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22661163324916647368013245 8497936246843742763004967)
        ·
          refine ⟨12746904370265614144507451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8497936246843742763004967 12746904370265614144507451)
          ·
            refine ⟨19120356555398421216761177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12746904370265614144507451 19120356555398421216761177)
            ·
              refine ⟨14340267416548815912570883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19120356555398421216761177 14340267416548815912570883)
              ·
                refine ⟨21510401124823223868856325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14340267416548815912570883 21510401124823223868856325)
                ·
                  refine ⟨4033200210904354475410561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21510401124823223868856325 4033200210904354475410561)
                  ·
                    refine ⟨3024900158178265856557921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033200210904354475410561 3024900158178265856557921)
                    ·
                      refine ⟨2268675118633699392418441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024900158178265856557921 2268675118633699392418441)
                      ·
                        rfl

theorem cell23_4418229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4418229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418229 prefixEnd_4418229 := by exact prefixLift 4418229
  have htrace : WordTrace (prefixWord ++ tailWord_4418229) baseStart_4418229 baseEnd_4418229 := by
    simpa [prefixWord, tailWord_4418229, baseEnd_4418229] using wordTrace_append hprefix tailTrace_4418229
  have hstable : (prefixWord ++ tailWord_4418229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418229).length < 2 ^ (prefixWord ++ tailWord_4418229).sum := by decide
  have hdescent : baseEnd_4418229 < baseStart_4418229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418265 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_4418265 : Nat := 118140960795 + 4418265 * 2 ^ 59
def prefixEnd_4418265 : Nat := 4983230072969 + 3 ^ 40 * 4418265 * 2
def baseEnd_4418265 : Nat := 756231201312420417189425

theorem tailTrace_4418265 : CollatzResearch.WordTrace tailWord_4418265 prefixEnd_4418265 756231201312420417189425 := by
  unfold tailWord_4418265
  simp only [CollatzResearch.WordTrace]
  refine ⟨161147363338387959431960249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107431575558925306287973499 161147363338387959431960249)
  ·
    refine ⟨120860522503790969573970187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161147363338387959431960249 120860522503790969573970187)
    ·
      refine ⟨181290783755686454360955281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120860522503790969573970187 181290783755686454360955281)
      ·
        refine ⟨135968087816764840770716461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181290783755686454360955281 135968087816764840770716461)
        ·
          refine ⟨50988032931286815289018673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135968087816764840770716461 50988032931286815289018673)
          ·
            refine ⟨38241024698465111466764005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50988032931286815289018673 38241024698465111466764005)
            ·
              refine ⟨7170192130962208400018251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38241024698465111466764005 7170192130962208400018251)
              ·
                refine ⟨10755288196443312600027377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7170192130962208400018251 10755288196443312600027377)
                ·
                  refine ⟨8066466147332484450020533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10755288196443312600027377 8066466147332484450020533)
                  ·
                    refine ⟨756231201312420417189425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8066466147332484450020533 756231201312420417189425)
                    ·
                      rfl

theorem cell23_4418265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_4418265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418265 prefixEnd_4418265 := by exact prefixLift 4418265
  have htrace : WordTrace (prefixWord ++ tailWord_4418265) baseStart_4418265 baseEnd_4418265 := by
    simpa [prefixWord, tailWord_4418265, baseEnd_4418265] using wordTrace_append hprefix tailTrace_4418265
  have hstable : (prefixWord ++ tailWord_4418265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418265).length < 2 ^ (prefixWord ++ tailWord_4418265).sum := by decide
  have hdescent : baseEnd_4418265 < baseStart_4418265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418275 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4418275 : Nat := 118140960795 + 4418275 * 2 ^ 59
def prefixEnd_4418275 : Nat := 4983230072969 + 3 ^ 40 * 4418275 * 2
def baseEnd_4418275 : Nat := 2268698738743806212443229

theorem tailTrace_4418275 : CollatzResearch.WordTrace tailWord_4418275 prefixEnd_4418275 2268698738743806212443229 := by
  unfold tailWord_4418275
  simp only [CollatzResearch.WordTrace]
  refine ⟨161147728068351731139824279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107431818712234487426549519 161147728068351731139824279)
  ·
    refine ⟨241721592102527596709736419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161147728068351731139824279 241721592102527596709736419)
    ·
      refine ⟨362582388153791395064604629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241721592102527596709736419 362582388153791395064604629)
      ·
        refine ⟨8498024722354485821826671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 362582388153791395064604629 8498024722354485821826671)
        ·
          refine ⟨12747037083531728732740007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498024722354485821826671 12747037083531728732740007)
          ·
            refine ⟨19120555625297593099110011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12747037083531728732740007 19120555625297593099110011)
            ·
              refine ⟨28680833437946389648665017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19120555625297593099110011 28680833437946389648665017)
              ·
                refine ⟨21510625078459792236498763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28680833437946389648665017 21510625078459792236498763)
                ·
                  refine ⟨32265937617689688354748145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21510625078459792236498763 32265937617689688354748145)
                  ·
                    refine ⟨24199453213267266266061109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32265937617689688354748145 24199453213267266266061109)
                    ·
                      refine ⟨2268698738743806212443229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24199453213267266266061109 2268698738743806212443229)
                      ·
                        rfl

theorem cell23_4418275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4418275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418275 prefixEnd_4418275 := by exact prefixLift 4418275
  have htrace : WordTrace (prefixWord ++ tailWord_4418275) baseStart_4418275 baseEnd_4418275 := by
    simpa [prefixWord, tailWord_4418275, baseEnd_4418275] using wordTrace_append hprefix tailTrace_4418275
  have hstable : (prefixWord ++ tailWord_4418275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418275).length < 2 ^ (prefixWord ++ tailWord_4418275).sum := by decide
  have hdescent : baseEnd_4418275 < baseStart_4418275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418288 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_4418288 : Nat := 118140960795 + 4418288 * 2 ^ 59
def prefixEnd_4418288 : Nat := 4983230072969 + 3 ^ 40 * 4418288 * 2
def baseEnd_4418288 : Nat := 2268705413992314661580669

theorem tailTrace_4418288 : CollatzResearch.WordTrace tailWord_4418288 prefixEnd_4418288 2268705413992314661580669 := by
  unfold tailWord_4418288
  simp only [CollatzResearch.WordTrace]
  refine ⟨80574101108652317180023759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107432134811536422906698345 80574101108652317180023759)
  ·
    refine ⟨120861151662978475770035639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80574101108652317180023759 120861151662978475770035639)
    ·
      refine ⟨181291727494467713655053459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120861151662978475770035639 181291727494467713655053459)
      ·
        refine ⟨271937591241701570482580189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181291727494467713655053459 271937591241701570482580189)
        ·
          refine ⟨101976596715638088930967571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271937591241701570482580189 101976596715638088930967571)
          ·
            refine ⟨152964895073457133396451357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101976596715638088930967571 152964895073457133396451357)
            ·
              refine ⟨57361835652546425023669259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152964895073457133396451357 57361835652546425023669259)
              ·
                refine ⟨86042753478819637535503889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57361835652546425023669259 86042753478819637535503889)
                ·
                  refine ⟨64532065109114728151627917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86042753478819637535503889 64532065109114728151627917)
                  ·
                    refine ⟨24199524415918023056860469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64532065109114728151627917 24199524415918023056860469)
                    ·
                      refine ⟨2268705413992314661580669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24199524415918023056860469 2268705413992314661580669)
                      ·
                        rfl

theorem cell23_4418288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_4418288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418288 prefixEnd_4418288 := by exact prefixLift 4418288
  have htrace : WordTrace (prefixWord ++ tailWord_4418288) baseStart_4418288 baseEnd_4418288 := by
    simpa [prefixWord, tailWord_4418288, baseEnd_4418288] using wordTrace_append hprefix tailTrace_4418288
  have hstable : (prefixWord ++ tailWord_4418288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418288).length < 2 ^ (prefixWord ++ tailWord_4418288).sum := by decide
  have hdescent : baseEnd_4418288 < baseStart_4418288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418295 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 3, 4]
def baseStart_4418295 : Nat := 118140960795 + 4418295 * 2 ^ 59
def prefixEnd_4418295 : Nat := 4983230072969 + 3 ^ 40 * 4418295 * 2
def baseEnd_4418295 : Nat := 756236336118965378064379

theorem tailTrace_4418295 : CollatzResearch.WordTrace tailWord_4418295 prefixEnd_4418295 756236336118965378064379 := by
  unfold tailWord_4418295
  simp only [CollatzResearch.WordTrace]
  refine ⟨161148457528279274555552339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107432305018852849703701559 161148457528279274555552339)
  ·
    refine ⟨241722686292418911833328509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161148457528279274555552339 241722686292418911833328509)
    ·
      refine ⟨90646007359657091937498191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241722686292418911833328509 90646007359657091937498191)
      ·
        refine ⟨135969011039485637906247287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90646007359657091937498191 135969011039485637906247287)
        ·
          refine ⟨203953516559228456859370931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135969011039485637906247287 203953516559228456859370931)
          ·
            refine ⟨305930274838842685289056397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203953516559228456859370931 305930274838842685289056397)
            ·
              refine ⟨114723853064566006983396149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305930274838842685289056397 114723853064566006983396149)
              ·
                refine ⟨10755361224803063154693389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114723853064566006983396149 10755361224803063154693389)
                ·
                  refine ⟨4033260459301148683010021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10755361224803063154693389 4033260459301148683010021)
                  ·
                    refine ⟨756236336118965378064379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033260459301148683010021 756236336118965378064379)
                    ·
                      rfl

theorem cell23_4418295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_4418295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418295 prefixEnd_4418295 := by exact prefixLift 4418295
  have htrace : WordTrace (prefixWord ++ tailWord_4418295) baseStart_4418295 baseEnd_4418295 := by
    simpa [prefixWord, tailWord_4418295, baseEnd_4418295] using wordTrace_append hprefix tailTrace_4418295
  have hstable : (prefixWord ++ tailWord_4418295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418295).length < 2 ^ (prefixWord ++ tailWord_4418295).sum := by decide
  have hdescent : baseEnd_4418295 < baseStart_4418295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418305 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4418305 : Nat := 118140960795 + 4418305 * 2 ^ 59
def prefixEnd_4418305 : Nat := 4983230072969 + 3 ^ 40 * 4418305 * 2
def baseEnd_4418305 : Nat := 2268714143163441095068091

theorem tailTrace_4418305 : CollatzResearch.WordTrace tailWord_4418305 prefixEnd_4418305 2268714143163441095068091 := by
  unfold tailWord_4418305
  simp only [CollatzResearch.WordTrace]
  refine ⟨161148822258243046263416369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107432548172162030842277579 161148822258243046263416369)
  ·
    refine ⟨120861616693682284697562277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161148822258243046263416369 120861616693682284697562277)
    ·
      refine ⟨22661553130065428380792927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120861616693682284697562277 22661553130065428380792927)
      ·
        refine ⟨33992329695098142571189391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22661553130065428380792927 33992329695098142571189391)
        ·
          refine ⟨50988494542647213856784087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33992329695098142571189391 50988494542647213856784087)
          ·
            refine ⟨76482741813970820785176131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50988494542647213856784087 76482741813970820785176131)
            ·
              refine ⟨114724112720956231177764197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76482741813970820785176131 114724112720956231177764197)
              ·
                refine ⟨21510771135179293345830787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114724112720956231177764197 21510771135179293345830787)
                ·
                  refine ⟨32266156702768940018746181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21510771135179293345830787 32266156702768940018746181)
                  ·
                    refine ⟨6049904381769176253514909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32266156702768940018746181 6049904381769176253514909)
                    ·
                      refine ⟨2268714143163441095068091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6049904381769176253514909 2268714143163441095068091)
                      ·
                        rfl

theorem cell23_4418305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4418305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418305 prefixEnd_4418305 := by exact prefixLift 4418305
  have htrace : WordTrace (prefixWord ++ tailWord_4418305) baseStart_4418305 baseEnd_4418305 := by
    simpa [prefixWord, tailWord_4418305, baseEnd_4418305] using wordTrace_append hprefix tailTrace_4418305
  have hstable : (prefixWord ++ tailWord_4418305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418305).length < 2 ^ (prefixWord ++ tailWord_4418305).sum := by decide
  have hdescent : baseEnd_4418305 < baseStart_4418305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418312 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_4418312 : Nat := 118140960795 + 4418312 * 2 ^ 59
def prefixEnd_4418312 : Nat := 4983230072969 + 3 ^ 40 * 4418312 * 2
def baseEnd_4418312 : Nat := 756239245842674189226853

theorem tailTrace_4418312 : CollatzResearch.WordTrace tailWord_4418312 prefixEnd_4418312 756239245842674189226853 := by
  unfold tailWord_4418312
  simp only [CollatzResearch.WordTrace]
  refine ⟨80574538784608843229460595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107432718379478457639280793 80574538784608843229460595)
  ·
    refine ⟨120861808176913264844190893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80574538784608843229460595 120861808176913264844190893)
    ·
      refine ⟨45323178066342474316571585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120861808176913264844190893 45323178066342474316571585)
      ·
        refine ⟨33992383549756855737428689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45323178066342474316571585 33992383549756855737428689)
        ·
          refine ⟨25494287662317641803071517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33992383549756855737428689 25494287662317641803071517)
          ·
            refine ⟨9560357873369115676151819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25494287662317641803071517 9560357873369115676151819)
            ·
              refine ⟨14340536810053673514227729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9560357873369115676151819 14340536810053673514227729)
              ·
                refine ⟨10755402607540255135670797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14340536810053673514227729 10755402607540255135670797)
                ·
                  refine ⟨4033275977827595675876549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10755402607540255135670797 4033275977827595675876549)
                  ·
                    refine ⟨756239245842674189226853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033275977827595675876549 756239245842674189226853)
                    ·
                      rfl

theorem cell23_4418312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_4418312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418312 prefixEnd_4418312 := by exact prefixLift 4418312
  have htrace : WordTrace (prefixWord ++ tailWord_4418312) baseStart_4418312 baseEnd_4418312 := by
    simpa [prefixWord, tailWord_4418312, baseEnd_4418312] using wordTrace_append hprefix tailTrace_4418312
  have hstable : (prefixWord ++ tailWord_4418312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418312).length < 2 ^ (prefixWord ++ tailWord_4418312).sum := by decide
  have hdescent : baseEnd_4418312 < baseStart_4418312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418346 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_4418346 : Nat := 118140960795 + 4418346 * 2 ^ 59
def prefixEnd_4418346 : Nat := 4983230072969 + 3 ^ 40 * 4418346 * 2
def baseEnd_4418346 : Nat := 756245065290091811551801

theorem tailTrace_4418346 : CollatzResearch.WordTrace tailWord_4418346 prefixEnd_4418346 756245065290091811551801 := by
  unfold tailWord_4418346
  simp only [CollatzResearch.WordTrace]
  refine ⟨40287579412773627566414723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107433545100729673510439261 40287579412773627566414723)
  ·
    refine ⟨60431369119160441349622085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40287579412773627566414723 60431369119160441349622085)
    ·
      refine ⟨11330881709842582753054141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60431369119160441349622085 11330881709842582753054141)
      ·
        refine ⟨4249080641190968532395303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11330881709842582753054141 4249080641190968532395303)
        ·
          refine ⟨6373620961786452798592955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249080641190968532395303 6373620961786452798592955)
          ·
            refine ⟨9560431442679679197889433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6373620961786452798592955 9560431442679679197889433)
            ·
              refine ⟨7170323582009759398417075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9560431442679679197889433 7170323582009759398417075)
              ·
                refine ⟨10755485373014639097625613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7170323582009759398417075 10755485373014639097625613)
                ·
                  refine ⟨4033307014880489661609605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10755485373014639097625613 4033307014880489661609605)
                  ·
                    refine ⟨756245065290091811551801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033307014880489661609605 756245065290091811551801)
                    ·
                      rfl

theorem cell23_4418346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_4418346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418346 prefixEnd_4418346 := by exact prefixLift 4418346
  have htrace : WordTrace (prefixWord ++ tailWord_4418346) baseStart_4418346 baseEnd_4418346 := by
    simpa [prefixWord, tailWord_4418346, baseEnd_4418346] using wordTrace_append hprefix tailTrace_4418346
  have hstable : (prefixWord ++ tailWord_4418346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418346).length < 2 ^ (prefixWord ++ tailWord_4418346).sum := by decide
  have hdescent : baseEnd_4418346 < baseStart_4418346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418396 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4418396 : Nat := 118140960795 + 4418396 * 2 ^ 59
def prefixEnd_4418396 : Nat := 4983230072969 + 3 ^ 40 * 4418396 * 2
def baseEnd_4418396 : Nat := 2268760869903000239030173

theorem tailTrace_4418396 : CollatzResearch.WordTrace tailWord_4418396 prefixEnd_4418396 2268760869903000239030173 := by
  unfold tailWord_4418396
  simp only [CollatzResearch.WordTrace]
  refine ⟨80576070650456684402489521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107434760867275579203319361 80576070650456684402489521)
  ·
    refine ⟨60432052987842513301867141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80576070650456684402489521 60432052987842513301867141)
    ·
      refine ⟨11331009935220471244100089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60432052987842513301867141 11331009935220471244100089)
      ·
        refine ⟨8498257451415353433075067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11331009935220471244100089 8498257451415353433075067)
        ·
          refine ⟨12747386177123030149612601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498257451415353433075067 12747386177123030149612601)
          ·
            refine ⟨9560539632842272612209451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12747386177123030149612601 9560539632842272612209451)
            ·
              refine ⟨14340809449263408918314177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9560539632842272612209451 14340809449263408918314177)
              ·
                refine ⟨10755607086947556688735633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14340809449263408918314177 10755607086947556688735633)
                ·
                  refine ⟨8066705315210667516551725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10755607086947556688735633 8066705315210667516551725)
                  ·
                    refine ⟨3025014493204000318706897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8066705315210667516551725 3025014493204000318706897)
                    ·
                      refine ⟨2268760869903000239030173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025014493204000318706897 2268760869903000239030173)
                      ·
                        rfl

theorem cell23_4418396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4418396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418396 prefixEnd_4418396 := by exact prefixLift 4418396
  have htrace : WordTrace (prefixWord ++ tailWord_4418396) baseStart_4418396 baseEnd_4418396 := by
    simpa [prefixWord, tailWord_4418396, baseEnd_4418396] using wordTrace_append hprefix tailTrace_4418396
  have hstable : (prefixWord ++ tailWord_4418396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418396).length < 2 ^ (prefixWord ++ tailWord_4418396).sum := by decide
  have hdescent : baseEnd_4418396 < baseStart_4418396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418403 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 1, 1, 3]
def baseStart_4418403 : Nat := 118140960795 + 4418403 * 2 ^ 59
def prefixEnd_4418403 : Nat := 4983230072969 + 3 ^ 40 * 4418403 * 2
def baseEnd_4418403 : Nat := 2268764464267581711642641

theorem tailTrace_4418403 : CollatzResearch.WordTrace tailWord_4418403 prefixEnd_4418403 2268764464267581711642641 := by
  unfold tailWord_4418403
  simp only [CollatzResearch.WordTrace]
  refine ⟨161152396611888009000483863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107434931074592006000322575 161152396611888009000483863)
  ·
    refine ⟨241728594917832013500725795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161152396611888009000483863 241728594917832013500725795)
    ·
      refine ⟨362592892376748020251088693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241728594917832013500725795 362592892376748020251088693)
      ·
        refine ⟨33993083660320126898539565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 362592892376748020251088693 33993083660320126898539565)
        ·
          refine ⟨12747406372620047586952337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33993083660320126898539565 12747406372620047586952337)
          ·
            refine ⟨9560554779465035690214253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12747406372620047586952337 9560554779465035690214253)
            ·
              refine ⟨3585208042299388383830345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9560554779465035690214253 3585208042299388383830345)
              ·
                refine ⟨2688906031724541287872759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3585208042299388383830345 2688906031724541287872759)
                ·
                  refine ⟨4033359047586811931809139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688906031724541287872759 4033359047586811931809139)
                  ·
                    refine ⟨6050038571380217897713709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4033359047586811931809139 6050038571380217897713709)
                    ·
                      refine ⟨2268764464267581711642641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050038571380217897713709 2268764464267581711642641)
                      ·
                        rfl

theorem cell23_4418403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_4418403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418403 prefixEnd_4418403 := by exact prefixLift 4418403
  have htrace : WordTrace (prefixWord ++ tailWord_4418403) baseStart_4418403 baseEnd_4418403 := by
    simpa [prefixWord, tailWord_4418403, baseEnd_4418403] using wordTrace_append hprefix tailTrace_4418403
  have hstable : (prefixWord ++ tailWord_4418403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418403).length < 2 ^ (prefixWord ++ tailWord_4418403).sum := by decide
  have hdescent : baseEnd_4418403 < baseStart_4418403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418405 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4418405 : Nat := 118140960795 + 4418405 * 2 ^ 59
def prefixEnd_4418405 : Nat := 4983230072969 + 3 ^ 40 * 4418405 * 2
def baseEnd_4418405 : Nat := 2268765491228890703817631

theorem tailTrace_4418405 : CollatzResearch.WordTrace tailWord_4418405 prefixEnd_4418405 2268765491228890703817631 := by
  unfold tailWord_4418405
  simp only [CollatzResearch.WordTrace]
  refine ⟨161152469557880763342056669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107434979705253842228037779 161152469557880763342056669)
  ·
    refine ⟨60432176084205286253271251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161152469557880763342056669 60432176084205286253271251)
    ·
      refine ⟨90648264126307929379906877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60432176084205286253271251 90648264126307929379906877)
      ·
        refine ⟨33993099047365473517465079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90648264126307929379906877 33993099047365473517465079)
        ·
          refine ⟨50989648571048210276197619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33993099047365473517465079 50989648571048210276197619)
          ·
            refine ⟨76484472856572315414296429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50989648571048210276197619 76484472856572315414296429)
            ·
              refine ⟨28681677321214618280361161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76484472856572315414296429 28681677321214618280361161)
              ·
                refine ⟨21511257990910963710270871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28681677321214618280361161 21511257990910963710270871)
                ·
                  refine ⟨32266886986366445565406307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21511257990910963710270871 32266886986366445565406307)
                  ·
                    refine ⟨48400330479549668348109461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32266886986366445565406307 48400330479549668348109461)
                    ·
                      refine ⟨2268765491228890703817631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48400330479549668348109461 2268765491228890703817631)
                      ·
                        rfl

theorem cell23_4418405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4418405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418405 prefixEnd_4418405 := by exact prefixLift 4418405
  have htrace : WordTrace (prefixWord ++ tailWord_4418405) baseStart_4418405 baseEnd_4418405 := by
    simpa [prefixWord, tailWord_4418405, baseEnd_4418405] using wordTrace_append hprefix tailTrace_4418405
  have hstable : (prefixWord ++ tailWord_4418405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418405).length < 2 ^ (prefixWord ++ tailWord_4418405).sum := by decide
  have hdescent : baseEnd_4418405 < baseStart_4418405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418412 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_4418412 : Nat := 118140960795 + 4418412 * 2 ^ 59
def prefixEnd_4418412 : Nat := 4983230072969 + 3 ^ 40 * 4418412 * 2
def baseEnd_4418412 : Nat := 2268769085593472176430099

theorem tailTrace_4418412 : CollatzResearch.WordTrace tailWord_4418412 prefixEnd_4418412 2268769085593472176430099 := by
  unfold tailWord_4418412
  simp only [CollatzResearch.WordTrace]
  refine ⟨80576362434427701768780745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107435149912570269025040993 80576362434427701768780745)
  ·
    refine ⟨60432271825820776326585559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80576362434427701768780745 60432271825820776326585559)
    ·
      refine ⟨90648407738731164489878339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60432271825820776326585559 90648407738731164489878339)
      ·
        refine ⟨135972611608096746734817509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90648407738731164489878339 135972611608096746734817509)
        ·
          refine ⟨25494864676518140012778283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135972611608096746734817509 25494864676518140012778283)
          ·
            refine ⟨38242297014777210019167425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25494864676518140012778283 38242297014777210019167425)
            ·
              refine ⟨28681722761082907514375569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38242297014777210019167425 28681722761082907514375569)
              ·
                refine ⟨21511292070812180635781677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28681722761082907514375569 21511292070812180635781677)
                ·
                  refine ⟨8066734526554567738418129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21511292070812180635781677 8066734526554567738418129)
                  ·
                    refine ⟨6050050894915925803813597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8066734526554567738418129 6050050894915925803813597)
                    ·
                      refine ⟨2268769085593472176430099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050050894915925803813597 2268769085593472176430099)
                      ·
                        rfl

theorem cell23_4418412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_4418412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418412 prefixEnd_4418412 := by exact prefixLift 4418412
  have htrace : WordTrace (prefixWord ++ tailWord_4418412) baseStart_4418412 baseEnd_4418412 := by
    simpa [prefixWord, tailWord_4418412, baseEnd_4418412] using wordTrace_append hprefix tailTrace_4418412
  have hstable : (prefixWord ++ tailWord_4418412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418412).length < 2 ^ (prefixWord ++ tailWord_4418412).sum := by decide
  have hdescent : baseEnd_4418412 < baseStart_4418412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418419 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 2, 4]
def baseStart_4418419 : Nat := 118140960795 + 4418419 * 2 ^ 59
def prefixEnd_4418419 : Nat := 4983230072969 + 3 ^ 40 * 4418419 * 2
def baseEnd_4418419 : Nat := 756257559986017883014189

theorem tailTrace_4418419 : CollatzResearch.WordTrace tailWord_4418419 prefixEnd_4418419 756257559986017883014189 := by
  unfold tailWord_4418419
  simp only [CollatzResearch.WordTrace]
  refine ⟨161152980179830043733066311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107435320119886695822044207 161152980179830043733066311)
  ·
    refine ⟨241729470269745065599599467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161152980179830043733066311 241729470269745065599599467)
    ·
      refine ⟨362594205404617598399399201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241729470269745065599599467 362594205404617598399399201)
      ·
        refine ⟨271945654053463198799549401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362594205404617598399399201 271945654053463198799549401)
        ·
          refine ⟨203959240540097399099662051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271945654053463198799549401 203959240540097399099662051)
          ·
            refine ⟨305938860810146098649493077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203959240540097399099662051 305938860810146098649493077)
            ·
              refine ⟨3585221025118899593548747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 305938860810146098649493077 3585221025118899593548747)
              ·
                refine ⟨5377831537678349390323121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3585221025118899593548747 5377831537678349390323121)
                ·
                  refine ⟨4033373653258762042742341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5377831537678349390323121 4033373653258762042742341)
                  ·
                    refine ⟨756257559986017883014189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033373653258762042742341 756257559986017883014189)
                    ·
                      rfl

theorem cell23_4418419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 4].length) (baseStart_4418419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418419 prefixEnd_4418419 := by exact prefixLift 4418419
  have htrace : WordTrace (prefixWord ++ tailWord_4418419) baseStart_4418419 baseEnd_4418419 := by
    simpa [prefixWord, tailWord_4418419, baseEnd_4418419] using wordTrace_append hprefix tailTrace_4418419
  have hstable : (prefixWord ++ tailWord_4418419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418419).length < 2 ^ (prefixWord ++ tailWord_4418419).sum := by decide
  have hdescent : baseEnd_4418419 < baseStart_4418419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418429 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_4418429 : Nat := 118140960795 + 4418429 * 2 ^ 59
def prefixEnd_4418429 : Nat := 4983230072969 + 3 ^ 40 * 4418429 * 2
def baseEnd_4418429 : Nat := 2268777814764598609917521

theorem tailTrace_4418429 : CollatzResearch.WordTrace tailWord_4418429 prefixEnd_4418429 2268777814764598609917521 := by
  unfold tailWord_4418429
  simp only [CollatzResearch.WordTrace]
  refine ⟨161153344909793815440930341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107435563273195876960620227 161153344909793815440930341)
  ·
    refine ⟨30216252170586340395174439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161153344909793815440930341 30216252170586340395174439)
    ·
      refine ⟨45324378255879510592761659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30216252170586340395174439 45324378255879510592761659)
      ·
        refine ⟨67986567383819265889142489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45324378255879510592761659 67986567383819265889142489)
        ·
          refine ⟨50989925537864449416856867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67986567383819265889142489 50989925537864449416856867)
          ·
            refine ⟨76484888306796674125285301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50989925537864449416856867 76484888306796674125285301)
            ·
              refine ⟨7170458278762188199245497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76484888306796674125285301 7170458278762188199245497)
              ·
                refine ⟨5377843709071641149434123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7170458278762188199245497 5377843709071641149434123)
                ·
                  refine ⟨8066765563607461724151185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5377843709071641149434123 8066765563607461724151185)
                  ·
                    refine ⟨6050074172705596293113389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8066765563607461724151185 6050074172705596293113389)
                    ·
                      refine ⟨2268777814764598609917521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050074172705596293113389 2268777814764598609917521)
                      ·
                        rfl

theorem cell23_4418429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_4418429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418429 prefixEnd_4418429 := by exact prefixLift 4418429
  have htrace : WordTrace (prefixWord ++ tailWord_4418429) baseStart_4418429 baseEnd_4418429 := by
    simpa [prefixWord, tailWord_4418429, baseEnd_4418429] using wordTrace_append hprefix tailTrace_4418429
  have hstable : (prefixWord ++ tailWord_4418429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418429).length < 2 ^ (prefixWord ++ tailWord_4418429).sum := by decide
  have hdescent : baseEnd_4418429 < baseStart_4418429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418454 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4418454 : Nat := 118140960795 + 4418454 * 2 ^ 59
def prefixEnd_4418454 : Nat := 4983230072969 + 3 ^ 40 * 4418454 * 2
def baseEnd_4418454 : Nat := 2268790651780961012104907

theorem tailTrace_4418454 : CollatzResearch.WordTrace tailWord_4418454 prefixEnd_4418454 2268790651780961012104907 := by
  unfold tailWord_4418454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10072141045918952794411901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107436171156468829807060277 10072141045918952794411901)
  ·
    refine ⟨3777052892219607297904463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10072141045918952794411901 3777052892219607297904463)
    ·
      refine ⟨5665579338329410946856695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777052892219607297904463 5665579338329410946856695)
      ·
        refine ⟨8498369007494116420285043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665579338329410946856695 8498369007494116420285043)
        ·
          refine ⟨12747553511241174630427565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498369007494116420285043 12747553511241174630427565)
          ·
            refine ⟨4780332566715440486410337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12747553511241174630427565 4780332566715440486410337)
            ·
              refine ⟨3585249425036580364807753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4780332566715440486410337 3585249425036580364807753)
              ·
                refine ⟨2688937068777435273605815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3585249425036580364807753 2688937068777435273605815)
                ·
                  refine ⟨4033405603166152910408723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688937068777435273605815 4033405603166152910408723)
                  ·
                    refine ⟨6050108404749229365613085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4033405603166152910408723 6050108404749229365613085)
                    ·
                      refine ⟨2268790651780961012104907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050108404749229365613085 2268790651780961012104907)
                      ·
                        rfl

theorem cell23_4418454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4418454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418454 prefixEnd_4418454 := by exact prefixLift 4418454
  have htrace : WordTrace (prefixWord ++ tailWord_4418454) baseStart_4418454 baseEnd_4418454 := by
    simpa [prefixWord, tailWord_4418454, baseEnd_4418454] using wordTrace_append hprefix tailTrace_4418454
  have hstable : (prefixWord ++ tailWord_4418454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418454).length < 2 ^ (prefixWord ++ tailWord_4418454).sum := by decide
  have hdescent : baseEnd_4418454 < baseStart_4418454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418460 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4418460 : Nat := 118140960795 + 4418460 * 2 ^ 59
def prefixEnd_4418460 : Nat := 4983230072969 + 3 ^ 40 * 4418460 * 2
def baseEnd_4418460 : Nat := 2268793732664887988629879

theorem tailTrace_4418460 : CollatzResearch.WordTrace tailWord_4418460 prefixEnd_4418460 2268793732664887988629879 := by
  unfold tailWord_4418460
  simp only [CollatzResearch.WordTrace]
  refine ⟨80577237786340753867654417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107436317048454338490205889 80577237786340753867654417)
  ·
    refine ⟨60432928339755565400740813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80577237786340753867654417 60432928339755565400740813)
    ·
      refine ⟨22662348127408337025277805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60432928339755565400740813 22662348127408337025277805)
      ·
        refine ⟨8498380547778126384479177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22662348127408337025277805 8498380547778126384479177)
        ·
          refine ⟨6373785410833594788359383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8498380547778126384479177 6373785410833594788359383)
          ·
            refine ⟨9560678116250392182539075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6373785410833594788359383 9560678116250392182539075)
            ·
              refine ⟨14341017174375588273808613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9560678116250392182539075 14341017174375588273808613)
              ·
                refine ⟨2688940720195422801339115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14341017174375588273808613 2688940720195422801339115)
                ·
                  refine ⟨4033411080293134202008673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688940720195422801339115 4033411080293134202008673)
                  ·
                    refine ⟨3025058310219850651506505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033411080293134202008673 3025058310219850651506505)
                    ·
                      refine ⟨2268793732664887988629879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025058310219850651506505 2268793732664887988629879)
                      ·
                        rfl

theorem cell23_4418460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4418460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418460 prefixEnd_4418460 := by exact prefixLift 4418460
  have htrace : WordTrace (prefixWord ++ tailWord_4418460) baseStart_4418460 baseEnd_4418460 := by
    simpa [prefixWord, tailWord_4418460, baseEnd_4418460] using wordTrace_append hprefix tailTrace_4418460
  have hstable : (prefixWord ++ tailWord_4418460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418460).length < 2 ^ (prefixWord ++ tailWord_4418460).sum := by decide
  have hdescent : baseEnd_4418460 < baseStart_4418460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418475 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 2, 6]
def baseStart_4418475 : Nat := 118140960795 + 4418475 * 2 ^ 59
def prefixEnd_4418475 : Nat := 4983230072969 + 3 ^ 40 * 4418475 * 2
def baseEnd_4418475 : Nat := 756267144958235143314103

theorem tailTrace_4418475 : CollatzResearch.WordTrace tailWord_4418475 prefixEnd_4418475 756267144958235143314103 := by
  unfold tailWord_4418475
  simp only [CollatzResearch.WordTrace]
  refine ⟨161155022667627165297104879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107436681778418110198069919 161155022667627165297104879)
  ·
    refine ⟨241732534001440747945657319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161155022667627165297104879 241732534001440747945657319)
    ·
      refine ⟨362598801002161121918485979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241732534001440747945657319 362598801002161121918485979)
      ·
        refine ⟨543898201503241682877728969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362598801002161121918485979 543898201503241682877728969)
        ·
          refine ⟨407923651127431262158296727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543898201503241682877728969 407923651127431262158296727)
          ·
            refine ⟨611885476691146893237445091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407923651127431262158296727 611885476691146893237445091)
            ·
              refine ⟨917828215036720339856167637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611885476691146893237445091 917828215036720339856167637)
              ·
                refine ⟨21511598789923132965378929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 917828215036720339856167637 21511598789923132965378929)
                ·
                  refine ⟨16133699092442349724034197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21511598789923132965378929 16133699092442349724034197)
                  ·
                    refine ⟨756267144958235143314103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16133699092442349724034197 756267144958235143314103)
                    ·
                      rfl

theorem cell23_4418475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_4418475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418475 prefixEnd_4418475 := by exact prefixLift 4418475
  have htrace : WordTrace (prefixWord ++ tailWord_4418475) baseStart_4418475 baseEnd_4418475 := by
    simpa [prefixWord, tailWord_4418475, baseEnd_4418475] using wordTrace_append hprefix tailTrace_4418475
  have hstable : (prefixWord ++ tailWord_4418475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418475).length < 2 ^ (prefixWord ++ tailWord_4418475).sum := by decide
  have hdescent : baseEnd_4418475 < baseStart_4418475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418499 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 6, 2, 2]
def baseStart_4418499 : Nat := 118140960795 + 4418499 * 2 ^ 59
def prefixEnd_4418499 : Nat := 4983230072969 + 3 ^ 40 * 4418499 * 2
def baseEnd_4418499 : Nat := 2268813758410413336042199

theorem tailTrace_4418499 : CollatzResearch.WordTrace tailWord_4418499 prefixEnd_4418499 2268813758410413336042199 := by
  unfold tailWord_4418499
  simp only [CollatzResearch.WordTrace]
  refine ⟨161155898019540217395978551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107437265346360144930652367 161155898019540217395978551)
  ·
    refine ⟨241733847029310326093967827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161155898019540217395978551 241733847029310326093967827)
    ·
      refine ⟨362600770543965489140951741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241733847029310326093967827 362600770543965489140951741)
      ·
        refine ⟨135975288953987058427856903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362600770543965489140951741 135975288953987058427856903)
        ·
          refine ⟨203962933430980587641785355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135975288953987058427856903 203962933430980587641785355)
          ·
            refine ⟨305944400146470881462678033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203962933430980587641785355 305944400146470881462678033)
            ·
              refine ⟨229458300109853161097008525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305944400146470881462678033 229458300109853161097008525)
              ·
                refine ⟨86046862541194935411378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229458300109853161097008525 86046862541194935411378197)
                ·
                  refine ⟨4033446681618512597408353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86046862541194935411378197 4033446681618512597408353)
                  ·
                    refine ⟨3025085011213884448056265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033446681618512597408353 3025085011213884448056265)
                    ·
                      refine ⟨2268813758410413336042199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025085011213884448056265 2268813758410413336042199)
                      ·
                        rfl

theorem cell23_4418499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_4418499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418499 prefixEnd_4418499 := by exact prefixLift 4418499
  have htrace : WordTrace (prefixWord ++ tailWord_4418499) baseStart_4418499 baseEnd_4418499 := by
    simpa [prefixWord, tailWord_4418499, baseEnd_4418499] using wordTrace_append hprefix tailTrace_4418499
  have hstable : (prefixWord ++ tailWord_4418499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418499).length < 2 ^ (prefixWord ++ tailWord_4418499).sum := by decide
  have hdescent : baseEnd_4418499 < baseStart_4418499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418522 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_4418522 : Nat := 118140960795 + 4418522 * 2 ^ 59
def prefixEnd_4418522 : Nat := 4983230072969 + 3 ^ 40 * 4418522 * 2
def baseEnd_4418522 : Nat := 252091729829496305117177

theorem tailTrace_4418522 : CollatzResearch.WordTrace tailWord_4418522 prefixEnd_4418522 252091729829496305117177 := by
  unfold tailWord_4418522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40289184224614223081016455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107437824598971261549377213 40289184224614223081016455)
  ·
    refine ⟨60433776336921334621524683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40289184224614223081016455 60433776336921334621524683)
    ·
      refine ⟨90650664505382001932287025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60433776336921334621524683 90650664505382001932287025)
      ·
        refine ⟨67987998379036501449215269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90650664505382001932287025 67987998379036501449215269)
        ·
          refine ⟨12747749696069344021727863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67987998379036501449215269 12747749696069344021727863)
          ·
            refine ⟨19121624544104016032591795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12747749696069344021727863 19121624544104016032591795)
            ·
              refine ⟨28682436816156024048887693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19121624544104016032591795 28682436816156024048887693)
              ·
                refine ⟨10755913806058509018332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28682436816156024048887693 10755913806058509018332885)
                ·
                  refine ⟨252091729829496305117177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10755913806058509018332885 252091729829496305117177)
                  ·
                    rfl

theorem cell23_4418522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_4418522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418522 prefixEnd_4418522 := by exact prefixLift 4418522
  have htrace : WordTrace (prefixWord ++ tailWord_4418522) baseStart_4418522 baseEnd_4418522 := by
    simpa [prefixWord, tailWord_4418522, baseEnd_4418522] using wordTrace_append hprefix tailTrace_4418522
  have hstable : (prefixWord ++ tailWord_4418522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418522).length < 2 ^ (prefixWord ++ tailWord_4418522).sum := by decide
  have hdescent : baseEnd_4418522 < baseStart_4418522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418532 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_4418532 : Nat := 118140960795 + 4418532 * 2 ^ 59
def prefixEnd_4418532 : Nat := 4983230072969 + 3 ^ 40 * 4418532 * 2
def baseEnd_4418532 : Nat := 2268830703272011706929547

theorem tailTrace_4418532 : CollatzResearch.WordTrace tailWord_4418532 prefixEnd_4418532 2268830703272011706929547 := by
  unfold tailWord_4418532
  simp only [CollatzResearch.WordTrace]
  refine ⟨80578550814210332015964925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107438067752280442687953233 80578550814210332015964925)
  ·
    refine ⟨30216956555328874505986847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80578550814210332015964925 30216956555328874505986847)
    ·
      refine ⟨45325434832993311758980271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30216956555328874505986847 45325434832993311758980271)
      ·
        refine ⟨67988152249489967638470407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45325434832993311758980271 67988152249489967638470407)
        ·
          refine ⟨101982228374234951457705611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67988152249489967638470407 101982228374234951457705611)
          ·
            refine ⟨152973342561352427186558417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101982228374234951457705611 152973342561352427186558417)
            ·
              refine ⟨114730006921014320389918813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152973342561352427186558417 114730006921014320389918813)
              ·
                refine ⟨43023752595380370146219555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114730006921014320389918813 43023752595380370146219555)
                ·
                  refine ⟨64535628893070555219329333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43023752595380370146219555 64535628893070555219329333)
                  ·
                    refine ⟨6050215208725364551812125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64535628893070555219329333 6050215208725364551812125)
                    ·
                      refine ⟨2268830703272011706929547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050215208725364551812125 2268830703272011706929547)
                      ·
                        rfl

theorem cell23_4418532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_4418532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418532 prefixEnd_4418532 := by exact prefixLift 4418532
  have htrace : WordTrace (prefixWord ++ tailWord_4418532) baseStart_4418532 baseEnd_4418532 := by
    simpa [prefixWord, tailWord_4418532, baseEnd_4418532] using wordTrace_append hprefix tailTrace_4418532
  have hstable : (prefixWord ++ tailWord_4418532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418532).length < 2 ^ (prefixWord ++ tailWord_4418532).sum := by decide
  have hdescent : baseEnd_4418532 < baseStart_4418532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418552 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_4418552 : Nat := 118140960795 + 4418552 * 2 ^ 59
def prefixEnd_4418552 : Nat := 4983230072969 + 3 ^ 40 * 4418552 * 2
def baseEnd_4418552 : Nat := 756280324295033876226485

theorem tailTrace_4418552 : CollatzResearch.WordTrace tailWord_4418552 prefixEnd_4418552 756280324295033876226485 := by
  unfold tailWord_4418552
  simp only [CollatzResearch.WordTrace]
  refine ⟨80578915544174103723828955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107438554058898804965105273 80578915544174103723828955)
  ·
    refine ⟨120868373316261155585743433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80578915544174103723828955 120868373316261155585743433)
    ·
      refine ⟨90651279987195866689307575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120868373316261155585743433 90651279987195866689307575)
      ·
        refine ⟨135976919980793800033961363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90651279987195866689307575 135976919980793800033961363)
        ·
          refine ⟨203965379971190700050942045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135976919980793800033961363 203965379971190700050942045)
          ·
            refine ⟨76487017489196512519103267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203965379971190700050942045 76487017489196512519103267)
            ·
              refine ⟨114730526233794768778654901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76487017489196512519103267 114730526233794768778654901)
              ·
                refine ⟨10755986834418259572998897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114730526233794768778654901 10755986834418259572998897)
                ·
                  refine ⟨8066990125813694679749173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10755986834418259572998897 8066990125813694679749173)
                  ·
                    refine ⟨756280324295033876226485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8066990125813694679749173 756280324295033876226485)
                    ·
                      rfl

theorem cell23_4418552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_4418552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418552 prefixEnd_4418552 := by exact prefixLift 4418552
  have htrace : WordTrace (prefixWord ++ tailWord_4418552) baseStart_4418552 baseEnd_4418552 := by
    simpa [prefixWord, tailWord_4418552, baseEnd_4418552] using wordTrace_append hprefix tailTrace_4418552
  have hstable : (prefixWord ++ tailWord_4418552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418552).length < 2 ^ (prefixWord ++ tailWord_4418552).sum := by decide
  have hdescent : baseEnd_4418552 < baseStart_4418552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418556 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 5]
def baseStart_4418556 : Nat := 118140960795 + 4418556 * 2 ^ 59
def prefixEnd_4418556 : Nat := 4983230072969 + 3 ^ 40 * 4418556 * 2
def baseEnd_4418556 : Nat := 252093669645302179225493

theorem tailTrace_4418556 : CollatzResearch.WordTrace tailWord_4418556 prefixEnd_4418556 252093669645302179225493 := by
  unfold tailWord_4418556
  simp only [CollatzResearch.WordTrace]
  refine ⟨80578988490166858065401761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107438651320222477420535681 80578988490166858065401761)
  ·
    refine ⟨60434241367625143549051321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80578988490166858065401761 60434241367625143549051321)
    ·
      refine ⟨45325681025718857661788491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60434241367625143549051321 45325681025718857661788491)
      ·
        refine ⟨67988521538578286492682737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45325681025718857661788491 67988521538578286492682737)
        ·
          refine ⟨50991391153933714869512053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67988521538578286492682737 50991391153933714869512053)
          ·
            refine ⟨4780442920681285769016755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50991391153933714869512053 4780442920681285769016755)
            ·
              refine ⟨7170664381021928653525133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780442920681285769016755 7170664381021928653525133)
              ·
                refine ⟨2688999142883223245071925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7170664381021928653525133 2688999142883223245071925)
                ·
                  refine ⟨252093669645302179225493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688999142883223245071925 252093669645302179225493)
                  ·
                    rfl

theorem cell23_4418556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_4418556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418556 prefixEnd_4418556 := by exact prefixLift 4418556
  have htrace : WordTrace (prefixWord ++ tailWord_4418556) baseStart_4418556 baseEnd_4418556 := by
    simpa [prefixWord, tailWord_4418556, baseEnd_4418556] using wordTrace_append hprefix tailTrace_4418556
  have hstable : (prefixWord ++ tailWord_4418556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418556).length < 2 ^ (prefixWord ++ tailWord_4418556).sum := by decide
  have hdescent : baseEnd_4418556 < baseStart_4418556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418606 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4418606 : Nat := 118140960795 + 4418606 * 2 ^ 59
def prefixEnd_4418606 : Nat := 4983230072969 + 3 ^ 40 * 4418606 * 2
def baseEnd_4418606 : Nat := 2268868700840444417404207

theorem tailTrace_4418606 : CollatzResearch.WordTrace tailWord_4418606 prefixEnd_4418606 2268868700840444417404207 := by
  unfold tailWord_4418606
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144975078769071833765459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107439867086768383113415781 20144975078769071833765459)
  ·
    refine ⟨30217462618153607750648189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20144975078769071833765459 30217462618153607750648189)
    ·
      refine ⟨11331548481807602906493071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30217462618153607750648189 11331548481807602906493071)
      ·
        refine ⟨16997322722711404359739607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331548481807602906493071 16997322722711404359739607)
        ·
          refine ⟨25495984084067106539609411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16997322722711404359739607 25495984084067106539609411)
          ·
            refine ⟨38243976126100659809414117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25495984084067106539609411 38243976126100659809414117)
            ·
              refine ⟨7170745523643873714265147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38243976126100659809414117 7170745523643873714265147)
              ·
                refine ⟨10756118285465810571397721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7170745523643873714265147 10756118285465810571397721)
                ·
                  refine ⟨8067088714099357928548291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10756118285465810571397721 8067088714099357928548291)
                  ·
                    refine ⟨12100633071149036892822437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8067088714099357928548291 12100633071149036892822437)
                    ·
                      refine ⟨2268868700840444417404207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12100633071149036892822437 2268868700840444417404207)
                      ·
                        rfl

theorem cell23_4418606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4418606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418606 prefixEnd_4418606 := by exact prefixLift 4418606
  have htrace : WordTrace (prefixWord ++ tailWord_4418606) baseStart_4418606 baseEnd_4418606 := by
    simpa [prefixWord, tailWord_4418606, baseEnd_4418606] using wordTrace_append hprefix tailTrace_4418606
  have hstable : (prefixWord ++ tailWord_4418606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418606).length < 2 ^ (prefixWord ++ tailWord_4418606).sum := by decide
  have hdescent : baseEnd_4418606 < baseStart_4418606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418632 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_4418632 : Nat := 118140960795 + 4418632 * 2 ^ 59
def prefixEnd_4418632 : Nat := 4983230072969 + 3 ^ 40 * 4418632 * 2
def baseEnd_4418632 : Nat := 2268882051337461315679087

theorem tailTrace_4418632 : CollatzResearch.WordTrace tailWord_4418632 prefixEnd_4418632 2268882051337461315679087 := by
  unfold tailWord_4418632
  simp only [CollatzResearch.WordTrace]
  refine ⟨80580374464029190555285075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107440499285372254073713433 80580374464029190555285075)
  ·
    refine ⟨120870561696043785832927613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80580374464029190555285075 120870561696043785832927613)
    ·
      refine ⟨45326460636016419687347855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120870561696043785832927613 45326460636016419687347855)
      ·
        refine ⟨67989690954024629531021783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45326460636016419687347855 67989690954024629531021783)
        ·
          refine ⟨101984536431036944296532675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67989690954024629531021783 101984536431036944296532675)
          ·
            refine ⟨152976804646555416444799013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101984536431036944296532675 152976804646555416444799013)
            ·
              refine ⟨28683150871229140583399815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152976804646555416444799013 28683150871229140583399815)
              ·
                refine ⟨43024726306843710875099723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28683150871229140583399815 43024726306843710875099723)
                ·
                  refine ⟨64537089460265566312649585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43024726306843710875099723 64537089460265566312649585)
                  ·
                    refine ⟨48402817095199174734487189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64537089460265566312649585 48402817095199174734487189)
                    ·
                      refine ⟨2268882051337461315679087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48402817095199174734487189 2268882051337461315679087)
                      ·
                        rfl

theorem cell23_4418632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_4418632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418632 prefixEnd_4418632 := by exact prefixLift 4418632
  have htrace : WordTrace (prefixWord ++ tailWord_4418632) baseStart_4418632 baseEnd_4418632 := by
    simpa [prefixWord, tailWord_4418632, baseEnd_4418632] using wordTrace_append hprefix tailTrace_4418632
  have hstable : (prefixWord ++ tailWord_4418632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418632).length < 2 ^ (prefixWord ++ tailWord_4418632).sum := by decide
  have hdescent : baseEnd_4418632 < baseStart_4418632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418656 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3]
def baseStart_4418656 : Nat := 118140960795 + 4418656 * 2 ^ 59
def prefixEnd_4418656 : Nat := 4983230072969 + 3 ^ 40 * 4418656 * 2
def baseEnd_4418656 : Nat := 2268894374873169221778977

theorem tailTrace_4418656 : CollatzResearch.WordTrace tailWord_4418656 prefixEnd_4418656 2268894374873169221778977 := by
  unfold tailWord_4418656
  simp only [CollatzResearch.WordTrace]
  refine ⟨80580812139985716604721911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107441082853314288806295881 80580812139985716604721911)
  ·
    refine ⟨120871218209978574907082867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80580812139985716604721911 120871218209978574907082867)
    ·
      refine ⟨181306827314967862360624301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120871218209978574907082867 181306827314967862360624301)
      ·
        refine ⟨67990060243112948385234113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181306827314967862360624301 67990060243112948385234113)
        ·
          refine ⟨50992545182334711288925585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67990060243112948385234113 50992545182334711288925585)
          ·
            refine ⟨38244408886751033466694189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50992545182334711288925585 38244408886751033466694189)
            ·
              refine ⟨14341653332531637550010321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38244408886751033466694189 14341653332531637550010321)
              ·
                refine ⟨10756239999398728162507741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14341653332531637550010321 10756239999398728162507741)
                ·
                  refine ⟨4033589999774523060940403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10756239999398728162507741 4033589999774523060940403)
                  ·
                    refine ⟨6050384999661784591410605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4033589999774523060940403 6050384999661784591410605)
                    ·
                      refine ⟨2268894374873169221778977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050384999661784591410605 2268894374873169221778977)
                      ·
                        rfl

theorem cell23_4418656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_4418656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418656 prefixEnd_4418656 := by exact prefixLift 4418656
  have htrace : WordTrace (prefixWord ++ tailWord_4418656) baseStart_4418656 baseEnd_4418656 := by
    simpa [prefixWord, tailWord_4418656, baseEnd_4418656] using wordTrace_append hprefix tailTrace_4418656
  have hstable : (prefixWord ++ tailWord_4418656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418656).length < 2 ^ (prefixWord ++ tailWord_4418656).sum := by decide
  have hdescent : baseEnd_4418656 < baseStart_4418656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418659 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 1, 5]
def baseStart_4418659 : Nat := 118140960795 + 4418659 * 2 ^ 59
def prefixEnd_4418659 : Nat := 4983230072969 + 3 ^ 40 * 4418659 * 2
def baseEnd_4418659 : Nat := 756298638438377570013821

theorem tailTrace_4418659 : CollatzResearch.WordTrace tailWord_4418659 prefixEnd_4418659 756298638438377570013821 := by
  unfold tailWord_4418659
  simp only [CollatzResearch.WordTrace]
  refine ⟨161161733698960564721803031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107441155799307043147868687 161161733698960564721803031)
  ·
    refine ⟨241742600548440847082704547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161161733698960564721803031 241742600548440847082704547)
    ·
      refine ⟨362613900822661270624056821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241742600548440847082704547 362613900822661270624056821)
      ·
        refine ⟨33995053202124494121005327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 362613900822661270624056821 33995053202124494121005327)
        ·
          refine ⟨50992579803186741181507991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33995053202124494121005327 50992579803186741181507991)
          ·
            refine ⟨76488869704780111772261987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50992579803186741181507991 76488869704780111772261987)
            ·
              refine ⟨114733304557170167658392981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76488869704780111772261987 114733304557170167658392981)
              ·
                refine ⟨5378123651117351608987171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114733304557170167658392981 5378123651117351608987171)
                ·
                  refine ⟨8067185476676027413480757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378123651117351608987171 8067185476676027413480757)
                  ·
                    refine ⟨756298638438377570013821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8067185476676027413480757 756298638438377570013821)
                    ·
                      rfl

theorem cell23_4418659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 5].length) (baseStart_4418659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418659 prefixEnd_4418659 := by exact prefixLift 4418659
  have htrace : WordTrace (prefixWord ++ tailWord_4418659) baseStart_4418659 baseEnd_4418659 := by
    simpa [prefixWord, tailWord_4418659, baseEnd_4418659] using wordTrace_append hprefix tailTrace_4418659
  have hstable : (prefixWord ++ tailWord_4418659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418659).length < 2 ^ (prefixWord ++ tailWord_4418659).sum := by decide
  have hdescent : baseEnd_4418659 < baseStart_4418659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418699 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3]
def baseStart_4418699 : Nat := 118140960795 + 4418699 * 2 ^ 59
def prefixEnd_4418699 : Nat := 4983230072969 + 3 ^ 40 * 4418699 * 2
def baseEnd_4418699 : Nat := 2268916454541312553541279

theorem tailTrace_4418699 : CollatzResearch.WordTrace tailWord_4418699 prefixEnd_4418699 2268916454541312553541279 := by
  unfold tailWord_4418699
  simp only [CollatzResearch.WordTrace]
  refine ⟨161163192618815651553259151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107442128412543767702172767 161163192618815651553259151)
  ·
    refine ⟨241744788928223477329888727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161163192618815651553259151 241744788928223477329888727)
    ·
      refine ⟨362617183392335215994833091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241744788928223477329888727 362617183392335215994833091)
      ·
        refine ⟨543925775088502823992249637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362617183392335215994833091 543925775088502823992249637)
        ·
          refine ⟨101986082829094279498546807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 543925775088502823992249637 101986082829094279498546807)
          ·
            refine ⟨152979124243641419247820211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101986082829094279498546807 152979124243641419247820211)
            ·
              refine ⟨229468686365462128871730317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152979124243641419247820211 229468686365462128871730317)
              ·
                refine ⟨86050757387048298326898869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229468686365462128871730317 86050757387048298326898869)
                ·
                  refine ⟨8067258505035777968146769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86050757387048298326898869 8067258505035777968146769)
                  ·
                    refine ⟨6050443878776833476110077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8067258505035777968146769 6050443878776833476110077)
                    ·
                      refine ⟨2268916454541312553541279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050443878776833476110077 2268916454541312553541279)
                      ·
                        rfl

theorem cell23_4418699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3].length) (baseStart_4418699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418699 prefixEnd_4418699 := by exact prefixLift 4418699
  have htrace : WordTrace (prefixWord ++ tailWord_4418699) baseStart_4418699 baseEnd_4418699 := by
    simpa [prefixWord, tailWord_4418699, baseEnd_4418699] using wordTrace_append hprefix tailTrace_4418699
  have hstable : (prefixWord ++ tailWord_4418699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418699).length < 2 ^ (prefixWord ++ tailWord_4418699).sum := by decide
  have hdescent : baseEnd_4418699 < baseStart_4418699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418706 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4418706 : Nat := 118140960795 + 4418706 * 2 ^ 59
def prefixEnd_4418706 : Nat := 4983230072969 + 3 ^ 40 * 4418706 * 2
def baseEnd_4418706 : Nat := 756306682968631342051249

theorem tailTrace_4418706 : CollatzResearch.WordTrace tailWord_4418706 prefixEnd_4418706 756306682968631342051249 := by
  unfold tailWord_4418706
  simp only [CollatzResearch.WordTrace]
  refine ⟨40290861982447572937190993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107442298619860194499175981 40290861982447572937190993)
  ·
    refine ⟨30218146486835679702893245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40290861982447572937190993 30218146486835679702893245)
    ·
      refine ⟨11331804932563379888584967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30218146486835679702893245 11331804932563379888584967)
      ·
        refine ⟨16997707398845069832877451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331804932563379888584967 16997707398845069832877451)
        ·
          refine ⟨25496561098267604749316177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16997707398845069832877451 25496561098267604749316177)
          ·
            refine ⟨19122420823700703561987133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25496561098267604749316177 19122420823700703561987133)
            ·
              refine ⟨7170907808887763835745175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19122420823700703561987133 7170907808887763835745175)
              ·
                refine ⟨10756361713331645753617763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7170907808887763835745175 10756361713331645753617763)
                ·
                  refine ⟨16134542569997468630426645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10756361713331645753617763 16134542569997468630426645)
                  ·
                    refine ⟨756306682968631342051249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16134542569997468630426645 756306682968631342051249)
                    ·
                      rfl

theorem cell23_4418706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4418706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418706 prefixEnd_4418706 := by exact prefixLift 4418706
  have htrace : WordTrace (prefixWord ++ tailWord_4418706) baseStart_4418706 baseEnd_4418706 := by
    simpa [prefixWord, tailWord_4418706, baseEnd_4418706] using wordTrace_append hprefix tailTrace_4418706
  have hstable : (prefixWord ++ tailWord_4418706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418706).length < 2 ^ (prefixWord ++ tailWord_4418706).sum := by decide
  have hdescent : baseEnd_4418706 < baseStart_4418706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418709 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4418709 : Nat := 118140960795 + 4418709 * 2 ^ 59
def prefixEnd_4418709 : Nat := 4983230072969 + 3 ^ 40 * 4418709 * 2
def baseEnd_4418709 : Nat := 2268921589347857514416233

theorem tailTrace_4418709 : CollatzResearch.WordTrace tailWord_4418709 prefixEnd_4418709 2268921589347857514416233 := by
  unfold tailWord_4418709
  simp only [CollatzResearch.WordTrace]
  refine ⟨161163557348779423261123181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107442371565852948840748787 161163557348779423261123181)
  ·
    refine ⟨60436334005792283722921193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161163557348779423261123181 60436334005792283722921193)
    ·
      refine ⟨45327250504344212792190895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60436334005792283722921193 45327250504344212792190895)
      ·
        refine ⟨67990875756516319188286343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45327250504344212792190895 67990875756516319188286343)
        ·
          refine ⟨101986313634774478782429515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67990875756516319188286343 101986313634774478782429515)
          ·
            refine ⟨152979470452161718173644273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101986313634774478782429515 152979470452161718173644273)
            ·
              refine ⟨114734602839121288630233205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152979470452161718173644273 114734602839121288630233205)
              ·
                refine ⟨10756369016167620809084363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114734602839121288630233205 10756369016167620809084363)
                ·
                  refine ⟨16134553524251431213626545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10756369016167620809084363 16134553524251431213626545)
                  ·
                    refine ⟨12100915143188573410219909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16134553524251431213626545 12100915143188573410219909)
                    ·
                      refine ⟨2268921589347857514416233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12100915143188573410219909 2268921589347857514416233)
                      ·
                        rfl

theorem cell23_4418709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4418709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418709 prefixEnd_4418709 := by exact prefixLift 4418709
  have htrace : WordTrace (prefixWord ++ tailWord_4418709) baseStart_4418709 baseEnd_4418709 := by
    simpa [prefixWord, tailWord_4418709, baseEnd_4418709] using wordTrace_append hprefix tailTrace_4418709
  have hstable : (prefixWord ++ tailWord_4418709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418709).length < 2 ^ (prefixWord ++ tailWord_4418709).sum := by decide
  have hdescent : baseEnd_4418709 < baseStart_4418709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418733 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_4418733 : Nat := 118140960795 + 4418733 * 2 ^ 59
def prefixEnd_4418733 : Nat := 4983230072969 + 3 ^ 40 * 4418733 * 2
def baseEnd_4418733 : Nat := 2268933912883565420516123

theorem tailTrace_4418733 : CollatzResearch.WordTrace tailWord_4418733 prefixEnd_4418733 2268933912883565420516123 := by
  unfold tailWord_4418733
  simp only [CollatzResearch.WordTrace]
  refine ⟨161164432700692475359996853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107442955133794983573331235 161164432700692475359996853)
  ·
    refine ⟨15109165565689919564999705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161164432700692475359996853 15109165565689919564999705)
    ·
      refine ⟨11331874174267439673749779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15109165565689919564999705 11331874174267439673749779)
      ·
        refine ⟨16997811261401159510624669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331874174267439673749779 16997811261401159510624669)
        ·
          refine ⟨6374179223025434816484251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16997811261401159510624669 6374179223025434816484251)
          ·
            refine ⟨9561268834538152224726377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6374179223025434816484251 9561268834538152224726377)
            ·
              refine ⟨7170951625903614168544783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9561268834538152224726377 7170951625903614168544783)
              ·
                refine ⟨10756427438855421252817175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7170951625903614168544783 10756427438855421252817175)
                ·
                  refine ⟨16134641158283131879225763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10756427438855421252817175 16134641158283131879225763)
                  ·
                    refine ⟨24201961737424697818838645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16134641158283131879225763 24201961737424697818838645)
                    ·
                      refine ⟨2268933912883565420516123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24201961737424697818838645 2268933912883565420516123)
                      ·
                        rfl

theorem cell23_4418733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_4418733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418733 prefixEnd_4418733 := by exact prefixLift 4418733
  have htrace : WordTrace (prefixWord ++ tailWord_4418733) baseStart_4418733 baseEnd_4418733 := by
    simpa [prefixWord, tailWord_4418733, baseEnd_4418733] using wordTrace_append hprefix tailTrace_4418733
  have hstable : (prefixWord ++ tailWord_4418733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418733).length < 2 ^ (prefixWord ++ tailWord_4418733).sum := by decide
  have hdescent : baseEnd_4418733 < baseStart_4418733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418809 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 7]
def baseStart_4418809 : Nat := 118140960795 + 4418809 * 2 ^ 59
def prefixEnd_4418809 : Nat := 4983230072969 + 3 ^ 40 * 4418809 * 2
def baseEnd_4418809 : Nat := 252108104157034124796197

theorem tailTrace_4418809 : CollatzResearch.WordTrace tailWord_4418809 prefixEnd_4418809 252108104157034124796197 := by
  unfold tailWord_4418809
  simp only [CollatzResearch.WordTrace]
  refine ⟨161167204648417140339763481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107444803098944760226508987 161167204648417140339763481)
  ·
    refine ⟨120875403486312855254822611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161167204648417140339763481 120875403486312855254822611)
    ·
      refine ⟨181313105229469282882233917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120875403486312855254822611 181313105229469282882233917)
      ·
        refine ⟨67992414461050981080837719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181313105229469282882233917 67992414461050981080837719)
        ·
          refine ⟨101988621691576471621256579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67992414461050981080837719 101988621691576471621256579)
          ·
            refine ⟨152982932537364707431884869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101988621691576471621256579 152982932537364707431884869)
            ·
              refine ⟨28684299850755882643478413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152982932537364707431884869 28684299850755882643478413)
              ·
                refine ⟨10756612444033455991304405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28684299850755882643478413 10756612444033455991304405)
                ·
                  refine ⟨252108104157034124796197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10756612444033455991304405 252108104157034124796197)
                  ·
                    rfl

theorem cell23_4418809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_4418809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418809 prefixEnd_4418809 := by exact prefixLift 4418809
  have htrace : WordTrace (prefixWord ++ tailWord_4418809) baseStart_4418809 baseEnd_4418809 := by
    simpa [prefixWord, tailWord_4418809, baseEnd_4418809] using wordTrace_append hprefix tailTrace_4418809
  have hstable : (prefixWord ++ tailWord_4418809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418809).length < 2 ^ (prefixWord ++ tailWord_4418809).sum := by decide
  have hdescent : baseEnd_4418809 < baseStart_4418809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418820 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_4418820 : Nat := 118140960795 + 4418820 * 2 ^ 59
def prefixEnd_4418820 : Nat := 4983230072969 + 3 ^ 40 * 4418820 * 2
def baseEnd_4418820 : Nat := 2268978585700506580128223

theorem tailTrace_4418820 : CollatzResearch.WordTrace tailWord_4418820 prefixEnd_4418820 2268978585700506580128223 := by
  unfold tailWord_4418820
  simp only [CollatzResearch.WordTrace]
  refine ⟨80583802925688644609206957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107445070567584859478942609 80583802925688644609206957)
  ·
    refine ⟨30218926097133241728452609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80583802925688644609206957 30218926097133241728452609)
    ·
      refine ⟨22664194572849931296339457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30218926097133241728452609 22664194572849931296339457)
      ·
        refine ⟨16998145929637448472254593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22664194572849931296339457 16998145929637448472254593)
        ·
          refine ⟨12748609447228086354190945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16998145929637448472254593 12748609447228086354190945)
          ·
            refine ⟨9561457085421064765643209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12748609447228086354190945 9561457085421064765643209)
            ·
              refine ⟨7171092814065798574232407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9561457085421064765643209 7171092814065798574232407)
              ·
                refine ⟨10756639221098697861348611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171092814065798574232407 10756639221098697861348611)
                ·
                  refine ⟨16134958831648046792022917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10756639221098697861348611 16134958831648046792022917)
                  ·
                    refine ⟨3025304780934008773504297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16134958831648046792022917 3025304780934008773504297)
                    ·
                      refine ⟨2268978585700506580128223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025304780934008773504297 2268978585700506580128223)
                      ·
                        rfl

theorem cell23_4418820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_4418820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418820 prefixEnd_4418820 := by exact prefixLift 4418820
  have htrace : WordTrace (prefixWord ++ tailWord_4418820) baseStart_4418820 baseEnd_4418820 := by
    simpa [prefixWord, tailWord_4418820, baseEnd_4418820] using wordTrace_append hprefix tailTrace_4418820
  have hstable : (prefixWord ++ tailWord_4418820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418820).length < 2 ^ (prefixWord ++ tailWord_4418820).sum := by decide
  have hdescent : baseEnd_4418820 < baseStart_4418820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418859 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_4418859 : Nat := 118140960795 + 4418859 * 2 ^ 59
def prefixEnd_4418859 : Nat := 4983230072969 + 3 ^ 40 * 4418859 * 2
def baseEnd_4418859 : Nat := 2268998611446031927540543

theorem tailTrace_4418859 : CollatzResearch.WordTrace tailWord_4418859 prefixEnd_4418859 2268998611446031927540543 := by
  unfold tailWord_4418859
  simp only [CollatzResearch.WordTrace]
  refine ⟨161169028298235998879083631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107446018865490665919389087 161169028298235998879083631)
  ·
    refine ⟨241753542447353998318625447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161169028298235998879083631 241753542447353998318625447)
    ·
      refine ⟨362630313671030997477938171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241753542447353998318625447 362630313671030997477938171)
      ·
        refine ⟨543945470506546496216907257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362630313671030997477938171 543945470506546496216907257)
        ·
          refine ⟨407959102879909872162680443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543945470506546496216907257 407959102879909872162680443)
          ·
            refine ⟨611938654319864808244020665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407959102879909872162680443 611938654319864808244020665)
            ·
              refine ⟨458953990739898606183015499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611938654319864808244020665 458953990739898606183015499)
              ·
                refine ⟨688430986109847909274523249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458953990739898606183015499 688430986109847909274523249)
                ·
                  refine ⟨516323239582385931955892437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688430986109847909274523249 516323239582385931955892437)
                  ·
                    refine ⟨12101325927712170280216229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 516323239582385931955892437 12101325927712170280216229)
                    ·
                      refine ⟨2268998611446031927540543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12101325927712170280216229 2268998611446031927540543)
                      ·
                        rfl

theorem cell23_4418859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_4418859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418859 prefixEnd_4418859 := by exact prefixLift 4418859
  have htrace : WordTrace (prefixWord ++ tailWord_4418859) baseStart_4418859 baseEnd_4418859 := by
    simpa [prefixWord, tailWord_4418859, baseEnd_4418859] using wordTrace_append hprefix tailTrace_4418859
  have hstable : (prefixWord ++ tailWord_4418859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418859).length < 2 ^ (prefixWord ++ tailWord_4418859).sum := by decide
  have hdescent : baseEnd_4418859 < baseStart_4418859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418876 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_4418876 : Nat := 118140960795 + 4418876 * 2 ^ 59
def prefixEnd_4418876 : Nat := 4983230072969 + 3 ^ 40 * 4418876 * 2
def baseEnd_4418876 : Nat := 2269007340617158361027965

theorem tailTrace_4418876 : CollatzResearch.WordTrace tailWord_4418876 prefixEnd_4418876 2269007340617158361027965 := by
  unfold tailWord_4418876
  simp only [CollatzResearch.WordTrace]
  refine ⟨80584824169587205391226241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107446432226116273854968321 80584824169587205391226241)
  ·
    refine ⟨60438618127190404043419681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80584824169587205391226241 60438618127190404043419681)
    ·
      refine ⟨45328963595392803032564761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60438618127190404043419681 45328963595392803032564761)
      ·
        refine ⟨33996722696544602274423571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45328963595392803032564761 33996722696544602274423571)
        ·
          refine ⟨50995084044816903411635357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33996722696544602274423571 50995084044816903411635357)
          ·
            refine ⟨19123156516806338779363259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50995084044816903411635357 19123156516806338779363259)
            ·
              refine ⟨28684734775209508169044889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19123156516806338779363259 28684734775209508169044889)
              ·
                refine ⟨21513551081407131126783667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28684734775209508169044889 21513551081407131126783667)
                ·
                  refine ⟨32270326622110696690175501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21513551081407131126783667 32270326622110696690175501)
                  ·
                    refine ⟨12101372483291511258815813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32270326622110696690175501 12101372483291511258815813)
                    ·
                      refine ⟨2269007340617158361027965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12101372483291511258815813 2269007340617158361027965)
                      ·
                        rfl

theorem cell23_4418876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_4418876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418876 prefixEnd_4418876 := by exact prefixLift 4418876
  have htrace : WordTrace (prefixWord ++ tailWord_4418876) baseStart_4418876 baseEnd_4418876 := by
    simpa [prefixWord, tailWord_4418876, baseEnd_4418876] using wordTrace_append hprefix tailTrace_4418876
  have hstable : (prefixWord ++ tailWord_4418876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418876).length < 2 ^ (prefixWord ++ tailWord_4418876).sum := by decide
  have hdescent : baseEnd_4418876 < baseStart_4418876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418896 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_4418896 : Nat := 118140960795 + 4418896 * 2 ^ 59
def prefixEnd_4418896 : Nat := 4983230072969 + 3 ^ 40 * 4418896 * 2
def baseEnd_4418896 : Nat := 2269017610230248282777873

theorem tailTrace_4418896 : CollatzResearch.WordTrace tailWord_4418896 prefixEnd_4418896 2269017610230248282777873 := by
  unfold tailWord_4418896
  simp only [CollatzResearch.WordTrace]
  refine ⟨80585188899550977099090271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107446918532734636132120361 80585188899550977099090271)
  ·
    refine ⟨120877783349326465648635407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80585188899550977099090271 120877783349326465648635407)
    ·
      refine ⟨181316675023989698472953111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120877783349326465648635407 181316675023989698472953111)
      ·
        refine ⟨271975012535984547709429667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181316675023989698472953111 271975012535984547709429667)
        ·
          refine ⟨407962518803976821564144501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271975012535984547709429667 407962518803976821564144501)
          ·
            refine ⟨38246486137872827021638547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 407962518803976821564144501 38246486137872827021638547)
            ·
              refine ⟨57369729206809240532457821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38246486137872827021638547 57369729206809240532457821)
              ·
                refine ⟨21513648452553465199671683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57369729206809240532457821 21513648452553465199671683)
                ·
                  refine ⟨32270472678830197799507525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21513648452553465199671683 32270472678830197799507525)
                  ·
                    refine ⟨6050713627280662087407661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32270472678830197799507525 6050713627280662087407661)
                    ·
                      refine ⟨2269017610230248282777873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6050713627280662087407661 2269017610230248282777873)
                      ·
                        rfl

theorem cell23_4418896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_4418896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418896 prefixEnd_4418896 := by exact prefixLift 4418896
  have htrace : WordTrace (prefixWord ++ tailWord_4418896) baseStart_4418896 baseEnd_4418896 := by
    simpa [prefixWord, tailWord_4418896, baseEnd_4418896] using wordTrace_append hprefix tailTrace_4418896
  have hstable : (prefixWord ++ tailWord_4418896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418896).length < 2 ^ (prefixWord ++ tailWord_4418896).sum := by decide
  have hdescent : baseEnd_4418896 < baseStart_4418896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418899 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 10]
def baseStart_4418899 : Nat := 118140960795 + 4418899 * 2 ^ 59
def prefixEnd_4418899 : Nat := 4983230072969 + 3 ^ 40 * 4418899 * 2
def baseEnd_4418899 : Nat := 252113238963579085671151

theorem tailTrace_4418899 : CollatzResearch.WordTrace tailWord_4418899 prefixEnd_4418899 252113238963579085671151 := by
  unfold tailWord_4418899
  simp only [CollatzResearch.WordTrace]
  refine ⟨161170487218091085710539751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107446991478727390473693167 161170487218091085710539751)
  ·
    refine ⟨241755730827136628565809627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161170487218091085710539751 241755730827136628565809627)
    ·
      refine ⟨362633596240704942848714441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241755730827136628565809627 362633596240704942848714441)
      ·
        refine ⟨271975197180528707136535831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362633596240704942848714441 271975197180528707136535831)
        ·
          refine ⟨407962795770793060704803747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271975197180528707136535831 407962795770793060704803747)
          ·
            refine ⟨611944193656189591057205621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407962795770793060704803747 611944193656189591057205621)
            ·
              refine ⟨57369768155267774161613027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 611944193656189591057205621 57369768155267774161613027)
              ·
                refine ⟨86054652232901661242419541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57369768155267774161613027 86054652232901661242419541)
                ·
                  refine ⟨252113238963579085671151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 86054652232901661242419541 252113238963579085671151)
                  ·
                    rfl

theorem cell23_4418899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 10].length) (baseStart_4418899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418899 prefixEnd_4418899 := by exact prefixLift 4418899
  have htrace : WordTrace (prefixWord ++ tailWord_4418899) baseStart_4418899 baseEnd_4418899 := by
    simpa [prefixWord, tailWord_4418899, baseEnd_4418899] using wordTrace_append hprefix tailTrace_4418899
  have hstable : (prefixWord ++ tailWord_4418899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418899).length < 2 ^ (prefixWord ++ tailWord_4418899).sum := by decide
  have hdescent : baseEnd_4418899 < baseStart_4418899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418916 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 8]
def baseStart_4418916 : Nat := 118140960795 + 4418916 * 2 ^ 59
def prefixEnd_4418916 : Nat := 4983230072969 + 3 ^ 40 * 4418916 * 2
def baseEnd_4418916 : Nat := 252114208871482022725309

theorem tailTrace_4418916 : CollatzResearch.WordTrace tailWord_4418916 prefixEnd_4418916 252114208871482022725309 := by
  unfold tailWord_4418916
  simp only [CollatzResearch.WordTrace]
  refine ⟨80585553629514748806954301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107447404839352998409272401 80585553629514748806954301)
  ·
    refine ⟨30219582611068030802607863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80585553629514748806954301 30219582611068030802607863)
    ·
      refine ⟨45329373916602046203911795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30219582611068030802607863 45329373916602046203911795)
      ·
        refine ⟨67994060874903069305867693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45329373916602046203911795 67994060874903069305867693)
        ·
          refine ⟨25497772828088650989700385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67994060874903069305867693 25497772828088650989700385)
          ·
            refine ⟨19123329621066488242275289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25497772828088650989700385 19123329621066488242275289)
            ·
              refine ⟨14342497215799866181706467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19123329621066488242275289 14342497215799866181706467)
              ·
                refine ⟨21513745823699799272559701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14342497215799866181706467 21513745823699799272559701)
                ·
                  refine ⟨252114208871482022725309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21513745823699799272559701 252114208871482022725309)
                  ·
                    rfl

theorem cell23_4418916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_4418916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418916 prefixEnd_4418916 := by exact prefixLift 4418916
  have htrace : WordTrace (prefixWord ++ tailWord_4418916) baseStart_4418916 baseEnd_4418916 := by
    simpa [prefixWord, tailWord_4418916, baseEnd_4418916] using wordTrace_append hprefix tailTrace_4418916
  have hstable : (prefixWord ++ tailWord_4418916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418916).length < 2 ^ (prefixWord ++ tailWord_4418916).sum := by decide
  have hdescent : baseEnd_4418916 < baseStart_4418916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418970 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4418970 : Nat := 118140960795 + 4418970 * 2 ^ 59
def prefixEnd_4418970 : Nat := 4983230072969 + 3 ^ 40 * 4418970 * 2
def baseEnd_4418970 : Nat := 2269055607798680993252533

theorem tailTrace_4418970 : CollatzResearch.WordTrace tailWord_4418970 prefixEnd_4418970 2269055607798680993252533 := by
  unfold tailWord_4418970
  simp only [CollatzResearch.WordTrace]
  refine ⟨40293269200208466209093591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107448717867222576557582909 40293269200208466209093591)
  ·
    refine ⟨60439903800312699313640387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40293269200208466209093591 60439903800312699313640387)
    ·
      refine ⟨90659855700469048970460581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60439903800312699313640387 90659855700469048970460581)
      ·
        refine ⟨16998722943837946681961359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90659855700469048970460581 16998722943837946681961359)
        ·
          refine ⟨25498084415756920022942039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16998722943837946681961359 25498084415756920022942039)
          ·
            refine ⟨38247126623635380034413059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25498084415756920022942039 38247126623635380034413059)
            ·
              refine ⟨57370689935453070051619589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38247126623635380034413059 57370689935453070051619589)
              ·
                refine ⟨10757004362897450634678673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57370689935453070051619589 10757004362897450634678673)
                ·
                  refine ⟨8067753272173087976009005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10757004362897450634678673 8067753272173087976009005)
                  ·
                    refine ⟨3025407477064907991003377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8067753272173087976009005 3025407477064907991003377)
                    ·
                      refine ⟨2269055607798680993252533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025407477064907991003377 2269055607798680993252533)
                      ·
                        rfl

theorem cell23_4418970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4418970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418970 prefixEnd_4418970 := by exact prefixLift 4418970
  have htrace : WordTrace (prefixWord ++ tailWord_4418970) baseStart_4418970 baseEnd_4418970 := by
    simpa [prefixWord, tailWord_4418970, baseEnd_4418970] using wordTrace_append hprefix tailTrace_4418970
  have hstable : (prefixWord ++ tailWord_4418970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418970).length < 2 ^ (prefixWord ++ tailWord_4418970).sum := by decide
  have hdescent : baseEnd_4418970 < baseStart_4418970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418976 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_4418976 : Nat := 118140960795 + 4418976 * 2 ^ 59
def prefixEnd_4418976 : Nat := 4983230072969 + 3 ^ 40 * 4418976 * 2
def baseEnd_4418976 : Nat := 756352896227535989925835

theorem tailTrace_4418976 : CollatzResearch.WordTrace tailWord_4418976 prefixEnd_4418976 756352896227535989925835 := by
  unfold tailWord_4418976
  simp only [CollatzResearch.WordTrace]
  refine ⟨80586647819406063930546391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107448863759208085240728521 80586647819406063930546391)
  ·
    refine ⟨120879971729109095895819587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80586647819406063930546391 120879971729109095895819587)
    ·
      refine ⟨181319957593663643843729381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120879971729109095895819587 181319957593663643843729381)
      ·
        refine ⟨33997492048811933220699259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181319957593663643843729381 33997492048811933220699259)
        ·
          refine ⟨50996238073217899831048889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33997492048811933220699259 50996238073217899831048889)
          ·
            refine ⟨38247178554913424873286667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50996238073217899831048889 38247178554913424873286667)
            ·
              refine ⟨57370767832370137309930001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38247178554913424873286667 57370767832370137309930001)
              ·
                refine ⟨43028075874277602982447501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57370767832370137309930001 43028075874277602982447501)
                ·
                  refine ⟨16135528452854101118417813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43028075874277602982447501 16135528452854101118417813)
                  ·
                    refine ⟨756352896227535989925835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16135528452854101118417813 756352896227535989925835)
                    ·
                      rfl

theorem cell23_4418976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_4418976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418976 prefixEnd_4418976 := by exact prefixLift 4418976
  have htrace : WordTrace (prefixWord ++ tailWord_4418976) baseStart_4418976 baseEnd_4418976 := by
    simpa [prefixWord, tailWord_4418976, baseEnd_4418976] using wordTrace_append hprefix tailTrace_4418976
  have hstable : (prefixWord ++ tailWord_4418976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418976).length < 2 ^ (prefixWord ++ tailWord_4418976).sum := by decide
  have hdescent : baseEnd_4418976 < baseStart_4418976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418983 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4418983 : Nat := 118140960795 + 4418983 * 2 ^ 59
def prefixEnd_4418983 : Nat := 4983230072969 + 3 ^ 40 * 4418983 * 2
def baseEnd_4418983 : Nat := 2269062283047189442389973

theorem tailTrace_4418983 : CollatzResearch.WordTrace tailWord_4418983 prefixEnd_4418983 2269062283047189442389973 := by
  unfold tailWord_4418983
  simp only [CollatzResearch.WordTrace]
  refine ⟨161173550949786768056597603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107449033966524512037731735 161173550949786768056597603)
  ·
    refine ⟨241760326424680152084896405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161173550949786768056597603 241760326424680152084896405)
    ·
      refine ⟨11332515301156882128979519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 241760326424680152084896405 11332515301156882128979519)
      ·
        refine ⟨16998772951735323193469279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11332515301156882128979519 16998772951735323193469279)
        ·
          refine ⟨25498159427602984790203919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16998772951735323193469279 25498159427602984790203919)
          ·
            refine ⟨38247239141404477185305879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25498159427602984790203919 38247239141404477185305879)
            ·
              refine ⟨57370858712106715777958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38247239141404477185305879 57370858712106715777958819)
              ·
                refine ⟨86056288068160073666938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57370858712106715777958819 86056288068160073666938229)
                ·
                  refine ⟨8067777006390006906275459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86056288068160073666938229 8067777006390006906275459)
                  ·
                    refine ⟨12101665509585010359413189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8067777006390006906275459 12101665509585010359413189)
                    ·
                      refine ⟨2269062283047189442389973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12101665509585010359413189 2269062283047189442389973)
                      ·
                        rfl

theorem cell23_4418983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4418983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418983 prefixEnd_4418983 := by exact prefixLift 4418983
  have htrace : WordTrace (prefixWord ++ tailWord_4418983) baseStart_4418983 baseEnd_4418983 := by
    simpa [prefixWord, tailWord_4418983, baseEnd_4418983] using wordTrace_append hprefix tailTrace_4418983
  have hstable : (prefixWord ++ tailWord_4418983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418983).length < 2 ^ (prefixWord ++ tailWord_4418983).sum := by decide
  have hdescent : baseEnd_4418983 < baseStart_4418983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4418993 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_4418993 : Nat := 118140960795 + 4418993 * 2 ^ 59
def prefixEnd_4418993 : Nat := 4983230072969 + 3 ^ 40 * 4418993 * 2
def baseEnd_4418993 : Nat := 756355805951244801088309

theorem tailTrace_4418993 : CollatzResearch.WordTrace tailWord_4418993 prefixEnd_4418993 756355805951244801088309 := by
  unfold tailWord_4418993
  simp only [CollatzResearch.WordTrace]
  refine ⟨161173915679750539764461633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107449277119833693176307755 161173915679750539764461633)
  ·
    refine ⟨120880436759812904823346225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161173915679750539764461633 120880436759812904823346225)
    ·
      refine ⟨90660327569859678617509669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120880436759812904823346225 90660327569859678617509669)
      ·
        refine ⟨16998811419348689740783063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90660327569859678617509669 16998811419348689740783063)
        ·
          refine ⟨25498217129023034611174595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16998811419348689740783063 25498217129023034611174595)
          ·
            refine ⟨38247325693534551916761893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25498217129023034611174595 38247325693534551916761893)
            ·
              refine ⟨7171373567537728484392855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38247325693534551916761893 7171373567537728484392855)
              ·
                refine ⟨10757060351306592726589283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171373567537728484392855 10757060351306592726589283)
                ·
                  refine ⟨16135590526959889089883925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10757060351306592726589283 16135590526959889089883925)
                  ·
                    refine ⟨756355805951244801088309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16135590526959889089883925 756355805951244801088309)
                    ·
                      rfl

theorem cell23_4418993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_4418993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4418993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4418993 prefixEnd_4418993 := by exact prefixLift 4418993
  have htrace : WordTrace (prefixWord ++ tailWord_4418993) baseStart_4418993 baseEnd_4418993 := by
    simpa [prefixWord, tailWord_4418993, baseEnd_4418993] using wordTrace_append hprefix tailTrace_4418993
  have hstable : (prefixWord ++ tailWord_4418993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4418993).length < 2 ^ (prefixWord ++ tailWord_4418993).sum := by decide
  have hdescent : baseEnd_4418993 < baseStart_4418993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4418993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419000 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_4419000 : Nat := 118140960795 + 4419000 * 2 ^ 59
def prefixEnd_4419000 : Nat := 4983230072969 + 3 ^ 40 * 4419000 * 2
def baseEnd_4419000 : Nat := 2269071012218315875877395

theorem tailTrace_4419000 : CollatzResearch.WordTrace tailWord_4419000 prefixEnd_4419000 2269071012218315875877395 := by
  unfold tailWord_4419000
  simp only [CollatzResearch.WordTrace]
  refine ⟨80587085495362589979983227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107449447327150119973310969 80587085495362589979983227)
  ·
    refine ⟨120880628243043884969974841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80587085495362589979983227 120880628243043884969974841)
    ·
      refine ⟨90660471182282913727481131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120880628243043884969974841 90660471182282913727481131)
      ·
        refine ⟨135990706773424370591221697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90660471182282913727481131 135990706773424370591221697)
        ·
          refine ⟨101993030080068277943416273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135990706773424370591221697 101993030080068277943416273)
          ·
            refine ⟨76494772560051208457562205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101993030080068277943416273 76494772560051208457562205)
            ·
              refine ⟨28685539710019203171585827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76494772560051208457562205 28685539710019203171585827)
              ·
                refine ⟨43028309565028804757378741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28685539710019203171585827 43028309565028804757378741)
                ·
                  refine ⟨4033904021721450446004257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43028309565028804757378741 4033904021721450446004257)
                  ·
                    refine ⟨3025428016291087834503193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033904021721450446004257 3025428016291087834503193)
                    ·
                      refine ⟨2269071012218315875877395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025428016291087834503193 2269071012218315875877395)
                      ·
                        rfl

theorem cell23_4419000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_4419000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419000 prefixEnd_4419000 := by exact prefixLift 4419000
  have htrace : WordTrace (prefixWord ++ tailWord_4419000) baseStart_4419000 baseEnd_4419000 := by
    simpa [prefixWord, tailWord_4419000, baseEnd_4419000] using wordTrace_append hprefix tailTrace_4419000
  have hstable : (prefixWord ++ tailWord_4419000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419000).length < 2 ^ (prefixWord ++ tailWord_4419000).sum := by decide
  have hdescent : baseEnd_4419000 < baseStart_4419000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419004 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4419004 : Nat := 118140960795 + 4419004 * 2 ^ 59
def prefixEnd_4419004 : Nat := 4983230072969 + 3 ^ 40 * 4419004 * 2
def baseEnd_4419004 : Nat := 2269073066140933860227377

theorem tailTrace_4419004 : CollatzResearch.WordTrace tailWord_4419004 prefixEnd_4419004 2269073066140933860227377 := by
  unfold tailWord_4419004
  simp only [CollatzResearch.WordTrace]
  refine ⟨80587158441355344321556033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107449544588473792428741377 80587158441355344321556033)
  ·
    refine ⟨60440368831016508241167025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80587158441355344321556033 60440368831016508241167025)
    ·
      refine ⟨45330276623262381180875269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60440368831016508241167025 45330276623262381180875269)
      ·
        refine ⟨8499426866861696471414113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45330276623262381180875269 8499426866861696471414113)
        ·
          refine ⟨6374570150146272353560585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8499426866861696471414113 6374570150146272353560585)
          ·
            refine ⟨4780927612609704265170439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6374570150146272353560585 4780927612609704265170439)
            ·
              refine ⟨7171391418914556397755659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780927612609704265170439 7171391418914556397755659)
              ·
                refine ⟨10757087128371834596633489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171391418914556397755659 10757087128371834596633489)
                ·
                  refine ⟨8067815346278875947475117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10757087128371834596633489 8067815346278875947475117)
                  ·
                    refine ⟨3025430754854578480303169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8067815346278875947475117 3025430754854578480303169)
                    ·
                      refine ⟨2269073066140933860227377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025430754854578480303169 2269073066140933860227377)
                      ·
                        rfl

theorem cell23_4419004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4419004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419004 prefixEnd_4419004 := by exact prefixLift 4419004
  have htrace : WordTrace (prefixWord ++ tailWord_4419004) baseStart_4419004 baseEnd_4419004 := by
    simpa [prefixWord, tailWord_4419004, baseEnd_4419004] using wordTrace_append hprefix tailTrace_4419004
  have hstable : (prefixWord ++ tailWord_4419004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419004).length < 2 ^ (prefixWord ++ tailWord_4419004).sum := by decide
  have hdescent : baseEnd_4419004 < baseStart_4419004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419034 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2]
def baseStart_4419034 : Nat := 118140960795 + 4419034 * 2 ^ 59
def prefixEnd_4419034 : Nat := 4983230072969 + 3 ^ 40 * 4419034 * 2
def baseEnd_4419034 : Nat := 2269088470560568742852239

theorem tailTrace_4419034 : CollatzResearch.WordTrace tailWord_4419034 prefixEnd_4419034 2269088470560568742852239 := by
  unfold tailWord_4419034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40293852768150500941676039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107450274048401335844469437 40293852768150500941676039)
  ·
    refine ⟨60440779152225751412514059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40293852768150500941676039 60440779152225751412514059)
    ·
      refine ⟨90661168728338627118771089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60440779152225751412514059 90661168728338627118771089)
      ·
        refine ⟨67995876546253970339078317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90661168728338627118771089 67995876546253970339078317)
        ·
          refine ⟨25498453704845238877154369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67995876546253970339078317 25498453704845238877154369)
          ·
            refine ⟨19123840278633929157865777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25498453704845238877154369 19123840278633929157865777)
            ·
              refine ⟨14342880208975446868399333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19123840278633929157865777 14342880208975446868399333)
              ·
                refine ⟨2689290039182896287824875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14342880208975446868399333 2689290039182896287824875)
                ·
                  refine ⟨4033935058774344431737313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689290039182896287824875 4033935058774344431737313)
                  ·
                    refine ⟨3025451294080758323802985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033935058774344431737313 3025451294080758323802985)
                    ·
                      refine ⟨2269088470560568742852239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025451294080758323802985 2269088470560568742852239)
                      ·
                        rfl

theorem cell23_4419034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_4419034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419034 prefixEnd_4419034 := by exact prefixLift 4419034
  have htrace : WordTrace (prefixWord ++ tailWord_4419034) baseStart_4419034 baseEnd_4419034 := by
    simpa [prefixWord, tailWord_4419034, baseEnd_4419034] using wordTrace_append hprefix tailTrace_4419034
  have hstable : (prefixWord ++ tailWord_4419034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419034).length < 2 ^ (prefixWord ++ tailWord_4419034).sum := by decide
  have hdescent : baseEnd_4419034 < baseStart_4419034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419085 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4419085 : Nat := 118140960795 + 4419085 * 2 ^ 59
def prefixEnd_4419085 : Nat := 4983230072969 + 3 ^ 40 * 4419085 * 2
def baseEnd_4419085 : Nat := 2269114658073948043314505

theorem tailTrace_4419085 : CollatzResearch.WordTrace tailWord_4419085 prefixEnd_4419085 2269114658073948043314505 := by
  unfold tailWord_4419085
  simp only [CollatzResearch.WordTrace]
  refine ⟨161177271195417239476810709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107451514130278159651207139 161177271195417239476810709)
  ·
    refine ⟨3777592293642591550237751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 161177271195417239476810709 3777592293642591550237751)
    ·
      refine ⟨5666388440463887325356627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777592293642591550237751 5666388440463887325356627)
      ·
        refine ⟨8499582660695830988034941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5666388440463887325356627 8499582660695830988034941)
        ·
          refine ⟨3187343497760936620513103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8499582660695830988034941 3187343497760936620513103)
          ·
            refine ⟨4781015246641404930769655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187343497760936620513103 4781015246641404930769655)
            ·
              refine ⟨7171522869962107396154483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781015246641404930769655 7171522869962107396154483)
              ·
                refine ⟨10757284304943161094231725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171522869962107396154483 10757284304943161094231725)
                ·
                  refine ⟨4033981614353685410336897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10757284304943161094231725 4033981614353685410336897)
                  ·
                    refine ⟨3025486210765264057752673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4033981614353685410336897 3025486210765264057752673)
                    ·
                      refine ⟨2269114658073948043314505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025486210765264057752673 2269114658073948043314505)
                      ·
                        rfl

theorem cell23_4419085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4419085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419085 prefixEnd_4419085 := by exact prefixLift 4419085
  have htrace : WordTrace (prefixWord ++ tailWord_4419085) baseStart_4419085 baseEnd_4419085 := by
    simpa [prefixWord, tailWord_4419085, baseEnd_4419085] using wordTrace_append hprefix tailTrace_4419085
  have hstable : (prefixWord ++ tailWord_4419085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419085).length < 2 ^ (prefixWord ++ tailWord_4419085).sum := by decide
  have hdescent : baseEnd_4419085 < baseStart_4419085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419103 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_4419103 : Nat := 118140960795 + 4419103 * 2 ^ 59
def prefixEnd_4419103 : Nat := 4983230072969 + 3 ^ 40 * 4419103 * 2
def baseEnd_4419103 : Nat := 2269123900725728972889421

theorem tailTrace_4419103 : CollatzResearch.WordTrace tailWord_4419103 prefixEnd_4419103 2269123900725728972889421 := by
  unfold tailWord_4419103
  simp only [CollatzResearch.WordTrace]
  refine ⟨161177927709352028550965963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107451951806234685700643975 161177927709352028550965963)
  ·
    refine ⟨241766891564028042826448945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161177927709352028550965963 241766891564028042826448945)
    ·
      refine ⟨181325168673021032119836709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241766891564028042826448945 181325168673021032119836709)
      ·
        refine ⟨33998469126191443522469383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181325168673021032119836709 33998469126191443522469383)
        ·
          refine ⟨50997703689287165283704075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33998469126191443522469383 50997703689287165283704075)
          ·
            refine ⟨76496555533930747925556113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50997703689287165283704075 76496555533930747925556113)
            ·
              refine ⟨57372416650448060944167085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76496555533930747925556113 57372416650448060944167085)
              ·
                refine ⟨21514656243918022854062657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57372416650448060944167085 21514656243918022854062657)
                ·
                  refine ⟨16135992182938517140546993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21514656243918022854062657 16135992182938517140546993)
                  ·
                    refine ⟨12101994137203887855410245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16135992182938517140546993 12101994137203887855410245)
                    ·
                      refine ⟨2269123900725728972889421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12101994137203887855410245 2269123900725728972889421)
                      ·
                        rfl

theorem cell23_4419103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_4419103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419103 prefixEnd_4419103 := by exact prefixLift 4419103
  have htrace : WordTrace (prefixWord ++ tailWord_4419103) baseStart_4419103 baseEnd_4419103 := by
    simpa [prefixWord, tailWord_4419103, baseEnd_4419103] using wordTrace_append hprefix tailTrace_4419103
  have hstable : (prefixWord ++ tailWord_4419103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419103).length < 2 ^ (prefixWord ++ tailWord_4419103).sum := by decide
  have hdescent : baseEnd_4419103 < baseStart_4419103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419130 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_4419130 : Nat := 118140960795 + 4419130 * 2 ^ 59
def prefixEnd_4419130 : Nat := 4983230072969 + 3 ^ 40 * 4419130 * 2
def baseEnd_4419130 : Nat := 252126418300377818583533

theorem tailTrace_4419130 : CollatzResearch.WordTrace tailWord_4419130 prefixEnd_4419130 252126418300377818583533 := by
  unfold tailWord_4419130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40294728120063553040549711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107452608320169474774799229 40294728120063553040549711)
  ·
    refine ⟨60442092180095329560824567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40294728120063553040549711 60442092180095329560824567)
    ·
      refine ⟨90663138270142994341236851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60442092180095329560824567 90663138270142994341236851)
      ·
        refine ⟨135994707405214491511855277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90663138270142994341236851 135994707405214491511855277)
        ·
          refine ⟨50998015276955434316945729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135994707405214491511855277 50998015276955434316945729)
          ·
            refine ⟨38248511457716575737709297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50998015276955434316945729 38248511457716575737709297)
            ·
              refine ⟨28686383593287431803281973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38248511457716575737709297 28686383593287431803281973)
              ·
                refine ⟨2689348461870696731557685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28686383593287431803281973 2689348461870696731557685)
                ·
                  refine ⟨252126418300377818583533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2689348461870696731557685 252126418300377818583533)
                  ·
                    rfl

theorem cell23_4419130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_4419130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419130 prefixEnd_4419130 := by exact prefixLift 4419130
  have htrace : WordTrace (prefixWord ++ tailWord_4419130) baseStart_4419130 baseEnd_4419130 := by
    simpa [prefixWord, tailWord_4419130, baseEnd_4419130] using wordTrace_append hprefix tailTrace_4419130
  have hstable : (prefixWord ++ tailWord_4419130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419130).length < 2 ^ (prefixWord ++ tailWord_4419130).sum := by decide
  have hdescent : baseEnd_4419130 < baseStart_4419130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419153 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_4419153 : Nat := 118140960795 + 4419153 * 2 ^ 59
def prefixEnd_4419153 : Nat := 4983230072969 + 3 ^ 40 * 4419153 * 2
def baseEnd_4419153 : Nat := 2269149574758453777264191

theorem tailTrace_4419153 : CollatzResearch.WordTrace tailWord_4419153 prefixEnd_4419153 2269149574758453777264191 := by
  unfold tailWord_4419153
  simp only [CollatzResearch.WordTrace]
  refine ⟨161179751359170887090286113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107453167572780591393524075 161179751359170887090286113)
  ·
    refine ⟨120884813519378165317714585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161179751359170887090286113 120884813519378165317714585)
    ·
      refine ⟨90663610139533623988285939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120884813519378165317714585 90663610139533623988285939)
      ·
        refine ⟨135995415209300435982428909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90663610139533623988285939 135995415209300435982428909)
        ·
          refine ⟨50998280703487663493410841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135995415209300435982428909 50998280703487663493410841)
          ·
            refine ⟨38248710527615747620058131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50998280703487663493410841 38248710527615747620058131)
            ·
              refine ⟨57373065791423621430087197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38248710527615747620058131 57373065791423621430087197)
              ·
                refine ⟨21514899671783858036282699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57373065791423621430087197 21514899671783858036282699)
                ·
                  refine ⟨32272349507675787054424049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21514899671783858036282699 32272349507675787054424049)
                  ·
                    refine ⟨24204262130756840290818037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32272349507675787054424049 24204262130756840290818037)
                    ·
                      refine ⟨2269149574758453777264191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24204262130756840290818037 2269149574758453777264191)
                      ·
                        rfl

theorem cell23_4419153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_4419153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419153 prefixEnd_4419153 := by exact prefixLift 4419153
  have htrace : WordTrace (prefixWord ++ tailWord_4419153) baseStart_4419153 baseEnd_4419153 := by
    simpa [prefixWord, tailWord_4419153, baseEnd_4419153] using wordTrace_append hprefix tailTrace_4419153
  have hstable : (prefixWord ++ tailWord_4419153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419153).length < 2 ^ (prefixWord ++ tailWord_4419153).sum := by decide
  have hdescent : baseEnd_4419153 < baseStart_4419153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419158 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4419158 : Nat := 118140960795 + 4419158 * 2 ^ 59
def prefixEnd_4419158 : Nat := 4983230072969 + 3 ^ 40 * 4419158 * 2
def baseEnd_4419158 : Nat := 2269152142161726257701669

theorem tailTrace_4419158 : CollatzResearch.WordTrace tailWord_4419158 prefixEnd_4419158 2269152142161726257701669 := by
  unfold tailWord_4419158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073745857759548309013633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107453289149435181962812085 10073745857759548309013633)
  ·
    refine ⟨7555309393319661231760225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10073745857759548309013633 7555309393319661231760225)
    ·
      refine ⟨5666482044989745923820169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7555309393319661231760225 5666482044989745923820169)
      ·
        refine ⟨4249861533742309442865127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5666482044989745923820169 4249861533742309442865127)
        ·
          refine ⟨6374792300613464164297691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249861533742309442865127 6374792300613464164297691)
          ·
            refine ⟨9562188450920196246446537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6374792300613464164297691 9562188450920196246446537)
            ·
              refine ⟨7171641338190147184834903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9562188450920196246446537 7171641338190147184834903)
              ·
                refine ⟨10757462007285220777252355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171641338190147184834903 10757462007285220777252355)
                ·
                  refine ⟨16136193010927831165878533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10757462007285220777252355 16136193010927831165878533)
                  ·
                    refine ⟨3025536189548968343602225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16136193010927831165878533 3025536189548968343602225)
                    ·
                      refine ⟨2269152142161726257701669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025536189548968343602225 2269152142161726257701669)
                      ·
                        rfl

theorem cell23_4419158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4419158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419158 prefixEnd_4419158 := by exact prefixLift 4419158
  have htrace : WordTrace (prefixWord ++ tailWord_4419158) baseStart_4419158 baseEnd_4419158 := by
    simpa [prefixWord, tailWord_4419158, baseEnd_4419158] using wordTrace_append hprefix tailTrace_4419158
  have hstable : (prefixWord ++ tailWord_4419158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419158).length < 2 ^ (prefixWord ++ tailWord_4419158).sum := by decide
  have hdescent : baseEnd_4419158 < baseStart_4419158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419180 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_4419180 : Nat := 118140960795 + 4419180 * 2 ^ 59
def prefixEnd_4419180 : Nat := 4983230072969 + 3 ^ 40 * 4419180 * 2
def baseEnd_4419180 : Nat := 2269163438736125171626567

theorem tailTrace_4419180 : CollatzResearch.WordTrace tailWord_4419180 prefixEnd_4419180 2269163438736125171626567 := by
  unfold tailWord_4419180
  simp only [CollatzResearch.WordTrace]
  refine ⟨80590368065036535350759497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107453824086715380467679329 80590368065036535350759497)
  ·
    refine ⟨60442776048777401513069623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80590368065036535350759497 60442776048777401513069623)
    ·
      refine ⟨90664164073166102269604435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60442776048777401513069623 90664164073166102269604435)
      ·
        refine ⟨135996246109749153404406653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90664164073166102269604435 135996246109749153404406653)
        ·
          refine ⟨50998592291155932526652495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135996246109749153404406653 50998592291155932526652495)
          ·
            refine ⟨76497888436733898789978743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50998592291155932526652495 76497888436733898789978743)
            ·
              refine ⟨114746832655100848184968115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76497888436733898789978743 114746832655100848184968115)
              ·
                refine ⟨172120248982651272277452173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114746832655100848184968115 172120248982651272277452173)
                ·
                  refine ⟨64545093368494227104044565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172120248982651272277452173 64545093368494227104044565)
                  ·
                    refine ⟨3025551251648166895502089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64545093368494227104044565 3025551251648166895502089)
                    ·
                      refine ⟨2269163438736125171626567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025551251648166895502089 2269163438736125171626567)
                      ·
                        rfl

theorem cell23_4419180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_4419180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419180 prefixEnd_4419180 := by exact prefixLift 4419180
  have htrace : WordTrace (prefixWord ++ tailWord_4419180) baseStart_4419180 baseEnd_4419180 := by
    simpa [prefixWord, tailWord_4419180, baseEnd_4419180] using wordTrace_append hprefix tailTrace_4419180
  have hstable : (prefixWord ++ tailWord_4419180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419180).length < 2 ^ (prefixWord ++ tailWord_4419180).sum := by decide
  have hdescent : baseEnd_4419180 < baseStart_4419180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419193 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_4419193 : Nat := 118140960795 + 4419193 * 2 ^ 59
def prefixEnd_4419193 : Nat := 4983230072969 + 3 ^ 40 * 4419193 * 2
def baseEnd_4419193 : Nat := 2269170113984633620764007

theorem tailTrace_4419193 : CollatzResearch.WordTrace tailWord_4419193 prefixEnd_4419193 2269170113984633620764007 := by
  unfold tailWord_4419193
  simp only [CollatzResearch.WordTrace]
  refine ⟨161181210279025973921742233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107454140186017315947828155 161181210279025973921742233)
  ·
    refine ⟨120885907709269480441306675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161181210279025973921742233 120885907709269480441306675)
    ·
      refine ⟨181328861563904220661960013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120885907709269480441306675 181328861563904220661960013)
      ·
        refine ⟨67998323086464082748235005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181328861563904220661960013 67998323086464082748235005)
        ·
          refine ⟨25499371157424031030588127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67998323086464082748235005 25499371157424031030588127)
          ·
            refine ⟨38249056736136046545882191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25499371157424031030588127 38249056736136046545882191)
            ·
              refine ⟨57373585104204069818823287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38249056736136046545882191 57373585104204069818823287)
              ·
                refine ⟨86060377656306104728234931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57373585104204069818823287 86060377656306104728234931)
                ·
                  refine ⟨129090566484459157092352397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86060377656306104728234931 129090566484459157092352397)
                  ·
                    refine ⟨48408962431672183909632149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129090566484459157092352397 48408962431672183909632149)
                    ·
                      refine ⟨2269170113984633620764007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48408962431672183909632149 2269170113984633620764007)
                      ·
                        rfl

theorem cell23_4419193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_4419193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419193 prefixEnd_4419193 := by exact prefixLift 4419193
  have htrace : WordTrace (prefixWord ++ tailWord_4419193) baseStart_4419193 baseEnd_4419193 := by
    simpa [prefixWord, tailWord_4419193, baseEnd_4419193] using wordTrace_append hprefix tailTrace_4419193
  have hstable : (prefixWord ++ tailWord_4419193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419193).length < 2 ^ (prefixWord ++ tailWord_4419193).sum := by decide
  have hdescent : baseEnd_4419193 < baseStart_4419193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419197 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_4419197 : Nat := 118140960795 + 4419197 * 2 ^ 59
def prefixEnd_4419197 : Nat := 4983230072969 + 3 ^ 40 * 4419197 * 2
def baseEnd_4419197 : Nat := 2269172167907251605113989

theorem tailTrace_4419197 : CollatzResearch.WordTrace tailWord_4419197 prefixEnd_4419197 2269172167907251605113989 := by
  unfold tailWord_4419197
  simp only [CollatzResearch.WordTrace]
  refine ⟨161181356171011482604887845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107454237447340988403258563 161181356171011482604887845)
  ·
    refine ⟨30221504282064652988416471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161181356171011482604887845 30221504282064652988416471)
    ·
      refine ⟨45332256423096979482624707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30221504282064652988416471 45332256423096979482624707)
      ·
        refine ⟨67998384634645469223937061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45332256423096979482624707 67998384634645469223937061)
        ·
          refine ⟨12749697118996025479488199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67998384634645469223937061 12749697118996025479488199)
          ·
            refine ⟨19124545678494038219232299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12749697118996025479488199 19124545678494038219232299)
            ·
              refine ⟨28686818517741057328848449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19124545678494038219232299 28686818517741057328848449)
              ·
                refine ⟨21515113888305792996636337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28686818517741057328848449 21515113888305792996636337)
                ·
                  refine ⟨16136335416229344747477253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21515113888305792996636337 16136335416229344747477253)
                  ·
                    refine ⟨3025562890543002140151985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16136335416229344747477253 3025562890543002140151985)
                    ·
                      refine ⟨2269172167907251605113989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025562890543002140151985 2269172167907251605113989)
                      ·
                        rfl

theorem cell23_4419197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_4419197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419197 prefixEnd_4419197 := by exact prefixLift 4419197
  have htrace : WordTrace (prefixWord ++ tailWord_4419197) baseStart_4419197 baseEnd_4419197 := by
    simpa [prefixWord, tailWord_4419197, baseEnd_4419197] using wordTrace_append hprefix tailTrace_4419197
  have hstable : (prefixWord ++ tailWord_4419197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419197).length < 2 ^ (prefixWord ++ tailWord_4419197).sum := by decide
  have hdescent : baseEnd_4419197 < baseStart_4419197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419200 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_4419200 : Nat := 118140960795 + 4419200 * 2 ^ 59
def prefixEnd_4419200 : Nat := 4983230072969 + 3 ^ 40 * 4419200 * 2
def baseEnd_4419200 : Nat := 2269173708349215093376475

theorem tailTrace_4419200 : CollatzResearch.WordTrace tailWord_4419200 prefixEnd_4419200 2269173708349215093376475 := by
  unfold tailWord_4419200
  simp only [CollatzResearch.WordTrace]
  refine ⟨80590732795000307058623527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107454310393333742744831369 80590732795000307058623527)
  ·
    refine ⟨120886099192500460587935291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80590732795000307058623527 120886099192500460587935291)
    ·
      refine ⟨181329148788750690881902937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120886099192500460587935291 181329148788750690881902937)
      ·
        refine ⟨135996861591563018161427203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181329148788750690881902937 135996861591563018161427203)
        ·
          refine ⟨203995292387344527242140805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135996861591563018161427203 203995292387344527242140805)
          ·
            refine ⟨38249117322627098857901401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203995292387344527242140805 38249117322627098857901401)
            ·
              refine ⟨28686837991970324143426051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38249117322627098857901401 28686837991970324143426051)
              ·
                refine ⟨43030256987955486215139077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28686837991970324143426051 43030256987955486215139077)
                ·
                  refine ⟨8068173185241653665338577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43030256987955486215139077 8068173185241653665338577)
                  ·
                    refine ⟨6051129888931240249003933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8068173185241653665338577 6051129888931240249003933)
                    ·
                      refine ⟨2269173708349215093376475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6051129888931240249003933 2269173708349215093376475)
                      ·
                        rfl

theorem cell23_4419200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_4419200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419200 prefixEnd_4419200 := by exact prefixLift 4419200
  have htrace : WordTrace (prefixWord ++ tailWord_4419200) baseStart_4419200 baseEnd_4419200 := by
    simpa [prefixWord, tailWord_4419200, baseEnd_4419200] using wordTrace_append hprefix tailTrace_4419200
  have hstable : (prefixWord ++ tailWord_4419200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419200).length < 2 ^ (prefixWord ++ tailWord_4419200).sum := by decide
  have hdescent : baseEnd_4419200 < baseStart_4419200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419207 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 3, 4]
def baseStart_4419207 : Nat := 118140960795 + 4419207 * 2 ^ 59
def prefixEnd_4419207 : Nat := 4983230072969 + 3 ^ 40 * 4419207 * 2
def baseEnd_4419207 : Nat := 756392434237932188662981

theorem tailTrace_4419207 : CollatzResearch.WordTrace tailWord_4419207 prefixEnd_4419207 756392434237932188662981 := by
  unfold tailWord_4419207
  simp only [CollatzResearch.WordTrace]
  refine ⟨161181720900975254312751875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107454480600650169541834583 161181720900975254312751875)
  ·
    refine ⟨241772581351462881469127813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161181720900975254312751875 241772581351462881469127813)
    ·
      refine ⟨45332359003399290275461465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241772581351462881469127813 45332359003399290275461465)
      ·
        refine ⟨33999269252549467706596099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45332359003399290275461465 33999269252549467706596099)
        ·
          refine ⟨50998903878824201559894149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33999269252549467706596099 50998903878824201559894149)
          ·
            refine ⟨9562294477279537792480153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50998903878824201559894149 9562294477279537792480153)
            ·
              refine ⟨7171720857959653344360115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9562294477279537792480153 7171720857959653344360115)
              ·
                refine ⟨10757581286939480016540173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171720857959653344360115 10757581286939480016540173)
                ·
                  refine ⟨4034092982602305006202565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10757581286939480016540173 4034092982602305006202565)
                  ·
                    refine ⟨756392434237932188662981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034092982602305006202565 756392434237932188662981)
                    ·
                      rfl

theorem cell23_4419207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_4419207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419207 prefixEnd_4419207 := by exact prefixLift 4419207
  have htrace : WordTrace (prefixWord ++ tailWord_4419207) baseStart_4419207 baseEnd_4419207 := by
    simpa [prefixWord, tailWord_4419207, baseEnd_4419207] using wordTrace_append hprefix tailTrace_4419207
  have hstable : (prefixWord ++ tailWord_4419207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419207).length < 2 ^ (prefixWord ++ tailWord_4419207).sum := by decide
  have hdescent : baseEnd_4419207 < baseStart_4419207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419257 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4419257 : Nat := 118140960795 + 4419257 * 2 ^ 59
def prefixEnd_4419257 : Nat := 4983230072969 + 3 ^ 40 * 4419257 * 2
def baseEnd_4419257 : Nat := 2269202976746521370363713

theorem tailTrace_4419257 : CollatzResearch.WordTrace tailWord_4419257 prefixEnd_4419257 2269202976746521370363713 := by
  unfold tailWord_4419257
  simp only [CollatzResearch.WordTrace]
  refine ⟨161183544550794112852072025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107455696367196075234714683 161183544550794112852072025)
  ·
    refine ⟨120887658413095584639054019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161183544550794112852072025 120887658413095584639054019)
    ·
      refine ⟨181331487619643376958581029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120887658413095584639054019 181331487619643376958581029)
      ·
        refine ⟨33999653928683133179733943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181331487619643376958581029 33999653928683133179733943)
        ·
          refine ⟨50999480893024699769600915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33999653928683133179733943 50999480893024699769600915)
          ·
            refine ⟨76499221339537049654401373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50999480893024699769600915 76499221339537049654401373)
            ·
              refine ⟨28687208002326393620400515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76499221339537049654401373 28687208002326393620400515)
              ·
                refine ⟨43030812003489590430600773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28687208002326393620400515 43030812003489590430600773)
                ·
                  refine ⟨8068277250654298205737645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43030812003489590430600773 8068277250654298205737645)
                  ·
                    refine ⟨3025603968995361827151617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8068277250654298205737645 3025603968995361827151617)
                    ·
                      refine ⟨2269202976746521370363713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025603968995361827151617 2269202976746521370363713)
                      ·
                        rfl

theorem cell23_4419257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4419257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419257 prefixEnd_4419257 := by exact prefixLift 4419257
  have htrace : WordTrace (prefixWord ++ tailWord_4419257) baseStart_4419257 baseEnd_4419257 := by
    simpa [prefixWord, tailWord_4419257, baseEnd_4419257] using wordTrace_append hprefix tailTrace_4419257
  have hstable : (prefixWord ++ tailWord_4419257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419257).length < 2 ^ (prefixWord ++ tailWord_4419257).sum := by decide
  have hdescent : baseEnd_4419257 < baseStart_4419257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419280 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_4419280 : Nat := 118140960795 + 4419280 * 2 ^ 59
def prefixEnd_4419280 : Nat := 4983230072969 + 3 ^ 40 * 4419280 * 2
def baseEnd_4419280 : Nat := 756404928933858260125369

theorem tailTrace_4419280 : CollatzResearch.WordTrace tailWord_4419280 prefixEnd_4419280 756404928933858260125369 := by
  unfold tailWord_4419280
  simp only [CollatzResearch.WordTrace]
  refine ⟨80592191714855393890079647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107456255619807191853439529 80592191714855393890079647)
  ·
    refine ⟨120888287572283090835119471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80592191714855393890079647 120888287572283090835119471)
    ·
      refine ⟨181332431358424636252679207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120888287572283090835119471 181332431358424636252679207)
      ·
        refine ⟨271998647037636954379018811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181332431358424636252679207 271998647037636954379018811)
        ·
          refine ⟨407997970556455431568528217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271998647037636954379018811 407997970556455431568528217)
          ·
            refine ⟨305998477917341573676396163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407997970556455431568528217 305998477917341573676396163)
            ·
              refine ⟨458997716876012360514594245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305998477917341573676396163 458997716876012360514594245)
              ·
                refine ⟨86062071914252317596486421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458997716876012360514594245 86062071914252317596486421)
                ·
                  refine ⟨4034159620980577387335301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86062071914252317596486421 4034159620980577387335301)
                  ·
                    refine ⟨756404928933858260125369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034159620980577387335301 756404928933858260125369)
                    ·
                      rfl

theorem cell23_4419280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_4419280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419280 prefixEnd_4419280 := by exact prefixLift 4419280
  have htrace : WordTrace (prefixWord ++ tailWord_4419280) baseStart_4419280 baseEnd_4419280 := by
    simpa [prefixWord, tailWord_4419280, baseEnd_4419280] using wordTrace_append hprefix tailTrace_4419280
  have hstable : (prefixWord ++ tailWord_4419280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419280).length < 2 ^ (prefixWord ++ tailWord_4419280).sum := by decide
  have hdescent : baseEnd_4419280 < baseStart_4419280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419284 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_4419284 : Nat := 118140960795 + 4419284 * 2 ^ 59
def prefixEnd_4419284 : Nat := 4983230072969 + 3 ^ 40 * 4419284 * 2
def baseEnd_4419284 : Nat := 756405613574730921575363

theorem tailTrace_4419284 : CollatzResearch.WordTrace tailWord_4419284 prefixEnd_4419284 756405613574730921575363 := by
  unfold tailWord_4419284
  simp only [CollatzResearch.WordTrace]
  refine ⟨80592264660848148231652453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107456352881130864308869937 80592264660848148231652453)
  ·
    refine ⟨15111049623909027793434835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80592264660848148231652453 15111049623909027793434835)
    ·
      refine ⟨22666574435863541690152253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15111049623909027793434835 22666574435863541690152253)
      ·
        refine ⟨8499965413448828133807095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22666574435863541690152253 8499965413448828133807095)
        ·
          refine ⟨12749948120173242200710643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8499965413448828133807095 12749948120173242200710643)
          ·
            refine ⟨19124922180259863301065965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12749948120173242200710643 19124922180259863301065965)
            ·
              refine ⟨7171845817597448737899737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19124922180259863301065965 7171845817597448737899737)
              ·
                refine ⟨5378884363198086553424803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7171845817597448737899737 5378884363198086553424803)
                ·
                  refine ⟨8068326544797129830137205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378884363198086553424803 8068326544797129830137205)
                  ·
                    refine ⟨756405613574730921575363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8068326544797129830137205 756405613574730921575363)
                    ·
                      rfl

theorem cell23_4419284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_4419284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419284 prefixEnd_4419284 := by exact prefixLift 4419284
  have htrace : WordTrace (prefixWord ++ tailWord_4419284) baseStart_4419284 baseEnd_4419284 := by
    simpa [prefixWord, tailWord_4419284, baseEnd_4419284] using wordTrace_append hprefix tailTrace_4419284
  have hstable : (prefixWord ++ tailWord_4419284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419284).length < 2 ^ (prefixWord ++ tailWord_4419284).sum := by decide
  have hdescent : baseEnd_4419284 < baseStart_4419284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419297 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_4419297 : Nat := 118140960795 + 4419297 * 2 ^ 59
def prefixEnd_4419297 : Nat := 4983230072969 + 3 ^ 40 * 4419297 * 2
def baseEnd_4419297 : Nat := 756407838657567071287843

theorem tailTrace_4419297 : CollatzResearch.WordTrace tailWord_4419297 prefixEnd_4419297 756407838657567071287843 := by
  unfold tailWord_4419297
  simp only [CollatzResearch.WordTrace]
  refine ⟨161185003470649199683528145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107456668980432799789018763 161185003470649199683528145)
  ·
    refine ⟨120888752602986899762646109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161185003470649199683528145 120888752602986899762646109)
    ·
      refine ⟨45333282226120087410992291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120888752602986899762646109 45333282226120087410992291)
      ·
        refine ⟨67999923339180131116488437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45333282226120087410992291 67999923339180131116488437)
        ·
          refine ⟨6374992813048137292170791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67999923339180131116488437 6374992813048137292170791)
          ·
            refine ⟨9562489219572205938256187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6374992813048137292170791 9562489219572205938256187)
            ·
              refine ⟨14343733829358308907384281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9562489219572205938256187 14343733829358308907384281)
              ·
                refine ⟨10757800372018731680538211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14343733829358308907384281 10757800372018731680538211)
                ·
                  refine ⟨16136700558028097520807317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10757800372018731680538211 16136700558028097520807317)
                  ·
                    refine ⟨756407838657567071287843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16136700558028097520807317 756407838657567071287843)
                    ·
                      rfl

theorem cell23_4419297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_4419297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419297 prefixEnd_4419297 := by exact prefixLift 4419297
  have htrace : WordTrace (prefixWord ++ tailWord_4419297) baseStart_4419297 baseEnd_4419297 := by
    simpa [prefixWord, tailWord_4419297, baseEnd_4419297] using wordTrace_append hprefix tailTrace_4419297
  have hstable : (prefixWord ++ tailWord_4419297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419297).length < 2 ^ (prefixWord ++ tailWord_4419297).sum := by decide
  have hdescent : baseEnd_4419297 < baseStart_4419297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419307 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 3]
def baseStart_4419307 : Nat := 118140960795 + 4419307 * 2 ^ 59
def prefixEnd_4419307 : Nat := 4983230072969 + 3 ^ 40 * 4419307 * 2
def baseEnd_4419307 : Nat := 2269228650779246174738483

theorem tailTrace_4419307 : CollatzResearch.WordTrace tailWord_4419307 prefixEnd_4419307 2269228650779246174738483 := by
  unfold tailWord_4419307
  simp only [CollatzResearch.WordTrace]
  refine ⟨161185368200612971391392175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107456912133741980927594783 161185368200612971391392175)
  ·
    refine ⟨241778052300919457087088263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161185368200612971391392175 241778052300919457087088263)
    ·
      refine ⟨362667078451379185630632395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241778052300919457087088263 362667078451379185630632395)
      ·
        refine ⟨544000617677068778445948593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362667078451379185630632395 544000617677068778445948593)
        ·
          refine ⟨408000463257801583834461445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544000617677068778445948593 408000463257801583834461445)
          ·
            refine ⟨76500086860837796968961521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 408000463257801583834461445 76500086860837796968961521)
            ·
              refine ⟨57375065145628347726721141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76500086860837796968961521 57375065145628347726721141)
              ·
                refine ⟨5378912357402657599380107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57375065145628347726721141 5378912357402657599380107)
                ·
                  refine ⟨8068368536103986399070161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378912357402657599380107 8068368536103986399070161)
                  ·
                    refine ⟨6051276402077989799302621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8068368536103986399070161 6051276402077989799302621)
                    ·
                      refine ⟨2269228650779246174738483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6051276402077989799302621 2269228650779246174738483)
                      ·
                        rfl

theorem cell23_4419307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 3].length) (baseStart_4419307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419307 prefixEnd_4419307 := by exact prefixLift 4419307
  have htrace : WordTrace (prefixWord ++ tailWord_4419307) baseStart_4419307 baseEnd_4419307 := by
    simpa [prefixWord, tailWord_4419307, baseEnd_4419307] using wordTrace_append hprefix tailTrace_4419307
  have hstable : (prefixWord ++ tailWord_4419307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419307).length < 2 ^ (prefixWord ++ tailWord_4419307).sum := by decide
  have hdescent : baseEnd_4419307 < baseStart_4419307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419314 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_4419314 : Nat := 118140960795 + 4419314 * 2 ^ 59
def prefixEnd_4419314 : Nat := 4983230072969 + 3 ^ 40 * 4419314 * 2
def baseEnd_4419314 : Nat := 756410748381275882450317

theorem tailTrace_4419314 : CollatzResearch.WordTrace tailWord_4419314 prefixEnd_4419314 756410748381275882450317 := by
  unfold tailWord_4419314
  simp only [CollatzResearch.WordTrace]
  refine ⟨40296405877896902896724249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107457082341058407724597997 40296405877896902896724249)
  ·
    refine ⟨30222304408422677172543187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40296405877896902896724249 30222304408422677172543187)
    ·
      refine ⟨45333456612634015758814781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30222304408422677172543187 45333456612634015758814781)
      ·
        refine ⟨17000046229737755909555543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45333456612634015758814781 17000046229737755909555543)
        ·
          refine ⟨25500069344606633864333315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17000046229737755909555543 25500069344606633864333315)
          ·
            refine ⟨38250104016909950796499973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25500069344606633864333315 38250104016909950796499973)
            ·
              refine ⟨7171894503170615774343745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38250104016909950796499973 7171894503170615774343745)
              ·
                refine ⟨5378920877377961830757809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7171894503170615774343745 5378920877377961830757809)
                ·
                  refine ⟨4034190658033471373068357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5378920877377961830757809 4034190658033471373068357)
                  ·
                    refine ⟨756410748381275882450317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034190658033471373068357 756410748381275882450317)
                    ·
                      rfl

theorem cell23_4419314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_4419314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419314 prefixEnd_4419314 := by exact prefixLift 4419314
  have htrace : WordTrace (prefixWord ++ tailWord_4419314) baseStart_4419314 baseEnd_4419314 := by
    simpa [prefixWord, tailWord_4419314, baseEnd_4419314] using wordTrace_append hprefix tailTrace_4419314
  have hstable : (prefixWord ++ tailWord_4419314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419314).length < 2 ^ (prefixWord ++ tailWord_4419314).sum := by decide
  have hdescent : baseEnd_4419314 < baseStart_4419314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419337 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 3]
def baseStart_4419337 : Nat := 118140960795 + 4419337 * 2 ^ 59
def prefixEnd_4419337 : Nat := 4983230072969 + 3 ^ 40 * 4419337 * 2
def baseEnd_4419337 : Nat := 2269244055198881057363345

theorem tailTrace_4419337 : CollatzResearch.WordTrace tailWord_4419337 prefixEnd_4419337 2269244055198881057363345 := by
  unfold tailWord_4419337
  simp only [CollatzResearch.WordTrace]
  refine ⟨161186462390504286514984265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107457641593669524343322843 161186462390504286514984265)
  ·
    refine ⟨120889846792878214886238199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161186462390504286514984265 120889846792878214886238199)
    ·
      refine ⟨181334770189317322329357299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120889846792878214886238199 181334770189317322329357299)
      ·
        refine ⟨272002155283975983494035949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181334770189317322329357299 272002155283975983494035949)
        ·
          refine ⟨102000808231490993810263481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272002155283975983494035949 102000808231490993810263481)
          ·
            refine ⟨76500606173618245357697611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102000808231490993810263481 76500606173618245357697611)
            ·
              refine ⟨114750909260427368036546417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76500606173618245357697611 114750909260427368036546417)
              ·
                refine ⟨86063181945320526027409813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114750909260427368036546417 86063181945320526027409813)
                ·
                  refine ⟨4034211653686899657534835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86063181945320526027409813 4034211653686899657534835)
                  ·
                    refine ⟨6051317480530349486302253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4034211653686899657534835 6051317480530349486302253)
                    ·
                      refine ⟨2269244055198881057363345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6051317480530349486302253 2269244055198881057363345)
                      ·
                        rfl

theorem cell23_4419337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_4419337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419337 prefixEnd_4419337 := by exact prefixLift 4419337
  have htrace : WordTrace (prefixWord ++ tailWord_4419337) baseStart_4419337 baseEnd_4419337 := by
    simpa [prefixWord, tailWord_4419337, baseEnd_4419337] using wordTrace_append hprefix tailTrace_4419337
  have hstable : (prefixWord ++ tailWord_4419337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419337).length < 2 ^ (prefixWord ++ tailWord_4419337).sum := by decide
  have hdescent : baseEnd_4419337 < baseStart_4419337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419474 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4419474 : Nat := 118140960795 + 4419474 * 2 ^ 59
def prefixEnd_4419474 : Nat := 4983230072969 + 3 ^ 40 * 4419474 * 2
def baseEnd_4419474 : Nat := 2269314402048547021350215

theorem tailTrace_4419474 : CollatzResearch.WordTrace tailWord_4419474 prefixEnd_4419474 2269314402048547021350215 := by
  unfold tailWord_4419474
  simp only [CollatzResearch.WordTrace]
  refine ⟨40297864797751989728180369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107460972794005305941814317 40297864797751989728180369)
  ·
    refine ⟨30223398598313992296135277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40297864797751989728180369 30223398598313992296135277)
    ·
      refine ⟨11333774474367747111050729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30223398598313992296135277 11333774474367747111050729)
      ·
        refine ⟨8500330855775810333288047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11333774474367747111050729 8500330855775810333288047)
        ·
          refine ⟨12750496283663715499932071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8500330855775810333288047 12750496283663715499932071)
          ·
            refine ⟨19125744425495573249898107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12750496283663715499932071 19125744425495573249898107)
            ·
              refine ⟨28688616638243359874847161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19125744425495573249898107 28688616638243359874847161)
              ·
                refine ⟨21516462478682519906135371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28688616638243359874847161 21516462478682519906135371)
                ·
                  refine ⟨32274693718023779859203057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21516462478682519906135371 32274693718023779859203057)
                  ·
                    refine ⟨24206020288517834894402293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32274693718023779859203057 24206020288517834894402293)
                    ·
                      refine ⟨2269314402048547021350215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24206020288517834894402293 2269314402048547021350215)
                      ·
                        rfl

theorem cell23_4419474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4419474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419474 prefixEnd_4419474 := by exact prefixLift 4419474
  have htrace : WordTrace (prefixWord ++ tailWord_4419474) baseStart_4419474 baseEnd_4419474 := by
    simpa [prefixWord, tailWord_4419474, baseEnd_4419474] using wordTrace_append hprefix tailTrace_4419474
  have hstable : (prefixWord ++ tailWord_4419474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419474).length < 2 ^ (prefixWord ++ tailWord_4419474).sum := by decide
  have hdescent : baseEnd_4419474 < baseStart_4419474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419507 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 6]
def baseStart_4419507 : Nat := 118140960795 + 4419507 * 2 ^ 59
def prefixEnd_4419507 : Nat := 4983230072969 + 3 ^ 40 * 4419507 * 2
def baseEnd_4419507 : Nat := 252147927434460599137507

theorem tailTrace_4419507 : CollatzResearch.WordTrace tailWord_4419507 prefixEnd_4419507 252147927434460599137507 := by
  unfold tailWord_4419507
  simp only [CollatzResearch.WordTrace]
  refine ⟨161192662799888405548672775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107461775199925603699115183 161192662799888405548672775)
  ·
    refine ⟨241788994199832608323009163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161192662799888405548672775 241788994199832608323009163)
    ·
      refine ⟨362683491299748912484513745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241788994199832608323009163 362683491299748912484513745)
      ·
        refine ⟨272012618474811684363385309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362683491299748912484513745 272012618474811684363385309)
        ·
          refine ⟨102004731928054381636269491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272012618474811684363385309 102004731928054381636269491)
          ·
            refine ⟨153007097892081572454404237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102004731928054381636269491 153007097892081572454404237)
            ·
              refine ⟨57377661709530589670401589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153007097892081572454404237 57377661709530589670401589)
              ·
                refine ⟨5379155785268492781600149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57377661709530589670401589 5379155785268492781600149)
                ·
                  refine ⟨252147927434460599137507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5379155785268492781600149 252147927434460599137507)
                  ·
                    rfl

theorem cell23_4419507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 6].length) (baseStart_4419507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419507 prefixEnd_4419507 := by exact prefixLift 4419507
  have htrace : WordTrace (prefixWord ++ tailWord_4419507) baseStart_4419507 baseEnd_4419507 := by
    simpa [prefixWord, tailWord_4419507, baseEnd_4419507] using wordTrace_append hprefix tailTrace_4419507
  have hstable : (prefixWord ++ tailWord_4419507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419507).length < 2 ^ (prefixWord ++ tailWord_4419507).sum := by decide
  have hdescent : baseEnd_4419507 < baseStart_4419507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419528 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 1, 4]
def baseStart_4419528 : Nat := 118140960795 + 4419528 * 2 ^ 59
def prefixEnd_4419528 : Nat := 4983230072969 + 3 ^ 40 * 4419528 * 2
def baseEnd_4419528 : Nat := 756447376667963270024989

theorem tailTrace_4419528 : CollatzResearch.WordTrace tailWord_4419528 prefixEnd_4419528 756447376667963270024989 := by
  unfold tailWord_4419528
  simp only [CollatzResearch.WordTrace]
  refine ⟨80596714366406163067593619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107462285821874884090124825 80596714366406163067593619)
  ·
    refine ⟨120895071549609244601390429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80596714366406163067593619 120895071549609244601390429)
    ·
      refine ⟨45335651831103466725521411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120895071549609244601390429 45335651831103466725521411)
      ·
        refine ⟨68003477746655200088282117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45335651831103466725521411 68003477746655200088282117)
        ·
          refine ⟨12750652077497850016552897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68003477746655200088282117 12750652077497850016552897)
          ·
            refine ⟨9562989058123387512414673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12750652077497850016552897 9562989058123387512414673)
            ·
              refine ⟨7172241793592540634311005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9562989058123387512414673 7172241793592540634311005)
              ·
                refine ⟨2689590672597202737866627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7172241793592540634311005 2689590672597202737866627)
                ·
                  refine ⟨4034386008895804106799941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689590672597202737866627 4034386008895804106799941)
                  ·
                    refine ⟨756447376667963270024989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034386008895804106799941 756447376667963270024989)
                    ·
                      rfl

theorem cell23_4419528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_4419528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419528 prefixEnd_4419528 := by exact prefixLift 4419528
  have htrace : WordTrace (prefixWord ++ tailWord_4419528) baseStart_4419528 baseEnd_4419528 := by
    simpa [prefixWord, tailWord_4419528, baseEnd_4419528] using wordTrace_append hprefix tailTrace_4419528
  have hstable : (prefixWord ++ tailWord_4419528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419528).length < 2 ^ (prefixWord ++ tailWord_4419528).sum := by decide
  have hdescent : baseEnd_4419528 < baseStart_4419528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419537 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_4419537 : Nat := 118140960795 + 4419537 * 2 ^ 59
def prefixEnd_4419537 : Nat := 4983230072969 + 3 ^ 40 * 4419537 * 2
def baseEnd_4419537 : Nat := 756448917109926758287475

theorem tailTrace_4419537 : CollatzResearch.WordTrace tailWord_4419537 prefixEnd_4419537 756448917109926758287475 := by
  unfold tailWord_4419537
  simp only [CollatzResearch.WordTrace]
  refine ⟨161193756989779720672264865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107462504659853147114843243 161193756989779720672264865)
  ·
    refine ⟨120895317742334790504198649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161193756989779720672264865 120895317742334790504198649)
    ·
      refine ⟨90671488306751092878148987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120895317742334790504198649 90671488306751092878148987)
      ·
        refine ⟨136007232460126639317223481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90671488306751092878148987 136007232460126639317223481)
        ·
          refine ⟨102005424345094979487917611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136007232460126639317223481 102005424345094979487917611)
          ·
            refine ⟨153008136517642469231876417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102005424345094979487917611 153008136517642469231876417)
            ·
              refine ⟨114756102388231851923907313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153008136517642469231876417 114756102388231851923907313)
              ·
                refine ⟨86067076791173888942930485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114756102388231851923907313 86067076791173888942930485)
                ·
                  refine ⟨8068788449172552088399733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86067076791173888942930485 8068788449172552088399733)
                  ·
                    refine ⟨756448917109926758287475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8068788449172552088399733 756448917109926758287475)
                    ·
                      rfl

theorem cell23_4419537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_4419537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419537 prefixEnd_4419537 := by exact prefixLift 4419537
  have htrace : WordTrace (prefixWord ++ tailWord_4419537) baseStart_4419537 baseEnd_4419537 := by
    simpa [prefixWord, tailWord_4419537, baseEnd_4419537] using wordTrace_append hprefix tailTrace_4419537
  have hstable : (prefixWord ++ tailWord_4419537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419537).length < 2 ^ (prefixWord ++ tailWord_4419537).sum := by decide
  have hdescent : baseEnd_4419537 < baseStart_4419537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419541 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 6]
def baseStart_4419541 : Nat := 118140960795 + 4419541 * 2 ^ 59
def prefixEnd_4419541 : Nat := 4983230072969 + 3 ^ 40 * 4419541 * 2
def baseEnd_4419541 : Nat := 252149867250266473245823

theorem tailTrace_4419541 : CollatzResearch.WordTrace tailWord_4419541 prefixEnd_4419541 252149867250266473245823 := by
  unfold tailWord_4419541
  simp only [CollatzResearch.WordTrace]
  refine ⟨161193902881765229355410477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107462601921176819570273651 161193902881765229355410477)
  ·
    refine ⟨60447713580661961008278929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161193902881765229355410477 60447713580661961008278929)
    ·
      refine ⟨45335785185496470756209197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60447713580661961008278929 45335785185496470756209197)
      ·
        refine ⟨17000919444561176533578449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45335785185496470756209197 17000919444561176533578449)
        ·
          refine ⟨12750689583420882400183837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17000919444561176533578449 12750689583420882400183837)
          ·
            refine ⟨4781508593782830900068939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12750689583420882400183837 4781508593782830900068939)
            ·
              refine ⟨7172262890674246350103409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781508593782830900068939 7172262890674246350103409)
              ·
                refine ⟨5379197168005684762577557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7172262890674246350103409 5379197168005684762577557)
                ·
                  refine ⟨252149867250266473245823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5379197168005684762577557 252149867250266473245823)
                  ·
                    rfl

theorem cell23_4419541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_4419541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419541 prefixEnd_4419541 := by exact prefixLift 4419541
  have htrace : WordTrace (prefixWord ++ tailWord_4419541) baseStart_4419541 baseEnd_4419541 := by
    simpa [prefixWord, tailWord_4419541, baseEnd_4419541] using wordTrace_append hprefix tailTrace_4419541
  have hstable : (prefixWord ++ tailWord_4419541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419541).length < 2 ^ (prefixWord ++ tailWord_4419541).sum := by decide
  have hdescent : baseEnd_4419541 < baseStart_4419541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419551 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 3]
def baseStart_4419551 : Nat := 118140960795 + 4419551 * 2 ^ 59
def prefixEnd_4419551 : Nat := 4983230072969 + 3 ^ 40 * 4419551 * 2
def baseEnd_4419551 : Nat := 2269353940058943220087361

theorem tailTrace_4419551 : CollatzResearch.WordTrace tailWord_4419551 prefixEnd_4419551 2269353940058943220087361 := by
  unfold tailWord_4419551
  simp only [CollatzResearch.WordTrace]
  refine ⟨161194267611729001063274507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107462845074486000708849671 161194267611729001063274507)
  ·
    refine ⟨241791401417593501594911761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161194267611729001063274507 241791401417593501594911761)
    ·
      refine ⟨181343551063195126196183821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241791401417593501594911761 181343551063195126196183821)
      ·
        refine ⟨68003831648698172323568933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181343551063195126196183821 68003831648698172323568933)
        ·
          refine ⟨12750718434130907310669175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68003831648698172323568933 12750718434130907310669175)
          ·
            refine ⟨19126077651196360966003763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12750718434130907310669175 19126077651196360966003763)
            ·
              refine ⟨28689116476794541449005645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19126077651196360966003763 28689116476794541449005645)
              ·
                refine ⟨10758418678797953043377117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28689116476794541449005645 10758418678797953043377117)
                ·
                  refine ⟨4034407004549232391266419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10758418678797953043377117 4034407004549232391266419)
                  ·
                    refine ⟨6051610506823848586899629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4034407004549232391266419 6051610506823848586899629)
                    ·
                      refine ⟨2269353940058943220087361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6051610506823848586899629 2269353940058943220087361)
                      ·
                        rfl

theorem cell23_4419551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_4419551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419551 prefixEnd_4419551 := by exact prefixLift 4419551
  have htrace : WordTrace (prefixWord ++ tailWord_4419551) baseStart_4419551 baseEnd_4419551 := by
    simpa [prefixWord, tailWord_4419551, baseEnd_4419551] using wordTrace_append hprefix tailTrace_4419551
  have hstable : (prefixWord ++ tailWord_4419551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419551).length < 2 ^ (prefixWord ++ tailWord_4419551).sum := by decide
  have hdescent : baseEnd_4419551 < baseStart_4419551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419591 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4419591 : Nat := 118140960795 + 4419591 * 2 ^ 59
def prefixEnd_4419591 : Nat := 4983230072969 + 3 ^ 40 * 4419591 * 2
def baseEnd_4419591 : Nat := 2269374479285123063587177

theorem tailTrace_4419591 : CollatzResearch.WordTrace tailWord_4419591 prefixEnd_4419591 2269374479285123063587177 := by
  unfold tailWord_4419591
  simp only [CollatzResearch.WordTrace]
  refine ⟨161195726531584087894730627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107463817687722725263153751 161195726531584087894730627)
  ·
    refine ⟨241793589797376131842095941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161195726531584087894730627 241793589797376131842095941)
    ·
      refine ⟨45336298087008024720392989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241793589797376131842095941 45336298087008024720392989)
      ·
        refine ⟨17001111782628009270147371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45336298087008024720392989 17001111782628009270147371)
        ·
          refine ⟨25501667673942013905221057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17001111782628009270147371 25501667673942013905221057)
          ·
            refine ⟨19126250755456510428915793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25501667673942013905221057 19126250755456510428915793)
            ·
              refine ⟨14344688066592382821686845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19126250755456510428915793 14344688066592382821686845)
              ·
                refine ⟨5379258024972143558132567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14344688066592382821686845 5379258024972143558132567)
                ·
                  refine ⟨8068887037458215337198851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379258024972143558132567 8068887037458215337198851)
                  ·
                    refine ⟨12103330556187323005798277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8068887037458215337198851 12103330556187323005798277)
                    ·
                      refine ⟨2269374479285123063587177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12103330556187323005798277 2269374479285123063587177)
                      ·
                        rfl

theorem cell23_4419591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4419591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419591 prefixEnd_4419591 := by exact prefixLift 4419591
  have htrace : WordTrace (prefixWord ++ tailWord_4419591) baseStart_4419591 baseEnd_4419591 := by
    simpa [prefixWord, tailWord_4419591, baseEnd_4419591] using wordTrace_append hprefix tailTrace_4419591
  have hstable : (prefixWord ++ tailWord_4419591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419591).length < 2 ^ (prefixWord ++ tailWord_4419591).sum := by decide
  have hdescent : baseEnd_4419591 < baseStart_4419591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419627 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 7]
def baseStart_4419627 : Nat := 118140960795 + 4419627 * 2 ^ 59
def prefixEnd_4419627 : Nat := 4983230072969 + 3 ^ 40 * 4419627 * 2
def baseEnd_4419627 : Nat := 756464321529561640912337

theorem tailTrace_4419627 : CollatzResearch.WordTrace tailWord_4419627 prefixEnd_4419627 756464321529561640912337 := by
  unfold tailWord_4419627
  simp only [CollatzResearch.WordTrace]
  refine ⟨161197039559453666043041135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107464693039635777362027423 161197039559453666043041135)
  ·
    refine ⟨241795559339180499064561703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161197039559453666043041135 241795559339180499064561703)
    ·
      refine ⟨362693339008770748596842555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241795559339180499064561703 362693339008770748596842555)
      ·
        refine ⟨544040008513156122895263833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362693339008770748596842555 544040008513156122895263833)
        ·
          refine ⟨408030006384867092171447875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544040008513156122895263833 408030006384867092171447875)
          ·
            refine ⟨612045009577300638257171813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408030006384867092171447875 612045009577300638257171813)
            ·
              refine ⟨114758439295743869673219715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 612045009577300638257171813 114758439295743869673219715)
              ·
                refine ⟨172137658943615804509829573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114758439295743869673219715 172137658943615804509829573)
                ·
                  refine ⟨32275811051927963345593045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172137658943615804509829573 32275811051927963345593045)
                  ·
                    refine ⟨756464321529561640912337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32275811051927963345593045 756464321529561640912337)
                    ·
                      rfl

theorem cell23_4419627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_4419627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419627 prefixEnd_4419627 := by exact prefixLift 4419627
  have htrace : WordTrace (prefixWord ++ tailWord_4419627) baseStart_4419627 baseEnd_4419627 := by
    simpa [prefixWord, tailWord_4419627, baseEnd_4419627] using wordTrace_append hprefix tailTrace_4419627
  have hstable : (prefixWord ++ tailWord_4419627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419627).length < 2 ^ (prefixWord ++ tailWord_4419627).sum := by decide
  have hdescent : baseEnd_4419627 < baseStart_4419627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419674 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_4419674 : Nat := 118140960795 + 4419674 * 2 ^ 59
def prefixEnd_4419674 : Nat := 4983230072969 + 3 ^ 40 * 4419674 * 2
def baseEnd_4419674 : Nat := 756472366059815412949765

theorem tailTrace_4419674 : CollatzResearch.WordTrace tailWord_4419674 prefixEnd_4419674 756472366059815412949765 := by
  unfold tailWord_4419674
  simp only [CollatzResearch.WordTrace]
  refine ⟨40299688447570848267500519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107465835860188928713334717 40299688447570848267500519)
  ·
    refine ⟨60449532671356272401250779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40299688447570848267500519 60449532671356272401250779)
    ·
      refine ⟨90674299007034408601876169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60449532671356272401250779 90674299007034408601876169)
      ·
        refine ⟨68005724255275806451407127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90674299007034408601876169 68005724255275806451407127)
        ·
          refine ⟨102008586382913709677110691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68005724255275806451407127 102008586382913709677110691)
          ·
            refine ⟨153012879574370564515666037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102008586382913709677110691 153012879574370564515666037)
            ·
              refine ⟨14344957460097240423343691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153012879574370564515666037 14344957460097240423343691)
              ·
                refine ⟨21517436190145860635015537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14344957460097240423343691 21517436190145860635015537)
                ·
                  refine ⟨16138077142609395476261653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21517436190145860635015537 16138077142609395476261653)
                  ·
                    refine ⟨756472366059815412949765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16138077142609395476261653 756472366059815412949765)
                    ·
                      rfl

theorem cell23_4419674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_4419674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419674 prefixEnd_4419674 := by exact prefixLift 4419674
  have htrace : WordTrace (prefixWord ++ tailWord_4419674) baseStart_4419674 baseEnd_4419674 := by
    simpa [prefixWord, tailWord_4419674, baseEnd_4419674] using wordTrace_append hprefix tailTrace_4419674
  have hstable : (prefixWord ++ tailWord_4419674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419674).length < 2 ^ (prefixWord ++ tailWord_4419674).sum := by decide
  have hdescent : baseEnd_4419674 < baseStart_4419674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419684 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_4419684 : Nat := 118140960795 + 4419684 * 2 ^ 59
def prefixEnd_4419684 : Nat := 4983230072969 + 3 ^ 40 * 4419684 * 2
def baseEnd_4419684 : Nat := 2269422232985991199724249

theorem tailTrace_4419684 : CollatzResearch.WordTrace tailWord_4419684 prefixEnd_4419684 2269422232985991199724249 := by
  unfold tailWord_4419684
  simp only [CollatzResearch.WordTrace]
  refine ⟨80599559260123582388933053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107466079013498109851910737 80599559260123582388933053)
  ·
    refine ⟨30224834722546343395849895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80599559260123582388933053 30224834722546343395849895)
    ·
      refine ⟨45337252083819515093774843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30224834722546343395849895 45337252083819515093774843)
      ·
        refine ⟨68005878125729272640662265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45337252083819515093774843 68005878125729272640662265)
        ·
          refine ⟨51004408594296954480496699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68005878125729272640662265 51004408594296954480496699)
          ·
            refine ⟨76506612891445431720745049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51004408594296954480496699 76506612891445431720745049)
            ·
              refine ⟨57379959668584073790558787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76506612891445431720745049 57379959668584073790558787)
              ·
                refine ⟨86069939502876110685838181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57379959668584073790558787 86069939502876110685838181)
                ·
                  refine ⟨16138113656789270753594659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86069939502876110685838181 16138113656789270753594659)
                  ·
                    refine ⟨24207170485183906130391989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16138113656789270753594659 24207170485183906130391989)
                    ·
                      refine ⟨2269422232985991199724249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24207170485183906130391989 2269422232985991199724249)
                      ·
                        rfl

theorem cell23_4419684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_4419684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419684 prefixEnd_4419684 := by exact prefixLift 4419684
  have htrace : WordTrace (prefixWord ++ tailWord_4419684) baseStart_4419684 baseEnd_4419684 := by
    simpa [prefixWord, tailWord_4419684, baseEnd_4419684] using wordTrace_append hprefix tailTrace_4419684
  have hstable : (prefixWord ++ tailWord_4419684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419684).length < 2 ^ (prefixWord ++ tailWord_4419684).sum := by decide
  have hdescent : baseEnd_4419684 < baseStart_4419684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419698 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_4419698 : Nat := 118140960795 + 4419698 * 2 ^ 59
def prefixEnd_4419698 : Nat := 4983230072969 + 3 ^ 40 * 4419698 * 2
def baseEnd_4419698 : Nat := 2269429421715154144949185

theorem tailTrace_4419698 : CollatzResearch.WordTrace tailWord_4419698 prefixEnd_4419698 2269429421715154144949185 := by
  unfold tailWord_4419698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40299907285549111292218937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107466419428130963445917165 40299907285549111292218937)
  ·
    refine ⟨30224930464161833469164203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40299907285549111292218937 30224930464161833469164203)
    ·
      refine ⟨45337395696242750203746305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30224930464161833469164203 45337395696242750203746305)
      ·
        refine ⟨34003046772182062652809729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45337395696242750203746305 34003046772182062652809729)
        ·
          refine ⟨25502285079136546989607297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34003046772182062652809729 25502285079136546989607297)
          ·
            refine ⟨19126713809352410242205473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25502285079136546989607297 19126713809352410242205473)
            ·
              refine ⟨14345035357014307681654105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19126713809352410242205473 14345035357014307681654105)
              ·
                refine ⟨10758776517760730761240579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14345035357014307681654105 10758776517760730761240579)
                ·
                  refine ⟨16138164776641096141860869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10758776517760730761240579 16138164776641096141860869)
                  ·
                    refine ⟨3025905895620205526598913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16138164776641096141860869 3025905895620205526598913)
                    ·
                      refine ⟨2269429421715154144949185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025905895620205526598913 2269429421715154144949185)
                      ·
                        rfl

theorem cell23_4419698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_4419698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419698 prefixEnd_4419698 := by exact prefixLift 4419698
  have htrace : WordTrace (prefixWord ++ tailWord_4419698) baseStart_4419698 baseEnd_4419698 := by
    simpa [prefixWord, tailWord_4419698, baseEnd_4419698] using wordTrace_append hprefix tailTrace_4419698
  have hstable : (prefixWord ++ tailWord_4419698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419698).length < 2 ^ (prefixWord ++ tailWord_4419698).sum := by decide
  have hdescent : baseEnd_4419698 < baseStart_4419698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419702 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4419702 : Nat := 118140960795 + 4419702 * 2 ^ 59
def prefixEnd_4419702 : Nat := 4983230072969 + 3 ^ 40 * 4419702 * 2
def baseEnd_4419702 : Nat := 2269431475637772129299167

theorem tailTrace_4419702 : CollatzResearch.WordTrace tailWord_4419702 prefixEnd_4419702 2269431475637772129299167 := by
  unfold tailWord_4419702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10074985939636372115751335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107466516689454635901347573 10074985939636372115751335)
  ·
    refine ⟨15112478909454558173627003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10074985939636372115751335 15112478909454558173627003)
    ·
      refine ⟨22668718364181837260440505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15112478909454558173627003 22668718364181837260440505)
      ·
        refine ⟨17001538773136377945330379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22668718364181837260440505 17001538773136377945330379)
        ·
          refine ⟨25502308159704566917995569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17001538773136377945330379 25502308159704566917995569)
          ·
            refine ⟨19126731119778425188496677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25502308159704566917995569 19126731119778425188496677)
            ·
              refine ⟨3586262084958454722843127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19126731119778425188496677 3586262084958454722843127)
              ·
                refine ⟨5379393127437682084264691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586262084958454722843127 5379393127437682084264691)
                ·
                  refine ⟨8069089691156523126397037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379393127437682084264691 8069089691156523126397037)
                  ·
                    refine ⟨3025908634183696172398889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8069089691156523126397037 3025908634183696172398889)
                    ·
                      refine ⟨2269431475637772129299167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025908634183696172398889 2269431475637772129299167)
                      ·
                        rfl

theorem cell23_4419702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4419702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419702 prefixEnd_4419702 := by exact prefixLift 4419702
  have htrace : WordTrace (prefixWord ++ tailWord_4419702) baseStart_4419702 baseEnd_4419702 := by
    simpa [prefixWord, tailWord_4419702, baseEnd_4419702] using wordTrace_append hprefix tailTrace_4419702
  have hstable : (prefixWord ++ tailWord_4419702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419702).length < 2 ^ (prefixWord ++ tailWord_4419702).sum := by decide
  have hdescent : baseEnd_4419702 < baseStart_4419702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419715 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 2, 2, 2]
def baseStart_4419715 : Nat := 118140960795 + 4419715 * 2 ^ 59
def prefixEnd_4419715 : Nat := 4983230072969 + 3 ^ 40 * 4419715 * 2
def baseEnd_4419715 : Nat := 2269438150886280578436607

theorem tailTrace_4419715 : CollatzResearch.WordTrace tailWord_4419715 prefixEnd_4419715 2269438150886280578436607 := by
  unfold tailWord_4419715
  simp only [CollatzResearch.WordTrace]
  refine ⟨161200249183134857072244599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107466832788756571381496399 161200249183134857072244599)
  ·
    refine ⟨241800373774702285608366899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161200249183134857072244599 241800373774702285608366899)
    ·
      refine ⟨362700560662053428412550349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241800373774702285608366899 362700560662053428412550349)
      ·
        refine ⟨136012710248270035654706381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362700560662053428412550349 136012710248270035654706381)
        ·
          refine ⟨51004766343101263370514893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136012710248270035654706381 51004766343101263370514893)
          ·
            refine ⟨19126787378662973763943085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51004766343101263370514893 19126787378662973763943085)
            ·
              refine ⟨7172545266998615161478657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19126787378662973763943085 7172545266998615161478657)
              ·
                refine ⟨5379408950248961371108993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7172545266998615161478657 5379408950248961371108993)
                ·
                  refine ⟨4034556712686721028331745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5379408950248961371108993 4034556712686721028331745)
                  ·
                    refine ⟨3025917534515040771248809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4034556712686721028331745 3025917534515040771248809)
                    ·
                      refine ⟨2269438150886280578436607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3025917534515040771248809 2269438150886280578436607)
                      ·
                        rfl

theorem cell23_4419715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_4419715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419715 prefixEnd_4419715 := by exact prefixLift 4419715
  have htrace : WordTrace (prefixWord ++ tailWord_4419715) baseStart_4419715 baseEnd_4419715 := by
    simpa [prefixWord, tailWord_4419715, baseEnd_4419715] using wordTrace_append hprefix tailTrace_4419715
  have hstable : (prefixWord ++ tailWord_4419715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419715).length < 2 ^ (prefixWord ++ tailWord_4419715).sum := by decide
  have hdescent : baseEnd_4419715 < baseStart_4419715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419721 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 5]
def baseStart_4419721 : Nat := 118140960795 + 4419721 * 2 ^ 59
def prefixEnd_4419721 : Nat := 4983230072969 + 3 ^ 40 * 4419721 * 2
def baseEnd_4419721 : Nat := 252160136863356394995731

theorem tailTrace_4419721 : CollatzResearch.WordTrace tailWord_4419721 prefixEnd_4419721 252160136863356394995731 := by
  unfold tailWord_4419721
  simp only [CollatzResearch.WordTrace]
  refine ⟨161200468021113120096963017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107466978680742080064642011 161200468021113120096963017)
  ·
    refine ⟨120900351015834840072722263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161200468021113120096963017 120900351015834840072722263)
    ·
      refine ⟨181350526523752260109083395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120900351015834840072722263 181350526523752260109083395)
      ·
        refine ⟨272025789785628390163625093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181350526523752260109083395 272025789785628390163625093)
        ·
          refine ⟨51004835584805323155679705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272025789785628390163625093 51004835584805323155679705)
          ·
            refine ⟨38253626688603992366759779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51004835584805323155679705 38253626688603992366759779)
            ·
              refine ⟨57380440032905988550139669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38253626688603992366759779 57380440032905988550139669)
              ·
                refine ⟨2689708126542468213287797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57380440032905988550139669 2689708126542468213287797)
                ·
                  refine ⟨252160136863356394995731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2689708126542468213287797 252160136863356394995731)
                  ·
                    rfl

theorem cell23_4419721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 5].length) (baseStart_4419721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419721 prefixEnd_4419721 := by exact prefixLift 4419721
  have htrace : WordTrace (prefixWord ++ tailWord_4419721) baseStart_4419721 baseEnd_4419721 := by
    simpa [prefixWord, tailWord_4419721, baseEnd_4419721] using wordTrace_append hprefix tailTrace_4419721
  have hstable : (prefixWord ++ tailWord_4419721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419721).length < 2 ^ (prefixWord ++ tailWord_4419721).sum := by decide
  have hdescent : baseEnd_4419721 < baseStart_4419721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419771 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4]
def baseStart_4419771 : Nat := 118140960795 + 4419771 * 2 ^ 59
def prefixEnd_4419771 : Nat := 4983230072969 + 3 ^ 40 * 4419771 * 2
def baseEnd_4419771 : Nat := 2269466905802932359336349

theorem tailTrace_4419771 : CollatzResearch.WordTrace tailWord_4419771 prefixEnd_4419771 2269466905802932359336349 := by
  unfold tailWord_4419771
  simp only [CollatzResearch.WordTrace]
  refine ⟨161202291670931978636283167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107468194447287985757522111 161202291670931978636283167)
  ·
    refine ⟨241803437506397967954424751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161202291670931978636283167 241803437506397967954424751)
    ·
      refine ⟨362705156259596951931637127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241803437506397967954424751 362705156259596951931637127)
      ·
        refine ⟨544057734389395427897455691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362705156259596951931637127 544057734389395427897455691)
        ·
          refine ⟨816086601584093141846183537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544057734389395427897455691 816086601584093141846183537)
          ·
            refine ⟨612064951188069856384637653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816086601584093141846183537 612064951188069856384637653)
            ·
              refine ⟨14345272293470387259014945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 612064951188069856384637653 14345272293470387259014945)
              ·
                refine ⟨10758954220102790444261209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14345272293470387259014945 10758954220102790444261209)
                ·
                  refine ⟨8069215665077092833195907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10758954220102790444261209 8069215665077092833195907)
                  ·
                    refine ⟨12103823497615639249793861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8069215665077092833195907 12103823497615639249793861)
                    ·
                      refine ⟨2269466905802932359336349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12103823497615639249793861 2269466905802932359336349)
                      ·
                        rfl

theorem cell23_4419771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4].length) (baseStart_4419771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419771 prefixEnd_4419771 := by exact prefixLift 4419771
  have htrace : WordTrace (prefixWord ++ tailWord_4419771) baseStart_4419771 baseEnd_4419771 := by
    simpa [prefixWord, tailWord_4419771, baseEnd_4419771] using wordTrace_append hprefix tailTrace_4419771
  have hstable : (prefixWord ++ tailWord_4419771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419771).length < 2 ^ (prefixWord ++ tailWord_4419771).sum := by decide
  have hdescent : baseEnd_4419771 < baseStart_4419771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419791 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_4419791 : Nat := 118140960795 + 4419791 * 2 ^ 59
def prefixEnd_4419791 : Nat := 4983230072969 + 3 ^ 40 * 4419791 * 2
def baseEnd_4419791 : Nat := 2269477175416022281086257

theorem tailTrace_4419791 : CollatzResearch.WordTrace tailWord_4419791 prefixEnd_4419791 2269477175416022281086257 := by
  unfold tailWord_4419791
  simp only [CollatzResearch.WordTrace]
  refine ⟨161203021130859522052011227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107468680753906348034674151 161203021130859522052011227)
  ·
    refine ⟨241804531696289283078016841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161203021130859522052011227 241804531696289283078016841)
    ·
      refine ⟨181353398772216962308512631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241804531696289283078016841 181353398772216962308512631)
      ·
        refine ⟨272030098158325443462768947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181353398772216962308512631 272030098158325443462768947)
        ·
          refine ⟨408045147237488165194153421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272030098158325443462768947 408045147237488165194153421)
          ·
            refine ⟨153016930214058061947807533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408045147237488165194153421 153016930214058061947807533)
            ·
              refine ⟨57381348830271773230427825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153016930214058061947807533 57381348830271773230427825)
              ·
                refine ⟨43036011622703829922820869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57381348830271773230427825 43036011622703829922820869)
                ·
                  refine ⟨8069252179256968110528913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43036011622703829922820869 8069252179256968110528913)
                  ·
                    refine ⟨6051939134442726082896685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8069252179256968110528913 6051939134442726082896685)
                    ·
                      refine ⟨2269477175416022281086257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6051939134442726082896685 2269477175416022281086257)
                      ·
                        rfl

theorem cell23_4419791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_4419791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419791 prefixEnd_4419791 := by exact prefixLift 4419791
  have htrace : WordTrace (prefixWord ++ tailWord_4419791) baseStart_4419791 baseEnd_4419791 := by
    simpa [prefixWord, tailWord_4419791, baseEnd_4419791] using wordTrace_append hprefix tailTrace_4419791
  have hstable : (prefixWord ++ tailWord_4419791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419791).length < 2 ^ (prefixWord ++ tailWord_4419791).sum := by decide
  have hdescent : baseEnd_4419791 < baseStart_4419791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419805 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4419805 : Nat := 118140960795 + 4419805 * 2 ^ 59
def prefixEnd_4419805 : Nat := 4983230072969 + 3 ^ 40 * 4419805 * 2
def baseEnd_4419805 : Nat := 2269484364145185226311193

theorem tailTrace_4419805 : CollatzResearch.WordTrace tailWord_4419805 prefixEnd_4419805 2269484364145185226311193 := by
  unfold tailWord_4419805
  simp only [CollatzResearch.WordTrace]
  refine ⟨161203531752808802443020869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107469021168539201628680579 161203531752808802443020869)
  ·
    refine ⟨30225662203651650458066413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161203531752808802443020869 30225662203651650458066413)
    ·
      refine ⟨11334623326369368921774905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30225662203651650458066413 11334623326369368921774905)
      ·
        refine ⟨8500967494777026691331179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11334623326369368921774905 8500967494777026691331179)
        ·
          refine ⟨12751451242165540036996769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8500967494777026691331179 12751451242165540036996769)
          ·
            refine ⟨9563588431624155027747577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12751451242165540036996769 9563588431624155027747577)
            ·
              refine ⟨7172691323718116270810683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9563588431624155027747577 7172691323718116270810683)
              ·
                refine ⟨10759036985577174406216025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7172691323718116270810683 10759036985577174406216025)
                ·
                  refine ⟨8069277739182880804662019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10759036985577174406216025 8069277739182880804662019)
                  ·
                    refine ⟨12103916608774321206993029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8069277739182880804662019 12103916608774321206993029)
                    ·
                      refine ⟨2269484364145185226311193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12103916608774321206993029 2269484364145185226311193)
                      ·
                        rfl

theorem cell23_4419805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4419805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419805 prefixEnd_4419805 := by exact prefixLift 4419805
  have htrace : WordTrace (prefixWord ++ tailWord_4419805) baseStart_4419805 baseEnd_4419805 := by
    simpa [prefixWord, tailWord_4419805, baseEnd_4419805] using wordTrace_append hprefix tailTrace_4419805
  have hstable : (prefixWord ++ tailWord_4419805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419805).length < 2 ^ (prefixWord ++ tailWord_4419805).sum := by decide
  have hdescent : baseEnd_4419805 < baseStart_4419805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419808 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_4419808 : Nat := 118140960795 + 4419808 * 2 ^ 59
def prefixEnd_4419808 : Nat := 4983230072969 + 3 ^ 40 * 4419808 * 2
def baseEnd_4419808 : Nat := 2269485904587148714573679

theorem tailTrace_4419808 : CollatzResearch.WordTrace tailWord_4419808 prefixEnd_4419808 2269485904587148714573679 := by
  unfold tailWord_4419808
  simp only [CollatzResearch.WordTrace]
  refine ⟨80601820585898966977690039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107469094114531955970253385 80601820585898966977690039)
  ·
    refine ⟨120902730878848450466535059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80601820585898966977690039 120902730878848450466535059)
    ·
      refine ⟨181354096318272675699802589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120902730878848450466535059 181354096318272675699802589)
      ·
        refine ⟨68007786119352253387425971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181354096318272675699802589 68007786119352253387425971)
        ·
          refine ⟨102011679179028380081138957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68007786119352253387425971 102011679179028380081138957)
          ·
            refine ⟨38254379692135642530427109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102011679179028380081138957 38254379692135642530427109)
            ·
              refine ⟨7172696192275432974455083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38254379692135642530427109 7172696192275432974455083)
              ·
                refine ⟨10759044288413149461682625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7172696192275432974455083 10759044288413149461682625)
                ·
                  refine ⟨8069283216309862096261969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10759044288413149461682625 8069283216309862096261969)
                  ·
                    refine ⟨6051962412232396572196477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8069283216309862096261969 6051962412232396572196477)
                    ·
                      refine ⟨2269485904587148714573679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6051962412232396572196477 2269485904587148714573679)
                      ·
                        rfl

theorem cell23_4419808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_4419808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419808 prefixEnd_4419808 := by exact prefixLift 4419808
  have htrace : WordTrace (prefixWord ++ tailWord_4419808) baseStart_4419808 baseEnd_4419808 := by
    simpa [prefixWord, tailWord_4419808, baseEnd_4419808] using wordTrace_append hprefix tailTrace_4419808
  have hstable : (prefixWord ++ tailWord_4419808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419808).length < 2 ^ (prefixWord ++ tailWord_4419808).sum := by decide
  have hdescent : baseEnd_4419808 < baseStart_4419808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419841 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4419841 : Nat := 118140960795 + 4419841 * 2 ^ 59
def prefixEnd_4419841 : Nat := 4983230072969 + 3 ^ 40 * 4419841 * 2
def baseEnd_4419841 : Nat := 756500949816249028487009

theorem tailTrace_4419841 : CollatzResearch.WordTrace tailWord_4419841 prefixEnd_4419841 756500949816249028487009 := by
  unfold tailWord_4419841
  simp only [CollatzResearch.WordTrace]
  refine ⟨161204844780678380591331377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107469896520452253727554251 161204844780678380591331377)
  ·
    refine ⟨120903633585508785443498533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161204844780678380591331377 120903633585508785443498533)
    ·
      refine ⟨22669431297282897270655975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120903633585508785443498533 22669431297282897270655975)
      ·
        refine ⟨34004146945924345905983963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22669431297282897270655975 34004146945924345905983963)
        ·
          refine ⟨51006220418886518858975945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34004146945924345905983963 51006220418886518858975945)
          ·
            refine ⟨38254665314164889144231959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51006220418886518858975945 38254665314164889144231959)
            ·
              refine ⟨57381997971247333716347939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38254665314164889144231959 57381997971247333716347939)
              ·
                refine ⟨86072996956871000574521909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57381997971247333716347939 86072996956871000574521909)
                ·
                  refine ⟨8069343464706656303861429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86072996956871000574521909 8069343464706656303861429)
                  ·
                    refine ⟨756500949816249028487009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8069343464706656303861429 756500949816249028487009)
                    ·
                      rfl

theorem cell23_4419841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4419841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419841 prefixEnd_4419841 := by exact prefixLift 4419841
  have htrace : WordTrace (prefixWord ++ tailWord_4419841) baseStart_4419841 baseEnd_4419841 := by
    simpa [prefixWord, tailWord_4419841, baseEnd_4419841] using wordTrace_append hprefix tailTrace_4419841
  have hstable : (prefixWord ++ tailWord_4419841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419841).length < 2 ^ (prefixWord ++ tailWord_4419841).sum := by decide
  have hdescent : baseEnd_4419841 < baseStart_4419841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419872 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4419872 : Nat := 118140960795 + 4419872 * 2 ^ 59
def prefixEnd_4419872 : Nat := 4983230072969 + 3 ^ 40 * 4419872 * 2
def baseEnd_4419872 : Nat := 2269518767349036464173385

theorem tailTrace_4419872 : CollatzResearch.WordTrace tailWord_4419872 prefixEnd_4419872 2269518767349036464173385 := by
  unfold tailWord_4419872
  simp only [CollatzResearch.WordTrace]
  refine ⟨80602987721783036442854935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107470650295710715257139913 80602987721783036442854935)
  ·
    refine ⟨120904481582674554664282403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80602987721783036442854935 120904481582674554664282403)
    ·
      refine ⟨181356722374011831996423605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120904481582674554664282403 181356722374011831996423605)
      ·
        refine ⟨17002192722563609249664713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181356722374011831996423605 17002192722563609249664713)
        ·
          refine ⟨12751644541922706937248535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17002192722563609249664713 12751644541922706937248535)
          ·
            refine ⟨19127466812884060405872803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12751644541922706937248535 19127466812884060405872803)
            ·
              refine ⟨28691200219326090608809205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19127466812884060405872803 28691200219326090608809205)
              ·
                refine ⟨2689800020561820994575863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28691200219326090608809205 2689800020561820994575863)
                ·
                  refine ⟨4034700030842731491863795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689800020561820994575863 4034700030842731491863795)
                  ·
                    refine ⟨6052050046264097237795693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4034700030842731491863795 6052050046264097237795693)
                    ·
                      refine ⟨2269518767349036464173385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6052050046264097237795693 2269518767349036464173385)
                      ·
                        rfl

theorem cell23_4419872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4419872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419872 prefixEnd_4419872 := by exact prefixLift 4419872
  have htrace : WordTrace (prefixWord ++ tailWord_4419872) baseStart_4419872 baseEnd_4419872 := by
    simpa [prefixWord, tailWord_4419872, baseEnd_4419872] using wordTrace_append hprefix tailTrace_4419872
  have hstable : (prefixWord ++ tailWord_4419872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419872).length < 2 ^ (prefixWord ++ tailWord_4419872).sum := by decide
  have hdescent : baseEnd_4419872 < baseStart_4419872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419879 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 6]
def baseStart_4419879 : Nat := 118140960795 + 4419879 * 2 ^ 59
def prefixEnd_4419879 : Nat := 4983230072969 + 3 ^ 40 * 4419879 * 2
def baseEnd_4419879 : Nat := 252169151301513104087317

theorem tailTrace_4419879 : CollatzResearch.WordTrace tailWord_4419879 prefixEnd_4419879 252169151301513104087317 := by
  unfold tailWord_4419879
  simp only [CollatzResearch.WordTrace]
  refine ⟨161206230754540713081214691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107470820503027142054143127 161206230754540713081214691)
  ·
    refine ⟨241809346131811069621822037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161206230754540713081214691 241809346131811069621822037)
    ·
      refine ⟨2833703274982160972130727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 241809346131811069621822037 2833703274982160972130727)
      ·
        refine ⟨4250554912473241458196091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2833703274982160972130727 4250554912473241458196091)
        ·
          refine ⟨6375832368709862187294137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250554912473241458196091 6375832368709862187294137)
          ·
            refine ⟨4781874276532396640470603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6375832368709862187294137 4781874276532396640470603)
            ·
              refine ⟨7172811414798594960705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781874276532396640470603 7172811414798594960705905)
              ·
                refine ⟨5379608561098946220529429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7172811414798594960705905 5379608561098946220529429)
                ·
                  refine ⟨252169151301513104087317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5379608561098946220529429 252169151301513104087317)
                  ·
                    rfl

theorem cell23_4419879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 6].length) (baseStart_4419879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419879 prefixEnd_4419879 := by exact prefixLift 4419879
  have htrace : WordTrace (prefixWord ++ tailWord_4419879) baseStart_4419879 baseEnd_4419879 := by
    simpa [prefixWord, tailWord_4419879, baseEnd_4419879] using wordTrace_append hprefix tailTrace_4419879
  have hstable : (prefixWord ++ tailWord_4419879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419879).length < 2 ^ (prefixWord ++ tailWord_4419879).sum := by decide
  have hdescent : baseEnd_4419879 < baseStart_4419879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419888 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_4419888 : Nat := 118140960795 + 4419888 * 2 ^ 59
def prefixEnd_4419888 : Nat := 4983230072969 + 3 ^ 40 * 4419888 * 2
def baseEnd_4419888 : Nat := 756508994346502800524437

theorem tailTrace_4419888 : CollatzResearch.WordTrace tailWord_4419888 prefixEnd_4419888 756508994346502800524437 := by
  unfold tailWord_4419888
  simp only [CollatzResearch.WordTrace]
  refine ⟨80603279505754053809146159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107471039341005405078861545 80603279505754053809146159)
  ·
    refine ⟨120904919258631080713719239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80603279505754053809146159 120904919258631080713719239)
    ·
      refine ⟨181357378887946621070578859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120904919258631080713719239 181357378887946621070578859)
      ·
        refine ⟨272036068331919931605868289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181357378887946621070578859 272036068331919931605868289)
        ·
          refine ⟨204027051248939948704401217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272036068331919931605868289 204027051248939948704401217)
          ·
            refine ⟨153020288436704961528300913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204027051248939948704401217 153020288436704961528300913)
            ·
              refine ⟨114765216327528721146225685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153020288436704961528300913 114765216327528721146225685)
              ·
                refine ⟨5379619515352908803729329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114765216327528721146225685 5379619515352908803729329)
                ·
                  refine ⟨4034714636514681602796997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5379619515352908803729329 4034714636514681602796997)
                  ·
                    refine ⟨756508994346502800524437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034714636514681602796997 756508994346502800524437)
                    ·
                      rfl

theorem cell23_4419888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_4419888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419888 prefixEnd_4419888 := by exact prefixLift 4419888
  have htrace : WordTrace (prefixWord ++ tailWord_4419888) baseStart_4419888 baseEnd_4419888 := by
    simpa [prefixWord, tailWord_4419888, baseEnd_4419888] using wordTrace_append hprefix tailTrace_4419888
  have hstable : (prefixWord ++ tailWord_4419888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419888).length < 2 ^ (prefixWord ++ tailWord_4419888).sum := by decide
  have hdescent : baseEnd_4419888 < baseStart_4419888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419891 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_4419891 : Nat := 118140960795 + 4419891 * 2 ^ 59
def prefixEnd_4419891 : Nat := 4983230072969 + 3 ^ 40 * 4419891 * 2
def baseEnd_4419891 : Nat := 2269528523481471889835797

theorem tailTrace_4419891 : CollatzResearch.WordTrace tailWord_4419891 prefixEnd_4419891 2269528523481471889835797 := by
  unfold tailWord_4419891
  simp only [CollatzResearch.WordTrace]
  refine ⟨161206668430497239130651527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107471112286998159420434351 161206668430497239130651527)
  ·
    refine ⟨241810002645745858695977291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161206668430497239130651527 241810002645745858695977291)
    ·
      refine ⟨362715003968618788043965937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241810002645745858695977291 362715003968618788043965937)
      ·
        refine ⟨272036252976464091032974453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362715003968618788043965937 272036252976464091032974453)
        ·
          refine ⟨25503398716543508534341355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 272036252976464091032974453 25503398716543508534341355)
          ·
            refine ⟨38255098074815262801512033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25503398716543508534341355 38255098074815262801512033)
            ·
              refine ⟨28691323556111447101134025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38255098074815262801512033 28691323556111447101134025)
              ·
                refine ⟨21518492667083585325850519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28691323556111447101134025 21518492667083585325850519)
                ·
                  refine ⟨32277739000625377988775779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21518492667083585325850519 32277739000625377988775779)
                  ·
                    refine ⟨48416608500938066983163669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32277739000625377988775779 48416608500938066983163669)
                    ·
                      refine ⟨2269528523481471889835797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48416608500938066983163669 2269528523481471889835797)
                      ·
                        rfl

theorem cell23_4419891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_4419891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419891 prefixEnd_4419891 := by exact prefixLift 4419891
  have htrace : WordTrace (prefixWord ++ tailWord_4419891) baseStart_4419891 baseEnd_4419891 := by
    simpa [prefixWord, tailWord_4419891, baseEnd_4419891] using wordTrace_append hprefix tailTrace_4419891
  have hstable : (prefixWord ++ tailWord_4419891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419891).length < 2 ^ (prefixWord ++ tailWord_4419891).sum := by decide
  have hdescent : baseEnd_4419891 < baseStart_4419891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419898 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_4419898 : Nat := 118140960795 + 4419898 * 2 ^ 59
def prefixEnd_4419898 : Nat := 4983230072969 + 3 ^ 40 * 4419898 * 2
def baseEnd_4419898 : Nat := 2269532117846053362448265

theorem tailTrace_4419898 : CollatzResearch.WordTrace tailWord_4419898 prefixEnd_4419898 2269532117846053362448265 := by
  unfold tailWord_4419898
  simp only [CollatzResearch.WordTrace]
  refine ⟨40301730935367969831539087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107471282494314586217437565 40301730935367969831539087)
  ·
    refine ⟨60452596403051954747308631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40301730935367969831539087 60452596403051954747308631)
    ·
      refine ⟨90678894604577932120962947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60452596403051954747308631 90678894604577932120962947)
      ·
        refine ⟨136018341906866898181444421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90678894604577932120962947 136018341906866898181444421)
        ·
          refine ⟨25503439107537543409020829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136018341906866898181444421 25503439107537543409020829)
          ·
            refine ⟨9563789665326578778382811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25503439107537543409020829 9563789665326578778382811)
            ·
              refine ⟨14345684497989868167574217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9563789665326578778382811 14345684497989868167574217)
              ·
                refine ⟨10759263373492401125680663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14345684497989868167574217 10759263373492401125680663)
                ·
                  refine ⟨16138895060238601688520995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10759263373492401125680663 16138895060238601688520995)
                  ·
                    refine ⟨24208342590357902532781493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16138895060238601688520995 24208342590357902532781493)
                    ·
                      refine ⟨2269532117846053362448265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24208342590357902532781493 2269532117846053362448265)
                      ·
                        rfl

theorem cell23_4419898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_4419898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419898 prefixEnd_4419898 := by exact prefixLift 4419898
  have htrace : WordTrace (prefixWord ++ tailWord_4419898) baseStart_4419898 baseEnd_4419898 := by
    simpa [prefixWord, tailWord_4419898, baseEnd_4419898] using wordTrace_append hprefix tailTrace_4419898
  have hstable : (prefixWord ++ tailWord_4419898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419898).length < 2 ^ (prefixWord ++ tailWord_4419898).sum := by decide
  have hdescent : baseEnd_4419898 < baseStart_4419898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419932 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4419932 : Nat := 118140960795 + 4419932 * 2 ^ 59
def prefixEnd_4419932 : Nat := 4983230072969 + 3 ^ 40 * 4419932 * 2
def baseEnd_4419932 : Nat := 2269549576188306229423109

theorem tailTrace_4419932 : CollatzResearch.WordTrace tailWord_4419932 prefixEnd_4419932 2269549576188306229423109 := by
  unfold tailWord_4419932
  simp only [CollatzResearch.WordTrace]
  refine ⟨80604081911674351566447025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107472109215565802088596033 80604081911674351566447025)
  ·
    refine ⟨60453061433755763674835269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80604081911674351566447025 60453061433755763674835269)
    ·
      refine ⟨11334949018829205689031613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60453061433755763674835269 11334949018829205689031613)
      ·
        refine ⟨4250605882060952133386855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11334949018829205689031613 4250605882060952133386855)
        ·
          refine ⟨6375908823091428200080283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250605882060952133386855 6375908823091428200080283)
          ·
            refine ⟨9563863234637142300120425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375908823091428200080283 9563863234637142300120425)
            ·
              refine ⟨7172897425977856725090319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9563863234637142300120425 7172897425977856725090319)
              ·
                refine ⟨10759346138966785087635479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7172897425977856725090319 10759346138966785087635479)
                ·
                  refine ⟨16139019208450177631453219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10759346138966785087635479 16139019208450177631453219)
                  ·
                    refine ⟨24208528812675266447179829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16139019208450177631453219 24208528812675266447179829)
                    ·
                      refine ⟨2269549576188306229423109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24208528812675266447179829 2269549576188306229423109)
                      ·
                        rfl

theorem cell23_4419932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4419932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419932 prefixEnd_4419932 := by exact prefixLift 4419932
  have htrace : WordTrace (prefixWord ++ tailWord_4419932) baseStart_4419932 baseEnd_4419932 := by
    simpa [prefixWord, tailWord_4419932, baseEnd_4419932] using wordTrace_append hprefix tailTrace_4419932
  have hstable : (prefixWord ++ tailWord_4419932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419932).length < 2 ^ (prefixWord ++ tailWord_4419932).sum := by decide
  have hdescent : baseEnd_4419932 < baseStart_4419932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419945 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 3]
def baseStart_4419945 : Nat := 118140960795 + 4419945 * 2 ^ 59
def prefixEnd_4419945 : Nat := 4983230072969 + 3 ^ 40 * 4419945 * 2
def baseEnd_4419945 : Nat := 2269556251436814678560549

theorem tailTrace_4419945 : CollatzResearch.WordTrace tailWord_4419945 prefixEnd_4419945 2269556251436814678560549 := by
  unfold tailWord_4419945
  simp only [CollatzResearch.WordTrace]
  refine ⟨161208637972301606353117289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107472425314867737568744859 161208637972301606353117289)
  ·
    refine ⟨120906478479226204764837967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161208637972301606353117289 120906478479226204764837967)
    ·
      refine ⟨181359717718839307147256951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120906478479226204764837967 181359717718839307147256951)
      ·
        refine ⟨272039576578258960720885427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181359717718839307147256951 272039576578258960720885427)
        ·
          refine ⟨408059364867388441081328141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272039576578258960720885427 408059364867388441081328141)
          ·
            refine ⟨153022261825270665405498053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408059364867388441081328141 153022261825270665405498053)
            ·
              refine ⟨28691674092238249763530885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153022261825270665405498053 28691674092238249763530885)
              ·
                refine ⟨5379688892294671830662041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28691674092238249763530885 5379688892294671830662041)
                ·
                  refine ⟨4034766669221003872996531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5379688892294671830662041 4034766669221003872996531)
                  ·
                    refine ⟨6052150003831505809494797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4034766669221003872996531 6052150003831505809494797)
                    ·
                      refine ⟨2269556251436814678560549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6052150003831505809494797 2269556251436814678560549)
                      ·
                        rfl

theorem cell23_4419945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_4419945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419945 prefixEnd_4419945 := by exact prefixLift 4419945
  have htrace : WordTrace (prefixWord ++ tailWord_4419945) baseStart_4419945 baseEnd_4419945 := by
    simpa [prefixWord, tailWord_4419945, baseEnd_4419945] using wordTrace_append hprefix tailTrace_4419945
  have hstable : (prefixWord ++ tailWord_4419945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419945).length < 2 ^ (prefixWord ++ tailWord_4419945).sum := by decide
  have hdescent : baseEnd_4419945 < baseStart_4419945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4419961 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_4419961 : Nat := 118140960795 + 4419961 * 2 ^ 59
def prefixEnd_4419961 : Nat := 4983230072969 + 3 ^ 40 * 4419961 * 2
def baseEnd_4419961 : Nat := 756521489042428871986825

theorem tailTrace_4419961 : CollatzResearch.WordTrace tailWord_4419961 prefixEnd_4419961 756521489042428871986825 := by
  unfold tailWord_4419961
  simp only [CollatzResearch.WordTrace]
  refine ⟨161209221540243641085699737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107472814360162427390466491 161209221540243641085699737)
  ·
    refine ⟨120906916155182730814274803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161209221540243641085699737 120906916155182730814274803)
    ·
      refine ⟨181360374232774096221412205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120906916155182730814274803 181360374232774096221412205)
      ·
        refine ⟨68010140337290286083029577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181360374232774096221412205 68010140337290286083029577)
        ·
          refine ⟨51007605252967714562272183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68010140337290286083029577 51007605252967714562272183)
          ·
            refine ⟨76511407879451571843408275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51007605252967714562272183 76511407879451571843408275)
            ·
              refine ⟨114767111819177357765112413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76511407879451571843408275 114767111819177357765112413)
              ·
                refine ⟨43037666932191509161917155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114767111819177357765112413 43037666932191509161917155)
                ·
                  refine ⟨64556500398287263742875733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43037666932191509161917155 64556500398287263742875733)
                  ·
                    refine ⟨756521489042428871986825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64556500398287263742875733 756521489042428871986825)
                    ·
                      rfl

theorem cell23_4419961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_4419961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4419961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4419961 prefixEnd_4419961 := by exact prefixLift 4419961
  have htrace : WordTrace (prefixWord ++ tailWord_4419961) baseStart_4419961 baseEnd_4419961 := by
    simpa [prefixWord, tailWord_4419961, baseEnd_4419961] using wordTrace_append hprefix tailTrace_4419961
  have hstable : (prefixWord ++ tailWord_4419961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4419961).length < 2 ^ (prefixWord ++ tailWord_4419961).sum := by decide
  have hdescent : baseEnd_4419961 < baseStart_4419961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4419961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420011 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_4420011 : Nat := 118140960795 + 4420011 * 2 ^ 59
def prefixEnd_4420011 : Nat := 4983230072969 + 3 ^ 40 * 4420011 * 2
def baseEnd_4420011 : Nat := 2269590141160011420335245

theorem tailTrace_4420011 : CollatzResearch.WordTrace tailWord_4420011 prefixEnd_4420011 2269590141160011420335245 := by
  unfold tailWord_4420011
  simp only [CollatzResearch.WordTrace]
  refine ⟨161211045190062499625019887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107474030126708333083346591 161211045190062499625019887)
  ·
    refine ⟨241816567785093749437529831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161211045190062499625019887 241816567785093749437529831)
    ·
      refine ⟨362724851677640624156294747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241816567785093749437529831 362724851677640624156294747)
      ·
        refine ⟨544087277516460936234442121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362724851677640624156294747 544087277516460936234442121)
        ·
          refine ⟨408065458137345702175831591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544087277516460936234442121 408065458137345702175831591)
          ·
            refine ⟨612098187206018553263747387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408065458137345702175831591 612098187206018553263747387)
            ·
              refine ⟨918147280809027829895621081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612098187206018553263747387 918147280809027829895621081)
              ·
                refine ⟨688610460606770872421715811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918147280809027829895621081 688610460606770872421715811)
                ·
                  refine ⟨1032915690910156308632573717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688610460606770872421715811 1032915690910156308632573717)
                  ·
                    refine ⟨48417923011413576967151893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1032915690910156308632573717 48417923011413576967151893)
                    ·
                      refine ⟨2269590141160011420335245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48417923011413576967151893 2269590141160011420335245)
                      ·
                        rfl

theorem cell23_4420011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_4420011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420011 prefixEnd_4420011 := by exact prefixLift 4420011
  have htrace : WordTrace (prefixWord ++ tailWord_4420011) baseStart_4420011 baseEnd_4420011 := by
    simpa [prefixWord, tailWord_4420011, baseEnd_4420011] using wordTrace_append hprefix tailTrace_4420011
  have hstable : (prefixWord ++ tailWord_4420011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420011).length < 2 ^ (prefixWord ++ tailWord_4420011).sum := by decide
  have hdescent : baseEnd_4420011 < baseStart_4420011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420075 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 2, 4, 2]
def baseStart_4420075 : Nat := 118140960795 + 4420075 * 2 ^ 59
def prefixEnd_4420075 : Nat := 4983230072969 + 3 ^ 40 * 4420075 * 2
def baseEnd_4420075 : Nat := 2269623003921899169934951

theorem tailTrace_4420075 : CollatzResearch.WordTrace tailWord_4420075 prefixEnd_4420075 2269623003921899169934951 := by
  unfold tailWord_4420075
  simp only [CollatzResearch.WordTrace]
  refine ⟨161213379461830638555349679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107475586307887092370233119 161213379461830638555349679)
  ·
    refine ⟨241820069192745957833024519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161213379461830638555349679 241820069192745957833024519)
    ·
      refine ⟨362730103789118936749536779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241820069192745957833024519 362730103789118936749536779)
      ·
        refine ⟨544095155683678405124305169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362730103789118936749536779 544095155683678405124305169)
        ·
          refine ⟨408071366762758803843228877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544095155683678405124305169 408071366762758803843228877)
          ·
            refine ⟨153026762536034551441210829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408071366762758803843228877 153026762536034551441210829)
            ·
              refine ⟨57385035951012956790454061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153026762536034551441210829 57385035951012956790454061)
              ·
                refine ⟨21519388481629858796420273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57385035951012956790454061 21519388481629858796420273)
                ·
                  refine ⟨16139541361222394097315205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21519388481629858796420273 16139541361222394097315205)
                  ·
                    refine ⟨3026164005229198893246601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16139541361222394097315205 3026164005229198893246601)
                    ·
                      refine ⟨2269623003921899169934951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026164005229198893246601 2269623003921899169934951)
                      ·
                        rfl

theorem cell23_4420075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4, 2].length) (baseStart_4420075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420075 prefixEnd_4420075 := by exact prefixLift 4420075
  have htrace : WordTrace (prefixWord ++ tailWord_4420075) baseStart_4420075 baseEnd_4420075 := by
    simpa [prefixWord, tailWord_4420075, baseEnd_4420075] using wordTrace_append hprefix tailTrace_4420075
  have hstable : (prefixWord ++ tailWord_4420075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420075).length < 2 ^ (prefixWord ++ tailWord_4420075).sum := by decide
  have hdescent : baseEnd_4420075 < baseStart_4420075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420088 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_4420088 : Nat := 118140960795 + 4420088 * 2 ^ 59
def prefixEnd_4420088 : Nat := 4983230072969 + 3 ^ 40 * 4420088 * 2
def baseEnd_4420088 : Nat := 2269629679170407619072391

theorem tailTrace_4420088 : CollatzResearch.WordTrace tailWord_4420088 prefixEnd_4420088 2269629679170407619072391 := by
  unfold tailWord_4420088
  simp only [CollatzResearch.WordTrace]
  refine ⟨80606926805391770887786459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107475902407189027850381945 80606926805391770887786459)
  ·
    refine ⟨120910390208087656331679689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80606926805391770887786459 120910390208087656331679689)
    ·
      refine ⟨90682792656065742248759767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120910390208087656331679689 90682792656065742248759767)
      ·
        refine ⟨136024188984098613373139651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90682792656065742248759767 136024188984098613373139651)
        ·
          refine ⟨204036283476147920059709477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136024188984098613373139651 204036283476147920059709477)
          ·
            refine ⟨38256803151777735011195527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204036283476147920059709477 38256803151777735011195527)
            ·
              refine ⟨57385204727666602516793291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38256803151777735011195527 57385204727666602516793291)
              ·
                refine ⟨86077807091499903775189937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57385204727666602516793291 86077807091499903775189937)
                ·
                  refine ⟨64558355318624927831392453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86077807091499903775189937 64558355318624927831392453)
                  ·
                    refine ⟨12104691622242173968386085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64558355318624927831392453 12104691622242173968386085)
                    ·
                      refine ⟨2269629679170407619072391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12104691622242173968386085 2269629679170407619072391)
                      ·
                        rfl

theorem cell23_4420088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_4420088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420088 prefixEnd_4420088 := by exact prefixLift 4420088
  have htrace : WordTrace (prefixWord ++ tailWord_4420088) baseStart_4420088 baseEnd_4420088 := by
    simpa [prefixWord, tailWord_4420088, baseEnd_4420088] using wordTrace_append hprefix tailTrace_4420088
  have hstable : (prefixWord ++ tailWord_4420088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420088).length < 2 ^ (prefixWord ++ tailWord_4420088).sum := by decide
  have hdescent : baseEnd_4420088 < baseStart_4420088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420095 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_4420095 : Nat := 118140960795 + 4420095 * 2 ^ 59
def prefixEnd_4420095 : Nat := 4983230072969 + 3 ^ 40 * 4420095 * 2
def baseEnd_4420095 : Nat := 2269633273534989091684859

theorem tailTrace_4420095 : CollatzResearch.WordTrace tailWord_4420095 prefixEnd_4420095 2269633273534989091684859 := by
  unfold tailWord_4420095
  simp only [CollatzResearch.WordTrace]
  refine ⟨161214108921758181971077739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107476072614505454647385159 161214108921758181971077739)
  ·
    refine ⟨241821163382637272956616609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161214108921758181971077739 241821163382637272956616609)
    ·
      refine ⟨181365872536977954717462457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241821163382637272956616609 181365872536977954717462457)
      ·
        refine ⟨136024404402733466038096843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181365872536977954717462457 136024404402733466038096843)
        ·
          refine ⟨204036606604100199057145265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136024404402733466038096843 204036606604100199057145265)
          ·
            refine ⟨153027454953075149292858949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204036606604100199057145265 153027454953075149292858949)
            ·
              refine ⟨28692647803701590492411053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153027454953075149292858949 28692647803701590492411053)
              ·
                refine ⟨10759742926388096434654145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28692647803701590492411053 10759742926388096434654145)
                ·
                  refine ⟨8069807194791072325990609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10759742926388096434654145 8069807194791072325990609)
                  ·
                    refine ⟨6052355396093304244492957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8069807194791072325990609 6052355396093304244492957)
                    ·
                      refine ⟨2269633273534989091684859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6052355396093304244492957 2269633273534989091684859)
                      ·
                        rfl

theorem cell23_4420095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_4420095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420095 prefixEnd_4420095 := by exact prefixLift 4420095
  have htrace : WordTrace (prefixWord ++ tailWord_4420095) baseStart_4420095 baseEnd_4420095 := by
    simpa [prefixWord, tailWord_4420095, baseEnd_4420095] using wordTrace_append hprefix tailTrace_4420095
  have hstable : (prefixWord ++ tailWord_4420095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420095).length < 2 ^ (prefixWord ++ tailWord_4420095).sum := by decide
  have hdescent : baseEnd_4420095 < baseStart_4420095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420109 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4420109 : Nat := 118140960795 + 4420109 * 2 ^ 59
def prefixEnd_4420109 : Nat := 4983230072969 + 3 ^ 40 * 4420109 * 2
def baseEnd_4420109 : Nat := 2269640462264152036909795

theorem tailTrace_4420109 : CollatzResearch.WordTrace tailWord_4420109 prefixEnd_4420109 2269640462264152036909795 := by
  unfold tailWord_4420109
  simp only [CollatzResearch.WordTrace]
  refine ⟨161214619543707462362087381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107476413029138308241391587 161214619543707462362087381)
  ·
    refine ⟨3778467645555643649111423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 161214619543707462362087381 3778467645555643649111423)
    ·
      refine ⟨5667701468333465473667135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778467645555643649111423 5667701468333465473667135)
      ·
        refine ⟨8501552202500198210500703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667701468333465473667135 8501552202500198210500703)
        ·
          refine ⟨12752328303750297315751055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8501552202500198210500703 12752328303750297315751055)
          ·
            refine ⟨19128492455625445973626583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12752328303750297315751055 19128492455625445973626583)
            ·
              refine ⟨28692738683438168960439875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19128492455625445973626583 28692738683438168960439875)
              ·
                refine ⟨43039108025157253440659813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28692738683438168960439875 43039108025157253440659813)
                ·
                  refine ⟨8069832754716985020123715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43039108025157253440659813 8069832754716985020123715)
                  ·
                    refine ⟨12104749132075477530185573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8069832754716985020123715 12104749132075477530185573)
                    ·
                      refine ⟨2269640462264152036909795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12104749132075477530185573 2269640462264152036909795)
                      ·
                        rfl

theorem cell23_4420109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4420109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420109 prefixEnd_4420109 := by exact prefixLift 4420109
  have htrace : WordTrace (prefixWord ++ tailWord_4420109) baseStart_4420109 baseEnd_4420109 := by
    simpa [prefixWord, tailWord_4420109, baseEnd_4420109] using wordTrace_append hprefix tailTrace_4420109
  have hstable : (prefixWord ++ tailWord_4420109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420109).length < 2 ^ (prefixWord ++ tailWord_4420109).sum := by decide
  have hdescent : baseEnd_4420109 < baseStart_4420109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420159 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 1, 1, 3]
def baseStart_4420159 : Nat := 118140960795 + 4420159 * 2 ^ 59
def prefixEnd_4420159 : Nat := 4983230072969 + 3 ^ 40 * 4420159 * 2
def baseEnd_4420159 : Nat := 2269666136296876841284565

theorem tailTrace_4420159 : CollatzResearch.WordTrace tailWord_4420159 prefixEnd_4420159 2269666136296876841284565 := by
  unfold tailWord_4420159
  simp only [CollatzResearch.WordTrace]
  refine ⟨161216443193526320901407531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107477628795684213934271687 161216443193526320901407531)
  ·
    refine ⟨241824664790289481352111297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161216443193526320901407531 241824664790289481352111297)
    ·
      refine ⟨181368498592717111014083473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241824664790289481352111297 181368498592717111014083473)
      ·
        refine ⟨136026373944537833260562605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181368498592717111014083473 136026373944537833260562605)
        ·
          refine ⟨51009890229201687472710977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136026373944537833260562605 51009890229201687472710977)
          ·
            refine ⟨38257417671901265604533233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51009890229201687472710977 38257417671901265604533233)
            ·
              refine ⟨28693063253925949203399925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38257417671901265604533233 28693063253925949203399925)
              ·
                refine ⟨2689974680055557737818743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28693063253925949203399925 2689974680055557737818743)
                ·
                  refine ⟨4034962020083336606728115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689974680055557737818743 4034962020083336606728115)
                  ·
                    refine ⟨6052443030125004910092173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4034962020083336606728115 6052443030125004910092173)
                    ·
                      refine ⟨2269666136296876841284565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6052443030125004910092173 2269666136296876841284565)
                      ·
                        rfl

theorem cell23_4420159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_4420159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420159 prefixEnd_4420159 := by exact prefixLift 4420159
  have htrace : WordTrace (prefixWord ++ tailWord_4420159) baseStart_4420159 baseEnd_4420159 := by
    simpa [prefixWord, tailWord_4420159, baseEnd_4420159] using wordTrace_append hprefix tailTrace_4420159
  have hstable : (prefixWord ++ tailWord_4420159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420159).length < 2 ^ (prefixWord ++ tailWord_4420159).sum := by decide
  have hdescent : baseEnd_4420159 < baseStart_4420159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420175 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 4, 4]
def baseStart_4420175 : Nat := 118140960795 + 4420175 * 2 ^ 59
def prefixEnd_4420175 : Nat := 4983230072969 + 3 ^ 40 * 4420175 * 2
def baseEnd_4420175 : Nat := 756558117329116259561497

theorem tailTrace_4420175 : CollatzResearch.WordTrace tailWord_4420175 prefixEnd_4420175 756558117329116259561497 := by
  unfold tailWord_4420175
  simp only [CollatzResearch.WordTrace]
  refine ⟨161217026761468355633989979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107478017840978903755993319 161217026761468355633989979)
  ·
    refine ⟨241825540142202533450984969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161217026761468355633989979 241825540142202533450984969)
    ·
      refine ⟨181369155106651900088238727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241825540142202533450984969 181369155106651900088238727)
      ·
        refine ⟨272053732659977850132358091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181369155106651900088238727 272053732659977850132358091)
        ·
          refine ⟨408080598989966775198537137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272053732659977850132358091 408080598989966775198537137)
          ·
            refine ⟨306060449242475081398902853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408080598989966775198537137 306060449242475081398902853)
            ·
              refine ⟨57386334232964077762294285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 306060449242475081398902853 57386334232964077762294285)
              ·
                refine ⟨21519875337361529160860357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57386334232964077762294285 21519875337361529160860357)
                ·
                  refine ⟨4034976625755286717661317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21519875337361529160860357 4034976625755286717661317)
                  ·
                    refine ⟨756558117329116259561497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034976625755286717661317 756558117329116259561497)
                    ·
                      rfl

theorem cell23_4420175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_4420175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420175 prefixEnd_4420175 := by exact prefixLift 4420175
  have htrace : WordTrace (prefixWord ++ tailWord_4420175) baseStart_4420175 baseEnd_4420175 := by
    simpa [prefixWord, tailWord_4420175, baseEnd_4420175] using wordTrace_append hprefix tailTrace_4420175
  have hstable : (prefixWord ++ tailWord_4420175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420175).length < 2 ^ (prefixWord ++ tailWord_4420175).sum := by decide
  have hdescent : baseEnd_4420175 < baseStart_4420175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420192 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_4420192 : Nat := 118140960795 + 4420192 * 2 ^ 59
def prefixEnd_4420192 : Nat := 4983230072969 + 3 ^ 40 * 4420192 * 2
def baseEnd_4420192 : Nat := 756561027052825070723971

theorem tailTrace_4420192 : CollatzResearch.WordTrace tailWord_4420192 prefixEnd_4420192 756561027052825070723971 := by
  unfold tailWord_4420192
  simp only [CollatzResearch.WordTrace]
  refine ⟨80608823401203383768679415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107478431201604511691572553 80608823401203383768679415)
  ·
    refine ⟨120913235101805075653019123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80608823401203383768679415 120913235101805075653019123)
    ·
      refine ⟨181369852652707613479528685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120913235101805075653019123 181369852652707613479528685)
      ·
        refine ⟨68013694744765355054823257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181369852652707613479528685 68013694744765355054823257)
        ·
          refine ⟨51010271058574016291117443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68013694744765355054823257 51010271058574016291117443)
          ·
            refine ⟨76515406587861024436676165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51010271058574016291117443 76515406587861024436676165)
            ·
              refine ⟨14346638735223942081876781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76515406587861024436676165 14346638735223942081876781)
              ·
                refine ⟨5379989525708978280703793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14346638735223942081876781 5379989525708978280703793)
                ·
                  refine ⟨4034992144281733710527845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5379989525708978280703793 4034992144281733710527845)
                  ·
                    refine ⟨756561027052825070723971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034992144281733710527845 756561027052825070723971)
                    ·
                      rfl

theorem cell23_4420192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_4420192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420192 prefixEnd_4420192 := by exact prefixLift 4420192
  have htrace : WordTrace (prefixWord ++ tailWord_4420192) baseStart_4420192 baseEnd_4420192 := by
    simpa [prefixWord, tailWord_4420192, baseEnd_4420192] using wordTrace_append hprefix tailTrace_4420192
  have hstable : (prefixWord ++ tailWord_4420192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420192).length < 2 ^ (prefixWord ++ tailWord_4420192).sum := by decide
  have hdescent : baseEnd_4420192 < baseStart_4420192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420202 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4420202 : Nat := 118140960795 + 4420202 * 2 ^ 59
def prefixEnd_4420202 : Nat := 4983230072969 + 3 ^ 40 * 4420202 * 2
def baseEnd_4420202 : Nat := 2269688215965020173046867

theorem tailTrace_4420202 : CollatzResearch.WordTrace tailWord_4420202 prefixEnd_4420202 2269688215965020173046867 := by
  unfold tailWord_4420202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40304502883092634811305715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107478674354913692830148573 40304502883092634811305715)
  ·
    refine ⟨60456754324638952216958573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40304502883092634811305715 60456754324638952216958573)
    ·
      refine ⟨22671282871739607081359465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60456754324638952216958573 22671282871739607081359465)
      ·
        refine ⟨17003462153804705311019599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22671282871739607081359465 17003462153804705311019599)
        ·
          refine ⟨25505193230707057966529399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17003462153804705311019599 25505193230707057966529399)
          ·
            refine ⟨38257789846060586949794099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25505193230707057966529399 38257789846060586949794099)
            ·
              refine ⟨57386684769090880424691149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38257789846060586949794099 57386684769090880424691149)
              ·
                refine ⟨21520006788409080159259181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57386684769090880424691149 21520006788409080159259181)
                ·
                  refine ⟨8070002545653405059722193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21520006788409080159259181 8070002545653405059722193)
                  ·
                    refine ⟨6052501909240053794791645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8070002545653405059722193 6052501909240053794791645)
                    ·
                      refine ⟨2269688215965020173046867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6052501909240053794791645 2269688215965020173046867)
                      ·
                        rfl

theorem cell23_4420202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4420202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420202 prefixEnd_4420202 := by exact prefixLift 4420202
  have htrace : WordTrace (prefixWord ++ tailWord_4420202) baseStart_4420202 baseEnd_4420202 := by
    simpa [prefixWord, tailWord_4420202, baseEnd_4420202] using wordTrace_append hprefix tailTrace_4420202
  have hstable : (prefixWord ++ tailWord_4420202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420202).length < 2 ^ (prefixWord ++ tailWord_4420202).sum := by decide
  have hdescent : baseEnd_4420202 < baseStart_4420202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420213 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4420213 : Nat := 118140960795 + 4420213 * 2 ^ 59
def prefixEnd_4420213 : Nat := 4983230072969 + 3 ^ 40 * 4420213 * 2
def baseEnd_4420213 : Nat := 756564621417406543336439

theorem tailTrace_4420213 : CollatzResearch.WordTrace tailWord_4420213 prefixEnd_4420213 756564621417406543336439 := by
  unfold tailWord_4420213
  simp only [CollatzResearch.WordTrace]
  refine ⟨161218412735330688123873293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107478941823553792082582195 161218412735330688123873293)
  ·
    refine ⟨60456904775749008046452485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161218412735330688123873293 60456904775749008046452485)
    ·
      refine ⟨11335669645452939008709841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60456904775749008046452485 11335669645452939008709841)
      ·
        refine ⟨8501752234089704256532381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11335669645452939008709841 8501752234089704256532381)
        ·
          refine ⟨3188157087783639096199643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8501752234089704256532381 3188157087783639096199643)
          ·
            refine ⟨4782235631675458644299465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188157087783639096199643 4782235631675458644299465)
            ·
              refine ⟨3586676723756593983224599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782235631675458644299465 3586676723756593983224599)
              ·
                refine ⟨5380015085634890974836899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586676723756593983224599 5380015085634890974836899)
                ·
                  refine ⟨8070022628452336462255349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5380015085634890974836899 8070022628452336462255349)
                  ·
                    refine ⟨756564621417406543336439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8070022628452336462255349 756564621417406543336439)
                    ·
                      rfl

theorem cell23_4420213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4420213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420213 prefixEnd_4420213 := by exact prefixLift 4420213
  have htrace : WordTrace (prefixWord ++ tailWord_4420213) baseStart_4420213 baseEnd_4420213 := by
    simpa [prefixWord, tailWord_4420213, baseEnd_4420213] using wordTrace_append hprefix tailTrace_4420213
  have hstable : (prefixWord ++ tailWord_4420213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420213).length < 2 ^ (prefixWord ++ tailWord_4420213).sum := by decide
  have hdescent : baseEnd_4420213 < baseStart_4420213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420272 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2]
def baseStart_4420272 : Nat := 118140960795 + 4420272 * 2 ^ 59
def prefixEnd_4420272 : Nat := 4983230072969 + 3 ^ 40 * 4420272 * 2
def baseEnd_4420272 : Nat := 2269724159610834899171545

theorem tailTrace_4420272 : CollatzResearch.WordTrace tailWord_4420272 prefixEnd_4420272 2269724159610834899171545 := by
  unfold tailWord_4420272
  simp only [CollatzResearch.WordTrace]
  refine ⟨80610282321058470600135535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107480376428077960800180713 80610282321058470600135535)
  ·
    refine ⟨120915423481587705900203303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80610282321058470600135535 120915423481587705900203303)
    ·
      refine ⟨181373135222381558850304955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120915423481587705900203303 181373135222381558850304955)
      ·
        refine ⟨272059702833572338275457433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181373135222381558850304955 272059702833572338275457433)
        ·
          refine ⟨204044777125179253706593075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272059702833572338275457433 204044777125179253706593075)
          ·
            refine ⟨306067165687768880559889613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204044777125179253706593075 306067165687768880559889613)
            ·
              refine ⟨114775187132913330209958605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306067165687768880559889613 114775187132913330209958605)
              ·
                refine ⟨43040695174842498828734477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114775187132913330209958605 43040695174842498828734477)
                ·
                  refine ⟨16140260690565937060775429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43040695174842498828734477 16140260690565937060775429)
                  ·
                    refine ⟨3026298879481113198895393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16140260690565937060775429 3026298879481113198895393)
                    ·
                      refine ⟨2269724159610834899171545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026298879481113198895393 2269724159610834899171545)
                      ·
                        rfl

theorem cell23_4420272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2].length) (baseStart_4420272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420272 prefixEnd_4420272 := by exact prefixLift 4420272
  have htrace : WordTrace (prefixWord ++ tailWord_4420272) baseStart_4420272 baseEnd_4420272 := by
    simpa [prefixWord, tailWord_4420272, baseEnd_4420272] using wordTrace_append hprefix tailTrace_4420272
  have hstable : (prefixWord ++ tailWord_4420272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420272).length < 2 ^ (prefixWord ++ tailWord_4420272).sum := by decide
  have hdescent : baseEnd_4420272 < baseStart_4420272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420275 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_4420275 : Nat := 118140960795 + 4420275 * 2 ^ 59
def prefixEnd_4420275 : Nat := 4983230072969 + 3 ^ 40 * 4420275 * 2
def baseEnd_4420275 : Nat := 2269725700052798387434031

theorem tailTrace_4420275 : CollatzResearch.WordTrace tailWord_4420275 prefixEnd_4420275 2269725700052798387434031 := by
  unfold tailWord_4420275
  simp only [CollatzResearch.WordTrace]
  refine ⟨161220674061106072712630279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107480449374070715141753519 161220674061106072712630279)
  ·
    refine ⟨241831011091659109068945419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161220674061106072712630279 241831011091659109068945419)
    ·
      refine ⟨362746516637488663603418129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241831011091659109068945419 362746516637488663603418129)
      ·
        refine ⟨272059887478116497702563597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362746516637488663603418129 272059887478116497702563597)
        ·
          refine ⟨102022457804293686638461349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272059887478116497702563597 102022457804293686638461349)
          ·
            refine ⟨19129210838305066244711503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102022457804293686638461349 19129210838305066244711503)
            ·
              refine ⟨28693816257457599367067255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19129210838305066244711503 28693816257457599367067255)
              ·
                refine ⟨43040724386186399050600883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28693816257457599367067255 43040724386186399050600883)
                ·
                  refine ⟨64561086579279598575901325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43040724386186399050600883 64561086579279598575901325)
                  ·
                    refine ⟨24210407467229849465962997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64561086579279598575901325 24210407467229849465962997)
                    ·
                      refine ⟨2269725700052798387434031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24210407467229849465962997 2269725700052798387434031)
                      ·
                        rfl

theorem cell23_4420275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_4420275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420275 prefixEnd_4420275 := by exact prefixLift 4420275
  have htrace : WordTrace (prefixWord ++ tailWord_4420275) baseStart_4420275 baseEnd_4420275 := by
    simpa [prefixWord, tailWord_4420275, baseEnd_4420275] using wordTrace_append hprefix tailTrace_4420275
  have hstable : (prefixWord ++ tailWord_4420275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420275).length < 2 ^ (prefixWord ++ tailWord_4420275).sum := by decide
  have hdescent : baseEnd_4420275 < baseStart_4420275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420295 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 7]
def baseStart_4420295 : Nat := 118140960795 + 4420295 * 2 ^ 59
def prefixEnd_4420295 : Nat := 4983230072969 + 3 ^ 40 * 4420295 * 2
def baseEnd_4420295 : Nat := 252192885518432034353771

theorem tailTrace_4420295 : CollatzResearch.WordTrace tailWord_4420295 prefixEnd_4420295 252192885518432034353771 := by
  unfold tailWord_4420295
  simp only [CollatzResearch.WordTrace]
  refine ⟨161221403521033616128358339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107480935680689077418905559 161221403521033616128358339)
  ·
    refine ⟨241832105281550424192537509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161221403521033616128358339 241832105281550424192537509)
    ·
      refine ⟨45343519740290704536100783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241832105281550424192537509 45343519740290704536100783)
      ·
        refine ⟨68015279610436056804151175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45343519740290704536100783 68015279610436056804151175)
        ·
          refine ⟨102022919415654085206226763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68015279610436056804151175 102022919415654085206226763)
          ·
            refine ⟨153034379123481127809340145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102022919415654085206226763 153034379123481127809340145)
            ·
              refine ⟨114775784342610845857005109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153034379123481127809340145 114775784342610845857005109)
              ·
                refine ⟨10760229782119766799094229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114775784342610845857005109 10760229782119766799094229)
                ·
                  refine ⟨252192885518432034353771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10760229782119766799094229 252192885518432034353771)
                  ·
                    rfl

theorem cell23_4420295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 7].length) (baseStart_4420295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420295 prefixEnd_4420295 := by exact prefixLift 4420295
  have htrace : WordTrace (prefixWord ++ tailWord_4420295) baseStart_4420295 baseEnd_4420295 := by
    simpa [prefixWord, tailWord_4420295, baseEnd_4420295] using wordTrace_append hprefix tailTrace_4420295
  have hstable : (prefixWord ++ tailWord_4420295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420295).length < 2 ^ (prefixWord ++ tailWord_4420295).sum := by decide
  have hdescent : baseEnd_4420295 < baseStart_4420295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420355 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 8]
def baseStart_4420355 : Nat := 118140960795 + 4420355 * 2 ^ 59
def prefixEnd_4420355 : Nat := 4983230072969 + 3 ^ 40 * 4420355 * 2
def baseEnd_4420355 : Nat := 756588926168386024811221

theorem tailTrace_4420355 : CollatzResearch.WordTrace tailWord_4420355 prefixEnd_4420355 756588926168386024811221 := by
  unfold tailWord_4420355
  simp only [CollatzResearch.WordTrace]
  refine ⟨161223591900816246375542519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107482394600544164250361679 161223591900816246375542519)
  ·
    refine ⟨241835387851224369563313779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161223591900816246375542519 241835387851224369563313779)
    ·
      refine ⟨362753081776836554344970669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241835387851224369563313779 362753081776836554344970669)
      ·
        refine ⟨136032405666313707879364001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362753081776836554344970669 136032405666313707879364001)
        ·
          refine ⟨102024304249735280909523001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136032405666313707879364001 102024304249735280909523001)
          ·
            refine ⟨76518228187301460682142251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102024304249735280909523001 76518228187301460682142251)
            ·
              refine ⟨114777342280952191023213377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76518228187301460682142251 114777342280952191023213377)
              ·
                refine ⟨86083006710714143267410033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114777342280952191023213377 86083006710714143267410033)
                ·
                  refine ⟨64562255033035607450557525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86083006710714143267410033 64562255033035607450557525)
                  ·
                    refine ⟨756588926168386024811221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64562255033035607450557525 756588926168386024811221)
                    ·
                      rfl

theorem cell23_4420355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_4420355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420355 prefixEnd_4420355 := by exact prefixLift 4420355
  have htrace : WordTrace (prefixWord ++ tailWord_4420355) baseStart_4420355 baseEnd_4420355 := by
    simpa [prefixWord, tailWord_4420355, baseEnd_4420355] using wordTrace_append hprefix tailTrace_4420355
  have hstable : (prefixWord ++ tailWord_4420355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420355).length < 2 ^ (prefixWord ++ tailWord_4420355).sum := by decide
  have hdescent : baseEnd_4420355 < baseStart_4420355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420362 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4420362 : Nat := 118140960795 + 4420362 * 2 ^ 59
def prefixEnd_4420362 : Nat := 4983230072969 + 3 ^ 40 * 4420362 * 2
def baseEnd_4420362 : Nat := 2269770372869739547046131

theorem tailTrace_4420362 : CollatzResearch.WordTrace tailWord_4420362 prefixEnd_4420362 2269770372869739547046131 := by
  unfold tailWord_4420362
  simp only [CollatzResearch.WordTrace]
  refine ⟨40305961802947721642761835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107482564807860591047364893 40305961802947721642761835)
  ·
    refine ⟨60458942704421582464142753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40305961802947721642761835 60458942704421582464142753)
    ·
      refine ⟨45344207028316186848107065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60458942704421582464142753 45344207028316186848107065)
      ·
        refine ⟨34008155271237140136080299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45344207028316186848107065 34008155271237140136080299)
        ·
          refine ⟨51012232906855710204120449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34008155271237140136080299 51012232906855710204120449)
          ·
            refine ⟨38259174680141782653090337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51012232906855710204120449 38259174680141782653090337)
            ·
              refine ⟨28694381010106336989817753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38259174680141782653090337 28694381010106336989817753)
              ·
                refine ⟨21520785757579752742363315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28694381010106336989817753 21520785757579752742363315)
                ·
                  refine ⟨32281178636369629113544973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21520785757579752742363315 32281178636369629113544973)
                  ·
                    refine ⟨12105441988638610917579365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32281178636369629113544973 12105441988638610917579365)
                    ·
                      refine ⟨2269770372869739547046131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12105441988638610917579365 2269770372869739547046131)
                      ·
                        rfl

theorem cell23_4420362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4420362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420362 prefixEnd_4420362 := by exact prefixLift 4420362
  have htrace : WordTrace (prefixWord ++ tailWord_4420362) baseStart_4420362 baseEnd_4420362 := by
    simpa [prefixWord, tailWord_4420362, baseEnd_4420362] using wordTrace_append hprefix tailTrace_4420362
  have hstable : (prefixWord ++ tailWord_4420362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420362).length < 2 ^ (prefixWord ++ tailWord_4420362).sum := by decide
  have hdescent : baseEnd_4420362 < baseStart_4420362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420392 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4420392 : Nat := 118140960795 + 4420392 * 2 ^ 59
def prefixEnd_4420392 : Nat := 4983230072969 + 3 ^ 40 * 4420392 * 2
def baseEnd_4420392 : Nat := 2269785777289374429670993

theorem tailTrace_4420392 : CollatzResearch.WordTrace tailWord_4420392 prefixEnd_4420392 2269785777289374429670993 := by
  unfold tailWord_4420392
  simp only [CollatzResearch.WordTrace]
  refine ⟨80612470700841100847319715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107483294267788134463092953 80612470700841100847319715)
  ·
    refine ⟨120918706051261651270979573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80612470700841100847319715 120918706051261651270979573)
    ·
      refine ⟨11336128692305779806654335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120918706051261651270979573 11336128692305779806654335)
      ·
        refine ⟨17004193038458669709981503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11336128692305779806654335 17004193038458669709981503)
        ·
          refine ⟨25506289557688004564972255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17004193038458669709981503 25506289557688004564972255)
          ·
            refine ⟨38259434336532006847458383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25506289557688004564972255 38259434336532006847458383)
            ·
              refine ⟨57389151504798010271187575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38259434336532006847458383 57389151504798010271187575)
              ·
                refine ⟨86083727257197015406781363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57389151504798010271187575 86083727257197015406781363)
                ·
                  refine ⟨129125590885795523110172045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86083727257197015406781363 129125590885795523110172045)
                  ·
                    refine ⟨48422096582173321166314517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129125590885795523110172045 48422096582173321166314517)
                    ·
                      refine ⟨2269785777289374429670993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48422096582173321166314517 2269785777289374429670993)
                      ·
                        rfl

theorem cell23_4420392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4420392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420392 prefixEnd_4420392 := by exact prefixLift 4420392
  have htrace : WordTrace (prefixWord ++ tailWord_4420392) baseStart_4420392 baseEnd_4420392 := by
    simpa [prefixWord, tailWord_4420392, baseEnd_4420392] using wordTrace_append hprefix tailTrace_4420392
  have hstable : (prefixWord ++ tailWord_4420392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420392).length < 2 ^ (prefixWord ++ tailWord_4420392).sum := by decide
  have hdescent : baseEnd_4420392 < baseStart_4420392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420402 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_4420402 : Nat := 118140960795 + 4420402 * 2 ^ 59
def prefixEnd_4420402 : Nat := 4983230072969 + 3 ^ 40 * 4420402 * 2
def baseEnd_4420402 : Nat := 252198990232879932282883

theorem tailTrace_4420402 : CollatzResearch.WordTrace tailWord_4420402 prefixEnd_4420402 252198990232879932282883 := by
  unfold tailWord_4420402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40306326532911493350625865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107483537421097315601668973 40306326532911493350625865)
  ·
    refine ⟨30229744899683620012969399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40306326532911493350625865 30229744899683620012969399)
    ·
      refine ⟨45344617349525430019454099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30229744899683620012969399 45344617349525430019454099)
      ·
        refine ⟨68016926024288145029181149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45344617349525430019454099 68016926024288145029181149)
        ·
          refine ⟨25506347259108054385942931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68016926024288145029181149 25506347259108054385942931)
          ·
            refine ⟨38259520888662081578914397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25506347259108054385942931 38259520888662081578914397)
            ·
              refine ⟨14347320333248280592092899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38259520888662081578914397 14347320333248280592092899)
              ·
                refine ⟨21520980499872420888139349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14347320333248280592092899 21520980499872420888139349)
                ·
                  refine ⟨252198990232879932282883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21520980499872420888139349 252198990232879932282883)
                  ·
                    rfl

theorem cell23_4420402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_4420402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420402 prefixEnd_4420402 := by exact prefixLift 4420402
  have htrace : WordTrace (prefixWord ++ tailWord_4420402) baseStart_4420402 baseEnd_4420402 := by
    simpa [prefixWord, tailWord_4420402, baseEnd_4420402] using wordTrace_append hprefix tailTrace_4420402
  have hstable : (prefixWord ++ tailWord_4420402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420402).length < 2 ^ (prefixWord ++ tailWord_4420402).sum := by decide
  have hdescent : baseEnd_4420402 < baseStart_4420402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420419 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 6]
def baseStart_4420419 : Nat := 118140960795 + 4420419 * 2 ^ 59
def prefixEnd_4420419 : Nat := 4983230072969 + 3 ^ 40 * 4420419 * 2
def baseEnd_4420419 : Nat := 252199960140782869337041

theorem tailTrace_4420419 : CollatzResearch.WordTrace tailWord_4420419 prefixEnd_4420419 252199960140782869337041 := by
  unfold tailWord_4420419
  simp only [CollatzResearch.WordTrace]
  refine ⟨161225926172584385305872311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107483950781722923537248207 161225926172584385305872311)
  ·
    refine ⟨241838889258876577958808467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161225926172584385305872311 241838889258876577958808467)
    ·
      refine ⟨362758333888314866938212701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241838889258876577958808467 362758333888314866938212701)
      ·
        refine ⟨136034375208118075101829763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362758333888314866938212701 136034375208118075101829763)
        ·
          refine ⟨204051562812177112652744645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136034375208118075101829763 204051562812177112652744645)
          ·
            refine ⟨38259668027283208622389621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204051562812177112652744645 38259668027283208622389621)
            ·
              refine ⟨3586843877557800808349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38259668027283208622389621 3586843877557800808349027)
              ·
                refine ⟨5380265816336701212523541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586843877557800808349027 5380265816336701212523541)
                ·
                  refine ⟨252199960140782869337041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5380265816336701212523541 252199960140782869337041)
                  ·
                    rfl

theorem cell23_4420419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 6].length) (baseStart_4420419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420419 prefixEnd_4420419 := by exact prefixLift 4420419
  have htrace : WordTrace (prefixWord ++ tailWord_4420419) baseStart_4420419 baseEnd_4420419 := by
    simpa [prefixWord, tailWord_4420419, baseEnd_4420419] using wordTrace_append hprefix tailTrace_4420419
  have hstable : (prefixWord ++ tailWord_4420419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420419).length < 2 ^ (prefixWord ++ tailWord_4420419).sum := by decide
  have hdescent : baseEnd_4420419 < baseStart_4420419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420432 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_4420432 : Nat := 118140960795 + 4420432 * 2 ^ 59
def prefixEnd_4420432 : Nat := 4983230072969 + 3 ^ 40 * 4420432 * 2
def baseEnd_4420432 : Nat := 756602105505184757723603

theorem tailTrace_4420432 : CollatzResearch.WordTrace tailWord_4420432 prefixEnd_4420432 756602105505184757723603 := by
  unfold tailWord_4420432
  simp only [CollatzResearch.WordTrace]
  refine ⟨80613200160768644263047775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107484266881024859017397033 80613200160768644263047775)
  ·
    refine ⟨120919800241152966394571663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80613200160768644263047775 120919800241152966394571663)
    ·
      refine ⟨181379700361729449591857495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120919800241152966394571663 181379700361729449591857495)
      ·
        refine ⟨272069550542594174387786243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181379700361729449591857495 272069550542594174387786243)
        ·
          refine ⟨408104325813891261581679365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272069550542594174387786243 408104325813891261581679365)
          ·
            refine ⟨76519561090104611546564881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 408104325813891261581679365 76519561090104611546564881)
            ·
              refine ⟨57389670817578458659923661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76519561090104611546564881 57389670817578458659923661)
              ·
                refine ⟨21521126556591921997471373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57389670817578458659923661 21521126556591921997471373)
                ·
                  refine ⟨8070422458721970749051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21521126556591921997471373 8070422458721970749051765)
                  ·
                    refine ⟨756602105505184757723603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8070422458721970749051765 756602105505184757723603)
                    ·
                      rfl

theorem cell23_4420432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_4420432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420432 prefixEnd_4420432 := by exact prefixLift 4420432
  have htrace : WordTrace (prefixWord ++ tailWord_4420432) baseStart_4420432 baseEnd_4420432 := by
    simpa [prefixWord, tailWord_4420432, baseEnd_4420432] using wordTrace_append hprefix tailTrace_4420432
  have hstable : (prefixWord ++ tailWord_4420432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420432).length < 2 ^ (prefixWord ++ tailWord_4420432).sum := by decide
  have hdescent : baseEnd_4420432 < baseStart_4420432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420456 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4420456 : Nat := 118140960795 + 4420456 * 2 ^ 59
def prefixEnd_4420456 : Nat := 4983230072969 + 3 ^ 40 * 4420456 * 2
def baseEnd_4420456 : Nat := 2269818640051262179270699

theorem tailTrace_4420456 : CollatzResearch.WordTrace tailWord_4420456 prefixEnd_4420456 2269818640051262179270699 := by
  unfold tailWord_4420456
  simp only [CollatzResearch.WordTrace]
  refine ⟨80613637836725170312484611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107484850448966893749979481 80613637836725170312484611)
  ·
    refine ⟨120920456755087755468726917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80613637836725170312484611 120920456755087755468726917)
    ·
      refine ⟨22672585641578954150386297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120920456755087755468726917 22672585641578954150386297)
      ·
        refine ⟨17004439231184215612789723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22672585641578954150386297 17004439231184215612789723)
        ·
          refine ⟨25506658846776323419184585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17004439231184215612789723 25506658846776323419184585)
          ·
            refine ⟨19129994135082242564388439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25506658846776323419184585 19129994135082242564388439)
            ·
              refine ⟨28694991202623363846582659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19129994135082242564388439 28694991202623363846582659)
              ·
                refine ⟨43042486803935045769873989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28694991202623363846582659 43042486803935045769873989)
                ·
                  refine ⟨8070466275737821081851373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43042486803935045769873989 8070466275737821081851373)
                  ·
                    refine ⟨3026424853401682905694265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8070466275737821081851373 3026424853401682905694265)
                    ·
                      refine ⟨2269818640051262179270699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026424853401682905694265 2269818640051262179270699)
                      ·
                        rfl

theorem cell23_4420456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4420456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420456 prefixEnd_4420456 := by exact prefixLift 4420456
  have htrace : WordTrace (prefixWord ++ tailWord_4420456) baseStart_4420456 baseEnd_4420456 := by
    simpa [prefixWord, tailWord_4420456, baseEnd_4420456] using wordTrace_append hprefix tailTrace_4420456
  have hstable : (prefixWord ++ tailWord_4420456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420456).length < 2 ^ (prefixWord ++ tailWord_4420456).sum := by decide
  have hdescent : baseEnd_4420456 < baseStart_4420456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420472 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_4420472 : Nat := 118140960795 + 4420472 * 2 ^ 59
def prefixEnd_4420472 : Nat := 4983230072969 + 3 ^ 40 * 4420472 * 2
def baseEnd_4420472 : Nat := 2269826855741734116670625

theorem tailTrace_4420472 : CollatzResearch.WordTrace tailWord_4420472 prefixEnd_4420472 2269826855741734116670625 := by
  unfold tailWord_4420472
  simp only [CollatzResearch.WordTrace]
  refine ⟨80613929620696187678775835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107485239494261583571701113 80613929620696187678775835)
  ·
    refine ⟨120920894431044281518163753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80613929620696187678775835 120920894431044281518163753)
    ·
      refine ⟨90690670823283211138622815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120920894431044281518163753 90690670823283211138622815)
      ·
        refine ⟨136036006234924816707934223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90690670823283211138622815 136036006234924816707934223)
        ·
          refine ⟨204054009352387225061901335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136036006234924816707934223 204054009352387225061901335)
          ·
            refine ⟨306081014028580837592852003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204054009352387225061901335 306081014028580837592852003)
            ·
              refine ⟨459121521042871256389278005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306081014028580837592852003 459121521042871256389278005)
              ·
                refine ⟨43042642597769180286494813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459121521042871256389278005 43042642597769180286494813)
                ·
                  refine ⟨16140990974163442607435555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43042642597769180286494813 16140990974163442607435555)
                  ·
                    refine ⟨24211486461245163911153333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16140990974163442607435555 24211486461245163911153333)
                    ·
                      refine ⟨2269826855741734116670625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24211486461245163911153333 2269826855741734116670625)
                      ·
                        rfl

theorem cell23_4420472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_4420472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420472 prefixEnd_4420472 := by exact prefixLift 4420472
  have htrace : WordTrace (prefixWord ++ tailWord_4420472) baseStart_4420472 baseEnd_4420472 := by
    simpa [prefixWord, tailWord_4420472, baseEnd_4420472] using wordTrace_append hprefix tailTrace_4420472
  have hstable : (prefixWord ++ tailWord_4420472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420472).length < 2 ^ (prefixWord ++ tailWord_4420472).sum := by decide
  have hdescent : baseEnd_4420472 < baseStart_4420472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420492 : List Nat := [2, 2, 1, 2, 1, 2, 4, 9]
def baseStart_4420492 : Nat := 118140960795 + 4420492 * 2 ^ 59
def prefixEnd_4420492 : Nat := 4983230072969 + 3 ^ 40 * 4420492 * 2
def baseEnd_4420492 : Nat := 84068041679808297719279

theorem tailTrace_4420492 : CollatzResearch.WordTrace tailWord_4420492 prefixEnd_4420492 84068041679808297719279 := by
  unfold tailWord_4420492
  simp only [CollatzResearch.WordTrace]
  refine ⟨80614294350659959386639865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107485725800879945848853153 80614294350659959386639865)
  ·
    refine ⟨60460720762994969539979899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80614294350659959386639865 60460720762994969539979899)
    ·
      refine ⟨90691081144492454309969849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60460720762994969539979899 90691081144492454309969849)
      ·
        refine ⟨68018310858369340732477387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90691081144492454309969849 68018310858369340732477387)
        ·
          refine ⟨102027466287554011098716081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68018310858369340732477387 102027466287554011098716081)
          ·
            refine ⟨76520599715665508324037061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102027466287554011098716081 76520599715665508324037061)
            ·
              refine ⟨14347612446687282810756949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76520599715665508324037061 14347612446687282810756949)
              ·
                refine ⟨84068041679808297719279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14347612446687282810756949 84068041679808297719279)
                ·
                  rfl

theorem cell23_4420492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 9].length) (baseStart_4420492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420492 prefixEnd_4420492 := by exact prefixLift 4420492
  have htrace : WordTrace (prefixWord ++ tailWord_4420492) baseStart_4420492 baseEnd_4420492 := by
    simpa [prefixWord, tailWord_4420492, baseEnd_4420492] using wordTrace_append hprefix tailTrace_4420492
  have hstable : (prefixWord ++ tailWord_4420492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420492).length < 2 ^ (prefixWord ++ tailWord_4420492).sum := by decide
  have hdescent : baseEnd_4420492 < baseStart_4420492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420513 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_4420513 : Nat := 118140960795 + 4420513 * 2 ^ 59
def prefixEnd_4420513 : Nat := 4983230072969 + 3 ^ 40 * 4420513 * 2
def baseEnd_4420513 : Nat := 756615969482856152085979

theorem tailTrace_4420513 : CollatzResearch.WordTrace tailWord_4420513 prefixEnd_4420513 756615969482856152085979 := by
  unfold tailWord_4420513
  simp only [CollatzResearch.WordTrace]
  refine ⟨161229354634243839359794193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107486236422829226239862795 161229354634243839359794193)
  ·
    refine ⟨120922015975682879519845645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161229354634243839359794193 120922015975682879519845645)
    ·
      refine ⟨45345755990881079819942117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120922015975682879519845645 45345755990881079819942117)
      ·
        refine ⟨8502329248290202466239147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45345755990881079819942117 8502329248290202466239147)
        ·
          refine ⟨12753493872435303699358721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502329248290202466239147 12753493872435303699358721)
          ·
            refine ⟨9565120404326477774519041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12753493872435303699358721 9565120404326477774519041)
            ·
              refine ⟨7173840303244858330889281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9565120404326477774519041 7173840303244858330889281)
              ·
                refine ⟨5380380227433643748166961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7173840303244858330889281 5380380227433643748166961)
                ·
                  refine ⟨4035285170575232811125221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5380380227433643748166961 4035285170575232811125221)
                  ·
                    refine ⟨756615969482856152085979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4035285170575232811125221 756615969482856152085979)
                    ·
                      rfl

theorem cell23_4420513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_4420513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420513 prefixEnd_4420513 := by exact prefixLift 4420513
  have htrace : WordTrace (prefixWord ++ tailWord_4420513) baseStart_4420513 baseEnd_4420513 := by
    simpa [prefixWord, tailWord_4420513, baseEnd_4420513] using wordTrace_append hprefix tailTrace_4420513
  have hstable : (prefixWord ++ tailWord_4420513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420513).length < 2 ^ (prefixWord ++ tailWord_4420513).sum := by decide
  have hdescent : baseEnd_4420513 < baseStart_4420513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420536 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_4420536 : Nat := 118140960795 + 4420536 * 2 ^ 59
def prefixEnd_4420536 : Nat := 4983230072969 + 3 ^ 40 * 4420536 * 2
def baseEnd_4420536 : Nat := 2269859718503621866270331

theorem tailTrace_4420536 : CollatzResearch.WordTrace tailWord_4420536 prefixEnd_4420536 2269859718503621866270331 := by
  unfold tailWord_4420536
  simp only [CollatzResearch.WordTrace]
  refine ⟨80615096756580257143940731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107486795675440342858587641 80615096756580257143940731)
  ·
    refine ⟨120922645134870385715911097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80615096756580257143940731 120922645134870385715911097)
    ·
      refine ⟨90691983851152789286933323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120922645134870385715911097 90691983851152789286933323)
      ·
        refine ⟨136037975776729183930399985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90691983851152789286933323 136037975776729183930399985)
        ·
          refine ⟨102028481832546887947799989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136037975776729183930399985 102028481832546887947799989)
          ·
            refine ⟨9565170171801270745106249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102028481832546887947799989 9565170171801270745106249)
            ·
              refine ⟨7173877628850953058829687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9565170171801270745106249 7173877628850953058829687)
              ·
                refine ⟨10760816443276429588244531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7173877628850953058829687 10760816443276429588244531)
                ·
                  refine ⟨16141224664914644382366797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10760816443276429588244531 16141224664914644382366797)
                  ·
                    refine ⟨6052959249342991643387549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16141224664914644382366797 6052959249342991643387549)
                    ·
                      refine ⟨2269859718503621866270331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6052959249342991643387549 2269859718503621866270331)
                      ·
                        rfl

theorem cell23_4420536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_4420536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420536 prefixEnd_4420536 := by exact prefixLift 4420536
  have htrace : WordTrace (prefixWord ++ tailWord_4420536) baseStart_4420536 baseEnd_4420536 := by
    simpa [prefixWord, tailWord_4420536, baseEnd_4420536] using wordTrace_append hprefix tailTrace_4420536
  have hstable : (prefixWord ++ tailWord_4420536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420536).length < 2 ^ (prefixWord ++ tailWord_4420536).sum := by decide
  have hdescent : baseEnd_4420536 < baseStart_4420536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420569 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_4420569 : Nat := 118140960795 + 4420569 * 2 ^ 59
def prefixEnd_4420569 : Nat := 4983230072969 + 3 ^ 40 * 4420569 * 2
def baseEnd_4420569 : Nat := 756625554455073412385893

theorem tailTrace_4420569 : CollatzResearch.WordTrace tailWord_4420569 prefixEnd_4420569 756625554455073412385893 := by
  unfold tailWord_4420569
  simp only [CollatzResearch.WordTrace]
  refine ⟨161231397122040960923832761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107487598081360640615888507 161231397122040960923832761)
  ·
    refine ⟨120923547841530720692874571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161231397122040960923832761 120923547841530720692874571)
    ·
      refine ⟨181385321762296081039311857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120923547841530720692874571 181385321762296081039311857)
      ·
        refine ⟨136038991321722060779483893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181385321762296081039311857 136038991321722060779483893)
        ·
          refine ⟨12753655436411443198076615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136038991321722060779483893 12753655436411443198076615)
          ·
            refine ⟨19130483154617164797114923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12753655436411443198076615 19130483154617164797114923)
            ·
              refine ⟨28695724731925747195672385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19130483154617164797114923 28695724731925747195672385)
              ·
                refine ⟨21521793548944310396754289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28695724731925747195672385 21521793548944310396754289)
                ·
                  refine ⟨16141345161708232797565717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21521793548944310396754289 16141345161708232797565717)
                  ·
                    refine ⟨756625554455073412385893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16141345161708232797565717 756625554455073412385893)
                    ·
                      rfl

theorem cell23_4420569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_4420569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420569 prefixEnd_4420569 := by exact prefixLift 4420569
  have htrace : WordTrace (prefixWord ++ tailWord_4420569) baseStart_4420569 baseEnd_4420569 := by
    simpa [prefixWord, tailWord_4420569, baseEnd_4420569] using wordTrace_append hprefix tailTrace_4420569
  have hstable : (prefixWord ++ tailWord_4420569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420569).length < 2 ^ (prefixWord ++ tailWord_4420569).sum := by decide
  have hdescent : baseEnd_4420569 < baseStart_4420569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420570 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_4420570 : Nat := 118140960795 + 4420570 * 2 ^ 59
def prefixEnd_4420570 : Nat := 4983230072969 + 3 ^ 40 * 4420570 * 2
def baseEnd_4420570 : Nat := 2269877176845874733245175

theorem tailTrace_4420570 : CollatzResearch.WordTrace tailWord_4420570 prefixEnd_4420570 2269877176845874733245175 := by
  unfold tailWord_4420570
  simp only [CollatzResearch.WordTrace]
  refine ⟨40307858398759334523654791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107487622396691558729746109 40307858398759334523654791)
  ·
    refine ⟨60461787598139001785482187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40307858398759334523654791 60461787598139001785482187)
    ·
      refine ⟨90692681397208502678223281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60461787598139001785482187 90692681397208502678223281)
      ·
        refine ⟨68019511047906377008667461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90692681397208502678223281 68019511047906377008667461)
        ·
          refine ⟨12753658321482445689125149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68019511047906377008667461 12753658321482445689125149)
          ·
            refine ⟨4782621870555917133421931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12753658321482445689125149 4782621870555917133421931)
            ·
              refine ⟨7173932805833875700132897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4782621870555917133421931 7173932805833875700132897)
              ·
                refine ⟨5380449604375406775099673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7173932805833875700132897 5380449604375406775099673)
                ·
                  refine ⟨4035337203281555081324755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5380449604375406775099673 4035337203281555081324755)
                  ·
                    refine ⟨6053005804922332621987133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035337203281555081324755 6053005804922332621987133)
                    ·
                      refine ⟨2269877176845874733245175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053005804922332621987133 2269877176845874733245175)
                      ·
                        rfl

theorem cell23_4420570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_4420570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420570 prefixEnd_4420570 := by exact prefixLift 4420570
  have htrace : WordTrace (prefixWord ++ tailWord_4420570) baseStart_4420570 baseEnd_4420570 := by
    simpa [prefixWord, tailWord_4420570, baseEnd_4420570] using wordTrace_append hprefix tailTrace_4420570
  have hstable : (prefixWord ++ tailWord_4420570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420570).length < 2 ^ (prefixWord ++ tailWord_4420570).sum := by decide
  have hdescent : baseEnd_4420570 < baseStart_4420570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420593 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_4420593 : Nat := 118140960795 + 4420593 * 2 ^ 59
def prefixEnd_4420593 : Nat := 4983230072969 + 3 ^ 40 * 4420593 * 2
def baseEnd_4420593 : Nat := 2269888986900928143257569

theorem tailTrace_4420593 : CollatzResearch.WordTrace tailWord_4420593 prefixEnd_4420593 2269888986900928143257569 := by
  unfold tailWord_4420593
  simp only [CollatzResearch.WordTrace]
  refine ⟨161232272473954013022706433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107488181649302675348470955 161232272473954013022706433)
  ·
    refine ⟨120924204355465509767029825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161232272473954013022706433 120924204355465509767029825)
    ·
      refine ⟨90693153266599132325272369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120924204355465509767029825 90693153266599132325272369)
      ·
        refine ⟨68019864949949349243954277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90693153266599132325272369 68019864949949349243954277)
        ·
          refine ⟨12753724678115502983241427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68019864949949349243954277 12753724678115502983241427)
          ·
            refine ⟨19130587017173254474862141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12753724678115502983241427 19130587017173254474862141)
            ·
              refine ⟨7173970131439970428073303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19130587017173254474862141 7173970131439970428073303)
              ·
                refine ⟨10760955197159955642109955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7173970131439970428073303 10760955197159955642109955)
                ·
                  refine ⟨16141432795739933463164933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10760955197159955642109955 16141432795739933463164933)
                  ·
                    refine ⟨3026518649201237524343425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16141432795739933463164933 3026518649201237524343425)
                    ·
                      refine ⟨2269888986900928143257569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026518649201237524343425 2269888986900928143257569)
                      ·
                        rfl

theorem cell23_4420593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_4420593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420593 prefixEnd_4420593 := by exact prefixLift 4420593
  have htrace : WordTrace (prefixWord ++ tailWord_4420593) baseStart_4420593 baseEnd_4420593 := by
    simpa [prefixWord, tailWord_4420593, baseEnd_4420593] using wordTrace_append hprefix tailTrace_4420593
  have hstable : (prefixWord ++ tailWord_4420593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420593).length < 2 ^ (prefixWord ++ tailWord_4420593).sum := by decide
  have hdescent : baseEnd_4420593 < baseStart_4420593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420639 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_4420639 : Nat := 118140960795 + 4420639 * 2 ^ 59
def prefixEnd_4420639 : Nat := 4983230072969 + 3 ^ 40 * 4420639 * 2
def baseEnd_4420639 : Nat := 2269912607011034963282357

theorem tailTrace_4420639 : CollatzResearch.WordTrace tailWord_4420639 prefixEnd_4420639 2269912607011034963282357 := by
  unfold tailWord_4420639
  simp only [CollatzResearch.WordTrace]
  refine ⟨161233950231787362878880971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107489300154524908585920647 161233950231787362878880971)
  ·
    refine ⟨241850925347681044318321457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161233950231787362878880971 241850925347681044318321457)
    ·
      refine ⟨181388194010760783238741093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241850925347681044318321457 181388194010760783238741093)
      ·
        refine ⟨34010286377017646857263955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181388194010760783238741093 34010286377017646857263955)
        ·
          refine ⟨51015429565526470285895933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34010286377017646857263955 51015429565526470285895933)
          ·
            refine ⟨19130786087072426357210975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51015429565526470285895933 19130786087072426357210975)
            ·
              refine ⟨28696179130608639535816463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19130786087072426357210975 28696179130608639535816463)
              ·
                refine ⟨43044268695912959303724695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28696179130608639535816463 43044268695912959303724695)
                ·
                  refine ⟨64566403043869438955587043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43044268695912959303724695 64566403043869438955587043)
                  ·
                    refine ⟨96849604565804158433380565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64566403043869438955587043 96849604565804158433380565)
                    ·
                      refine ⟨2269912607011034963282357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96849604565804158433380565 2269912607011034963282357)
                      ·
                        rfl

theorem cell23_4420639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_4420639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420639 prefixEnd_4420639 := by exact prefixLift 4420639
  have htrace : WordTrace (prefixWord ++ tailWord_4420639) baseStart_4420639 baseEnd_4420639 := by
    simpa [prefixWord, tailWord_4420639, baseEnd_4420639] using wordTrace_append hprefix tailTrace_4420639
  have hstable : (prefixWord ++ tailWord_4420639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420639).length < 2 ^ (prefixWord ++ tailWord_4420639).sum := by decide
  have hdescent : baseEnd_4420639 < baseStart_4420639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420644 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4420644 : Nat := 118140960795 + 4420644 * 2 ^ 59
def prefixEnd_4420644 : Nat := 4983230072969 + 3 ^ 40 * 4420644 * 2
def baseEnd_4420644 : Nat := 2269915174414307443719835

theorem tailTrace_4420644 : CollatzResearch.WordTrace tailWord_4420644 prefixEnd_4420644 2269915174414307443719835 := by
  unfold tailWord_4420644
  simp only [CollatzResearch.WordTrace]
  refine ⟨80617066298384624366406493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107489421731179499155208657 80617066298384624366406493)
  ·
    refine ⟨30231399861894234137402435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80617066298384624366406493 30231399861894234137402435)
    ·
      refine ⟨45347099792841351206103653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30231399861894234137402435 45347099792841351206103653)
      ·
        refine ⟨8502581211157753351144435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45347099792841351206103653 8502581211157753351144435)
        ·
          refine ⟨12753871816736630026716653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502581211157753351144435 12753871816736630026716653)
          ·
            refine ⟨4782701931276236260018745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12753871816736630026716653 4782701931276236260018745)
            ·
              refine ⟨3587026448457177195014059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782701931276236260018745 3587026448457177195014059)
              ·
                refine ⟨5380539672685765792521089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587026448457177195014059 5380539672685765792521089)
                ·
                  refine ⟨4035404754514324344390817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5380539672685765792521089 4035404754514324344390817)
                  ·
                    refine ⟨3026553565885743258293113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4035404754514324344390817 3026553565885743258293113)
                    ·
                      refine ⟨2269915174414307443719835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026553565885743258293113 2269915174414307443719835)
                      ·
                        rfl

theorem cell23_4420644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4420644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420644 prefixEnd_4420644 := by exact prefixLift 4420644
  have htrace : WordTrace (prefixWord ++ tailWord_4420644) baseStart_4420644 baseEnd_4420644 := by
    simpa [prefixWord, tailWord_4420644, baseEnd_4420644] using wordTrace_append hprefix tailTrace_4420644
  have hstable : (prefixWord ++ tailWord_4420644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420644).length < 2 ^ (prefixWord ++ tailWord_4420644).sum := by decide
  have hdescent : baseEnd_4420644 < baseStart_4420644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420666 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_4420666 : Nat := 118140960795 + 4420666 * 2 ^ 59
def prefixEnd_4420666 : Nat := 4983230072969 + 3 ^ 40 * 4420666 * 2
def baseEnd_4420666 : Nat := 2269926470988706357644733

theorem tailTrace_4420666 : CollatzResearch.WordTrace tailWord_4420666 prefixEnd_4420666 2269926470988706357644733 := by
  unfold tailWord_4420666
  simp only [CollatzResearch.WordTrace]
  refine ⟨40308733750672386622528463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107489956668459697660075901 40308733750672386622528463)
  ·
    refine ⟨60463100626008579933792695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40308733750672386622528463 60463100626008579933792695)
    ·
      refine ⟨90694650939012869900689043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60463100626008579933792695 90694650939012869900689043)
      ·
        refine ⟨136041976408519304851033565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90694650939012869900689043 136041976408519304851033565)
        ·
          refine ⟨51015741153194739319137587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136041976408519304851033565 51015741153194739319137587)
          ·
            refine ⟨76523611729792108978706381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51015741153194739319137587 76523611729792108978706381)
            ·
              refine ⟨28696354398672040867014893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76523611729792108978706381 28696354398672040867014893)
              ·
                refine ⟨10761132899502015325130585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28696354398672040867014893 10761132899502015325130585)
                ·
                  refine ⟨8070849674626511493847939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10761132899502015325130585 8070849674626511493847939)
                  ·
                    refine ⟨12106274511939767240771909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8070849674626511493847939 12106274511939767240771909)
                    ·
                      refine ⟨2269926470988706357644733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12106274511939767240771909 2269926470988706357644733)
                      ·
                        rfl

theorem cell23_4420666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_4420666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420666 prefixEnd_4420666 := by exact prefixLift 4420666
  have htrace : WordTrace (prefixWord ++ tailWord_4420666) baseStart_4420666 baseEnd_4420666 := by
    simpa [prefixWord, tailWord_4420666, baseEnd_4420666] using wordTrace_append hprefix tailTrace_4420666
  have hstable : (prefixWord ++ tailWord_4420666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420666).length < 2 ^ (prefixWord ++ tailWord_4420666).sum := by decide
  have hdescent : baseEnd_4420666 < baseStart_4420666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420689 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 8]
def baseStart_4420689 : Nat := 118140960795 + 4420689 * 2 ^ 59
def prefixEnd_4420689 : Nat := 4983230072969 + 3 ^ 40 * 4420689 * 2
def baseEnd_4420689 : Nat := 252215364560417751961903

theorem tailTrace_4420689 : CollatzResearch.WordTrace tailWord_4420689 prefixEnd_4420689 252215364560417751961903 := by
  unfold tailWord_4420689
  simp only [CollatzResearch.WordTrace]
  refine ⟨161235773881606221418201121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107490515921070814278800747 161235773881606221418201121)
  ·
    refine ⟨120926830411204666063650841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161235773881606221418201121 120926830411204666063650841)
    ·
      refine ⟨90695122808403499547738131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120926830411204666063650841 90695122808403499547738131)
      ·
        refine ⟨136042684212605249321607197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90695122808403499547738131 136042684212605249321607197)
        ·
          refine ⟨51016006579726968495602699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136042684212605249321607197 51016006579726968495602699)
          ·
            refine ⟨76524009869590452743404049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51016006579726968495602699 76524009869590452743404049)
            ·
              refine ⟨57393007402192839557553037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76524009869590452743404049 57393007402192839557553037)
              ·
                refine ⟨21522377775822314834082389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57393007402192839557553037 21522377775822314834082389)
                ·
                  refine ⟨252215364560417751961903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21522377775822314834082389 252215364560417751961903)
                  ·
                    rfl

theorem cell23_4420689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_4420689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420689 prefixEnd_4420689 := by exact prefixLift 4420689
  have htrace : WordTrace (prefixWord ++ tailWord_4420689) baseStart_4420689 baseEnd_4420689 := by
    simpa [prefixWord, tailWord_4420689, baseEnd_4420689] using wordTrace_append hprefix tailTrace_4420689
  have hstable : (prefixWord ++ tailWord_4420689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420689).length < 2 ^ (prefixWord ++ tailWord_4420689).sum := by decide
  have hdescent : baseEnd_4420689 < baseStart_4420689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420733 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_4420733 : Nat := 118140960795 + 4420733 * 2 ^ 59
def prefixEnd_4420733 : Nat := 4983230072969 + 3 ^ 40 * 4420733 * 2
def baseEnd_4420733 : Nat := 2269960874192557595506925

theorem tailTrace_4420733 : CollatzResearch.WordTrace tailWord_4420733 prefixEnd_4420733 2269960874192557595506925 := by
  unfold tailWord_4420733
  simp only [CollatzResearch.WordTrace]
  refine ⟨161237378693446816932802853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107491585795631211288535235 161237378693446816932802853)
  ·
    refine ⟨30232008505021278174900535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161237378693446816932802853 30232008505021278174900535)
    ·
      refine ⟨45348012757531917262350803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30232008505021278174900535 45348012757531917262350803)
      ·
        refine ⟨68022019136297875893526205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45348012757531917262350803 68022019136297875893526205)
        ·
          refine ⟨25508257176111703460072327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68022019136297875893526205 25508257176111703460072327)
          ·
            refine ⟨38262385764167555190108491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25508257176111703460072327 38262385764167555190108491)
            ·
              refine ⟨57393578646251332785162737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38262385764167555190108491 57393578646251332785162737)
              ·
                refine ⟨43045183984688499588872053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57393578646251332785162737 43045183984688499588872053)
                ·
                  refine ⟨4035485998564546836456755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43045183984688499588872053 4035485998564546836456755)
                  ·
                    refine ⟨6053228997846820254685133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035485998564546836456755 6053228997846820254685133)
                    ·
                      refine ⟨2269960874192557595506925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053228997846820254685133 2269960874192557595506925)
                      ·
                        rfl

theorem cell23_4420733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_4420733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420733 prefixEnd_4420733 := by exact prefixLift 4420733
  have htrace : WordTrace (prefixWord ++ tailWord_4420733) baseStart_4420733 baseEnd_4420733 := by
    simpa [prefixWord, tailWord_4420733, baseEnd_4420733] using wordTrace_append hprefix tailTrace_4420733
  have hstable : (prefixWord ++ tailWord_4420733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420733).length < 2 ^ (prefixWord ++ tailWord_4420733).sum := by decide
  have hdescent : baseEnd_4420733 < baseStart_4420733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420743 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_4420743 : Nat := 118140960795 + 4420743 * 2 ^ 59
def prefixEnd_4420743 : Nat := 4983230072969 + 3 ^ 40 * 4420743 * 2
def baseEnd_4420743 : Nat := 2269966008999102556381879

theorem tailTrace_4420743 : CollatzResearch.WordTrace tailWord_4420743 prefixEnd_4420743 2269966008999102556381879 := by
  unfold tailWord_4420743
  simp only [CollatzResearch.WordTrace]
  refine ⟨161237743423410588640666883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107491828948940392427111255 161237743423410588640666883)
  ·
    refine ⟨241856615135115882961000325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161237743423410588640666883 241856615135115882961000325)
    ·
      refine ⟨45348115337834228055187561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241856615135115882961000325 45348115337834228055187561)
      ·
        refine ⟨34011086503375671041390671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45348115337834228055187561 34011086503375671041390671)
        ·
          refine ⟨51016629755063506562086007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34011086503375671041390671 51016629755063506562086007)
          ·
            refine ⟨76524944632595259843129011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51016629755063506562086007 76524944632595259843129011)
            ·
              refine ⟨114787416948892889764693517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76524944632595259843129011 114787416948892889764693517)
              ·
                refine ⟨43045281355834833661760069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114787416948892889764693517 43045281355834833661760069)
                ·
                  refine ⟨8070990254219031311580013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43045281355834833661760069 8070990254219031311580013)
                  ·
                    refine ⟨3026621345332136741842505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8070990254219031311580013 3026621345332136741842505)
                    ·
                      refine ⟨2269966008999102556381879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026621345332136741842505 2269966008999102556381879)
                      ·
                        rfl

theorem cell23_4420743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_4420743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420743 prefixEnd_4420743 := by exact prefixLift 4420743
  have htrace : WordTrace (prefixWord ++ tailWord_4420743) baseStart_4420743 baseEnd_4420743 := by
    simpa [prefixWord, tailWord_4420743, baseEnd_4420743] using wordTrace_append hprefix tailTrace_4420743
  have hstable : (prefixWord ++ tailWord_4420743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420743).length < 2 ^ (prefixWord ++ tailWord_4420743).sum := by decide
  have hdescent : baseEnd_4420743 < baseStart_4420743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420750 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4420750 : Nat := 118140960795 + 4420750 * 2 ^ 59
def prefixEnd_4420750 : Nat := 4983230072969 + 3 ^ 40 * 4420750 * 2
def baseEnd_4420750 : Nat := 2269969603363684028994347

theorem tailTrace_4420750 : CollatzResearch.WordTrace tailWord_4420750 prefixEnd_4420750 2269969603363684028994347 := by
  unfold tailWord_4420750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20154749841798153604521463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107491999156256819224114469 20154749841798153604521463)
  ·
    refine ⟨30232124762697230406782195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20154749841798153604521463 30232124762697230406782195)
    ·
      refine ⟨45348187144045845610173293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30232124762697230406782195 45348187144045845610173293)
      ·
        refine ⟨17005570179017192103814985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45348187144045845610173293 17005570179017192103814985)
        ·
          refine ⟨12754177634262894077861239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17005570179017192103814985 12754177634262894077861239)
          ·
            refine ⟨19131266451394341116791859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12754177634262894077861239 19131266451394341116791859)
            ·
              refine ⟨28696899677091511675187789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19131266451394341116791859 28696899677091511675187789)
              ·
                refine ⟨10761337378909316878195421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28696899677091511675187789 10761337378909316878195421)
                ·
                  refine ⟨4035501517090993829323283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10761337378909316878195421 4035501517090993829323283)
                  ·
                    refine ⟨6053252275636490743984925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035501517090993829323283 6053252275636490743984925)
                    ·
                      refine ⟨2269969603363684028994347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053252275636490743984925 2269969603363684028994347)
                      ·
                        rfl

theorem cell23_4420750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4420750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420750 prefixEnd_4420750 := by exact prefixLift 4420750
  have htrace : WordTrace (prefixWord ++ tailWord_4420750) baseStart_4420750 baseEnd_4420750 := by
    simpa [prefixWord, tailWord_4420750, baseEnd_4420750] using wordTrace_append hprefix tailTrace_4420750
  have hstable : (prefixWord ++ tailWord_4420750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420750).length < 2 ^ (prefixWord ++ tailWord_4420750).sum := by decide
  have hdescent : baseEnd_4420750 < baseStart_4420750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420773 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_4420773 : Nat := 118140960795 + 4420773 * 2 ^ 59
def prefixEnd_4420773 : Nat := 4983230072969 + 3 ^ 40 * 4420773 * 2
def baseEnd_4420773 : Nat := 2269981413418737439006741

theorem tailTrace_4420773 : CollatzResearch.WordTrace tailWord_4420773 prefixEnd_4420773 2269981413418737439006741 := by
  unfold tailWord_4420773
  simp only [CollatzResearch.WordTrace]
  refine ⟨161238837613301903764258973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107492558408867935842839315 161238837613301903764258973)
  ·
    refine ⟨60464564104988213911597115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161238837613301903764258973 60464564104988213911597115)
    ·
      refine ⟨90696846157482320867395673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60464564104988213911597115 90696846157482320867395673)
      ·
        refine ⟨68022634618111740650546755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90696846157482320867395673 68022634618111740650546755)
        ·
          refine ⟨102033951927167610975820133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68022634618111740650546755 102033951927167610975820133)
          ·
            refine ⟨19131365986343927057966275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102033951927167610975820133 19131365986343927057966275)
            ·
              refine ⟨28697048979515890586949413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19131365986343927057966275 28697048979515890586949413)
              ·
                refine ⟨5380696683659229485053015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28697048979515890586949413 5380696683659229485053015)
                ·
                  refine ⟨8071045025488844227579523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5380696683659229485053015 8071045025488844227579523)
                  ·
                    refine ⟨12106567538233266341369285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8071045025488844227579523 12106567538233266341369285)
                    ·
                      refine ⟨2269981413418737439006741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12106567538233266341369285 2269981413418737439006741)
                      ·
                        rfl

theorem cell23_4420773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_4420773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420773 prefixEnd_4420773 := by exact prefixLift 4420773
  have htrace : WordTrace (prefixWord ++ tailWord_4420773) baseStart_4420773 baseEnd_4420773 := by
    simpa [prefixWord, tailWord_4420773, baseEnd_4420773] using wordTrace_append hprefix tailTrace_4420773
  have hstable : (prefixWord ++ tailWord_4420773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420773).length < 2 ^ (prefixWord ++ tailWord_4420773).sum := by decide
  have hdescent : baseEnd_4420773 < baseStart_4420773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420793 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4420793 : Nat := 118140960795 + 4420793 * 2 ^ 59
def prefixEnd_4420793 : Nat := 4983230072969 + 3 ^ 40 * 4420793 * 2
def baseEnd_4420793 : Nat := 2269991683031827360756649

theorem tailTrace_4420793 : CollatzResearch.WordTrace tailWord_4420793 prefixEnd_4420793 2269991683031827360756649 := by
  unfold tailWord_4420793
  simp only [CollatzResearch.WordTrace]
  refine ⟨161239567073229447179987033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107493044715486298119991355 161239567073229447179987033)
  ·
    refine ⟨120929675304922085384990275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161239567073229447179987033 120929675304922085384990275)
    ·
      refine ⟨181394512957383128077485413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120929675304922085384990275 181394512957383128077485413)
      ·
        refine ⟨34011471179509336514528515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181394512957383128077485413 34011471179509336514528515)
        ·
          refine ⟨51017206769264004771792773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34011471179509336514528515 51017206769264004771792773)
          ·
            refine ⟨9565726269237000894711145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51017206769264004771792773 9565726269237000894711145)
            ·
              refine ⟨7174294701927750671033359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9565726269237000894711145 7174294701927750671033359)
              ·
                refine ⟨10761442052891626006550039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7174294701927750671033359 10761442052891626006550039)
                ·
                  refine ⟨16142163079337439009825059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10761442052891626006550039 16142163079337439009825059)
                  ·
                    refine ⟨24213244619006158514737589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16142163079337439009825059 24213244619006158514737589)
                    ·
                      refine ⟨2269991683031827360756649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24213244619006158514737589 2269991683031827360756649)
                      ·
                        rfl

theorem cell23_4420793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4420793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420793 prefixEnd_4420793 := by exact prefixLift 4420793
  have htrace : WordTrace (prefixWord ++ tailWord_4420793) baseStart_4420793 baseEnd_4420793 := by
    simpa [prefixWord, tailWord_4420793, baseEnd_4420793] using wordTrace_append hprefix tailTrace_4420793
  have hstable : (prefixWord ++ tailWord_4420793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420793).length < 2 ^ (prefixWord ++ tailWord_4420793).sum := by decide
  have hdescent : baseEnd_4420793 < baseStart_4420793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420796 : List Nat := [2, 2, 2, 3, 2, 1, 11]
def baseStart_4420796 : Nat := 118140960795 + 4420796 * 2 ^ 59
def prefixEnd_4420796 : Nat := 4983230072969 + 3 ^ 40 * 4420796 * 2
def baseEnd_4420796 : Nat := 28024607697207294432335

theorem tailTrace_4420796 : CollatzResearch.WordTrace tailWord_4420796 prefixEnd_4420796 28024607697207294432335 := by
  unfold tailWord_4420796
  simp only [CollatzResearch.WordTrace]
  refine ⟨80619838246109289346173121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107493117661479052461564161 80619838246109289346173121)
  ·
    refine ⟨60464878684581967009629841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80619838246109289346173121 60464878684581967009629841)
    ·
      refine ⟨45348659013436475257222381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60464878684581967009629841 45348659013436475257222381)
      ·
        refine ⟨17005747130038678221458393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45348659013436475257222381 17005747130038678221458393)
        ·
          refine ⟨12754310347529008666093795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17005747130038678221458393 12754310347529008666093795)
          ·
            refine ⟨19131465521293512999140693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12754310347529008666093795 19131465521293512999140693)
            ·
              refine ⟨28024607697207294432335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19131465521293512999140693 28024607697207294432335)
              ·
                rfl

theorem cell23_4420796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 11].length) (baseStart_4420796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420796 prefixEnd_4420796 := by exact prefixLift 4420796
  have htrace : WordTrace (prefixWord ++ tailWord_4420796) baseStart_4420796 baseEnd_4420796 := by
    simpa [prefixWord, tailWord_4420796, baseEnd_4420796] using wordTrace_append hprefix tailTrace_4420796
  have hstable : (prefixWord ++ tailWord_4420796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420796).length < 2 ^ (prefixWord ++ tailWord_4420796).sum := by decide
  have hdescent : baseEnd_4420796 < baseStart_4420796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420801 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4420801 : Nat := 118140960795 + 4420801 * 2 ^ 59
def prefixEnd_4420801 : Nat := 4983230072969 + 3 ^ 40 * 4420801 * 2
def baseEnd_4420801 : Nat := 2269995790877063329456613

theorem tailTrace_4420801 : CollatzResearch.WordTrace tailWord_4420801 prefixEnd_4420801 2269995790877063329456613 := by
  unfold tailWord_4420801
  simp only [CollatzResearch.WordTrace]
  refine ⟨161239858857200464546278257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107493239238133643030852171 161239858857200464546278257)
  ·
    refine ⟨120929894142900348409708693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161239858857200464546278257 120929894142900348409708693)
    ·
      refine ⟨5668588787948453831705095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120929894142900348409708693 5668588787948453831705095)
      ·
        refine ⟨8502883181922680747557643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668588787948453831705095 8502883181922680747557643)
        ·
          refine ⟨12754324772884021121336465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502883181922680747557643 12754324772884021121336465)
          ·
            refine ⟨9565743579663015841002349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12754324772884021121336465 9565743579663015841002349)
            ·
              refine ⟨3587153842373630940375881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9565743579663015841002349 3587153842373630940375881)
              ·
                refine ⟨2690365381780223205281911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587153842373630940375881 2690365381780223205281911)
                ·
                  refine ⟨4035548072670334807922867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690365381780223205281911 4035548072670334807922867)
                  ·
                    refine ⟨6053322109005502211884301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035548072670334807922867 6053322109005502211884301)
                    ·
                      refine ⟨2269995790877063329456613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053322109005502211884301 2269995790877063329456613)
                      ·
                        rfl

theorem cell23_4420801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4420801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420801 prefixEnd_4420801 := by exact prefixLift 4420801
  have htrace : WordTrace (prefixWord ++ tailWord_4420801) baseStart_4420801 baseEnd_4420801 := by
    simpa [prefixWord, tailWord_4420801, baseEnd_4420801] using wordTrace_append hprefix tailTrace_4420801
  have hstable : (prefixWord ++ tailWord_4420801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420801).length < 2 ^ (prefixWord ++ tailWord_4420801).sum := by decide
  have hdescent : baseEnd_4420801 < baseStart_4420801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420807 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_4420807 : Nat := 118140960795 + 4420807 * 2 ^ 59
def prefixEnd_4420807 : Nat := 4983230072969 + 3 ^ 40 * 4420807 * 2
def baseEnd_4420807 : Nat := 2269998871760990305981585

theorem tailTrace_4420807 : CollatzResearch.WordTrace tailWord_4420807 prefixEnd_4420807 2269998871760990305981585 := by
  unfold tailWord_4420807
  simp only [CollatzResearch.WordTrace]
  refine ⟨161240077695178727570996675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107493385130119151713997783 161240077695178727570996675)
  ·
    refine ⟨241860116542768091356495013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161240077695178727570996675 241860116542768091356495013)
    ·
      refine ⟨45348771851769017129342815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241860116542768091356495013 45348771851769017129342815)
      ·
        refine ⟨68023157777653525694014223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45348771851769017129342815 68023157777653525694014223)
        ·
          refine ⟨102034736666480288541021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68023157777653525694014223 102034736666480288541021335)
          ·
            refine ⟨153052104999720432811532003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102034736666480288541021335 153052104999720432811532003)
            ·
              refine ⟨229578157499580649217298005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153052104999720432811532003 229578157499580649217298005)
              ·
                refine ⟨2690369033198210733015211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 229578157499580649217298005 2690369033198210733015211)
                ·
                  refine ⟨4035553549797316099522817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690369033198210733015211 4035553549797316099522817)
                  ·
                    refine ⟨3026665162347987074642113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4035553549797316099522817 3026665162347987074642113)
                    ·
                      refine ⟨2269998871760990305981585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026665162347987074642113 2269998871760990305981585)
                      ·
                        rfl

theorem cell23_4420807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_4420807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420807 prefixEnd_4420807 := by exact prefixLift 4420807
  have htrace : WordTrace (prefixWord ++ tailWord_4420807) baseStart_4420807 baseEnd_4420807 := by
    simpa [prefixWord, tailWord_4420807, baseEnd_4420807] using wordTrace_append hprefix tailTrace_4420807
  have hstable : (prefixWord ++ tailWord_4420807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420807).length < 2 ^ (prefixWord ++ tailWord_4420807).sum := by decide
  have hdescent : baseEnd_4420807 < baseStart_4420807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420836 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_4420836 : Nat := 118140960795 + 4420836 * 2 ^ 59
def prefixEnd_4420836 : Nat := 4983230072969 + 3 ^ 40 * 4420836 * 2
def baseEnd_4420836 : Nat := 2270013762699970692518951

theorem tailTrace_4420836 : CollatzResearch.WordTrace tailWord_4420836 prefixEnd_4420836 2270013762699970692518951 := by
  unfold tailWord_4420836
  simp only [CollatzResearch.WordTrace]
  refine ⟨80620567706036832761901181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107494090274715777015868241 80620567706036832761901181)
  ·
    refine ⟨30232712889763812285712943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80620567706036832761901181 30232712889763812285712943)
    ·
      refine ⟨45349069334645718428569415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30232712889763812285712943 45349069334645718428569415)
      ·
        refine ⟨68023604001968577642854123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45349069334645718428569415 68023604001968577642854123)
        ·
          refine ⟨102035406002952866464281185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68023604001968577642854123 102035406002952866464281185)
          ·
            refine ⟨76526554502214649848210889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102035406002952866464281185 76526554502214649848210889)
            ·
              refine ⟨57394915876660987386158167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76526554502214649848210889 57394915876660987386158167)
              ·
                refine ⟨86092373814991481079237251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57394915876660987386158167 86092373814991481079237251)
                ·
                  refine ⟨129138560722487221618855877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86092373814991481079237251 129138560722487221618855877)
                  ·
                    refine ⟨24213480135466354053535477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129138560722487221618855877 24213480135466354053535477)
                    ·
                      refine ⟨2270013762699970692518951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24213480135466354053535477 2270013762699970692518951)
                      ·
                        rfl

theorem cell23_4420836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4420836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420836 prefixEnd_4420836 := by exact prefixLift 4420836
  have htrace : WordTrace (prefixWord ++ tailWord_4420836) baseStart_4420836 baseEnd_4420836 := by
    simpa [prefixWord, tailWord_4420836, baseEnd_4420836] using wordTrace_append hprefix tailTrace_4420836
  have hstable : (prefixWord ++ tailWord_4420836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420836).length < 2 ^ (prefixWord ++ tailWord_4420836).sum := by decide
  have hdescent : baseEnd_4420836 < baseStart_4420836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420852 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4420852 : Nat := 118140960795 + 4420852 * 2 ^ 59
def prefixEnd_4420852 : Nat := 4983230072969 + 3 ^ 40 * 4420852 * 2
def baseEnd_4420852 : Nat := 2270021978390442629918879

theorem tailTrace_4420852 : CollatzResearch.WordTrace tailWord_4420852 prefixEnd_4420852 2270021978390442629918879 := by
  unfold tailWord_4420852
  simp only [CollatzResearch.WordTrace]
  refine ⟨80620859490007850128192405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107494479320010466837589873 80620859490007850128192405)
  ·
    refine ⟨3779102788594117974759019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80620859490007850128192405 3779102788594117974759019)
    ·
      refine ⟨5668654182891176962138529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779102788594117974759019 5668654182891176962138529)
      ·
        refine ⟨4251490637168382721603897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5668654182891176962138529 4251490637168382721603897)
        ·
          refine ⟨3188617977876287041202923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4251490637168382721603897 3188617977876287041202923)
          ·
            refine ⟨4782926966814430561804385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188617977876287041202923 4782926966814430561804385)
            ·
              refine ⟨3587195225110822921353289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782926966814430561804385 3587195225110822921353289)
              ·
                refine ⟨2690396418833117191014967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587195225110822921353289 2690396418833117191014967)
                ·
                  refine ⟨4035594628249675786522451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690396418833117191014967 4035594628249675786522451)
                  ·
                    refine ⟨6053391942374513679783677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035594628249675786522451 6053391942374513679783677)
                    ·
                      refine ⟨2270021978390442629918879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053391942374513679783677 2270021978390442629918879)
                      ·
                        rfl

theorem cell23_4420852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4420852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420852 prefixEnd_4420852 := by exact prefixLift 4420852
  have htrace : WordTrace (prefixWord ++ tailWord_4420852) baseStart_4420852 baseEnd_4420852 := by
    simpa [prefixWord, tailWord_4420852, baseEnd_4420852] using wordTrace_append hprefix tailTrace_4420852
  have hstable : (prefixWord ++ tailWord_4420852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420852).length < 2 ^ (prefixWord ++ tailWord_4420852).sum := by decide
  have hdescent : baseEnd_4420852 < baseStart_4420852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420914 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_4420914 : Nat := 118140960795 + 4420914 * 2 ^ 59
def prefixEnd_4420914 : Nat := 4983230072969 + 3 ^ 40 * 4420914 * 2
def baseEnd_4420914 : Nat := 2270053814191021387343593

theorem tailTrace_4420914 : CollatzResearch.WordTrace tailWord_4420914 prefixEnd_4420914 2270053814191021387343593 := by
  unfold tailWord_4420914
  simp only [CollatzResearch.WordTrace]
  refine ⟨40310995076447771211285449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107495986870527389896761197 40310995076447771211285449)
  ·
    refine ⟨30233246307335828408464087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40310995076447771211285449 30233246307335828408464087)
    ·
      refine ⟨45349869461003742612696131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30233246307335828408464087 45349869461003742612696131)
      ·
        refine ⟨68024804191505613919044197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45349869461003742612696131 68024804191505613919044197)
        ·
          refine ⟨12754650785907302609820787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68024804191505613919044197 12754650785907302609820787)
          ·
            refine ⟨19131976178860953914731181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12754650785907302609820787 19131976178860953914731181)
            ·
              refine ⟨7174491067072857718024193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19131976178860953914731181 7174491067072857718024193)
              ·
                refine ⟨5380868300304643288518145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7174491067072857718024193 5380868300304643288518145)
                ·
                  refine ⟨4035651225228482466388609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5380868300304643288518145 4035651225228482466388609)
                  ·
                    refine ⟨3026738418921361849791457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4035651225228482466388609 3026738418921361849791457)
                    ·
                      refine ⟨2270053814191021387343593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026738418921361849791457 2270053814191021387343593)
                      ·
                        rfl

theorem cell23_4420914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_4420914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420914 prefixEnd_4420914 := by exact prefixLift 4420914
  have htrace : WordTrace (prefixWord ++ tailWord_4420914) baseStart_4420914 baseEnd_4420914 := by
    simpa [prefixWord, tailWord_4420914, baseEnd_4420914] using wordTrace_append hprefix tailTrace_4420914
  have hstable : (prefixWord ++ tailWord_4420914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420914).length < 2 ^ (prefixWord ++ tailWord_4420914).sum := by decide
  have hdescent : baseEnd_4420914 < baseStart_4420914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4420953 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_4420953 : Nat := 118140960795 + 4420953 * 2 ^ 59
def prefixEnd_4420953 : Nat := 4983230072969 + 3 ^ 40 * 4420953 * 2
def baseEnd_4420953 : Nat := 2270073839936546734755913

theorem tailTrace_4420953 : CollatzResearch.WordTrace tailWord_4420953 prefixEnd_4420953 2270073839936546734755913 := by
  unfold tailWord_4420953
  simp only [CollatzResearch.WordTrace]
  refine ⟨161245402752649794505811513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107496935168433196337207675 161245402752649794505811513)
  ·
    refine ⟨120934052064487345879358635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161245402752649794505811513 120934052064487345879358635)
    ·
      refine ⟨181401078096731018819037953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120934052064487345879358635 181401078096731018819037953)
      ·
        refine ⟨136050808572548264114278465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181401078096731018819037953 136050808572548264114278465)
        ·
          refine ⟨102038106429411198085708849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136050808572548264114278465 102038106429411198085708849)
          ·
            refine ⟨76528579822058398564281637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102038106429411198085708849 76528579822058398564281637)
            ·
              refine ⟨14349108716635949730802807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76528579822058398564281637 14349108716635949730802807)
              ·
                refine ⟨21523663074953924596204211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14349108716635949730802807 21523663074953924596204211)
                ·
                  refine ⟨32285494612430886894306317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21523663074953924596204211 32285494612430886894306317)
                  ·
                    refine ⟨12107060479661582585364869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32285494612430886894306317 12107060479661582585364869)
                    ·
                      refine ⟨2270073839936546734755913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12107060479661582585364869 2270073839936546734755913)
                      ·
                        rfl

theorem cell23_4420953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_4420953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4420953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4420953 prefixEnd_4420953 := by exact prefixLift 4420953
  have htrace : WordTrace (prefixWord ++ tailWord_4420953) baseStart_4420953 baseEnd_4420953 := by
    simpa [prefixWord, tailWord_4420953, baseEnd_4420953] using wordTrace_append hprefix tailTrace_4420953
  have hstable : (prefixWord ++ tailWord_4420953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4420953).length < 2 ^ (prefixWord ++ tailWord_4420953).sum := by decide
  have hdescent : baseEnd_4420953 < baseStart_4420953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4420953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421058 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4421058 : Nat := 118140960795 + 4421058 * 2 ^ 59
def prefixEnd_4421058 : Nat := 4983230072969 + 3 ^ 40 * 4421058 * 2
def baseEnd_4421058 : Nat := 2270127755405268823942931

theorem tailTrace_4421058 : CollatzResearch.WordTrace tailWord_4421058 prefixEnd_4421058 2270127755405268823942931 := by
  unfold tailWord_4421058
  simp only [CollatzResearch.WordTrace]
  refine ⟨40312308104317349359595957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107499488278179598292255885 40312308104317349359595957)
  ·
    refine ⟨3779278884779751502462121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40312308104317349359595957 3779278884779751502462121)
    ·
      refine ⟨2834459163584813626846591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3779278884779751502462121 2834459163584813626846591)
      ·
        refine ⟨4251688745377220440269887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2834459163584813626846591 4251688745377220440269887)
        ·
          refine ⟨6377533118065830660404831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251688745377220440269887 6377533118065830660404831)
          ·
            refine ⟨9566299677098745990607247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6377533118065830660404831 9566299677098745990607247)
            ·
              refine ⟨14349449515648118985910871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9566299677098745990607247 14349449515648118985910871)
              ·
                refine ⟨21524174273472178478866307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14349449515648118985910871 21524174273472178478866307)
                ·
                  refine ⟨32286261410208267718299461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21524174273472178478866307 32286261410208267718299461)
                  ·
                    refine ⟨6053674014414050197181149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32286261410208267718299461 6053674014414050197181149)
                    ·
                      refine ⟨2270127755405268823942931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053674014414050197181149 2270127755405268823942931)
                      ·
                        rfl

theorem cell23_4421058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4421058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421058 prefixEnd_4421058 := by exact prefixLift 4421058
  have htrace : WordTrace (prefixWord ++ tailWord_4421058) baseStart_4421058 baseEnd_4421058 := by
    simpa [prefixWord, tailWord_4421058, baseEnd_4421058] using wordTrace_append hprefix tailTrace_4421058
  have hstable : (prefixWord ++ tailWord_4421058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421058).length < 2 ^ (prefixWord ++ tailWord_4421058).sum := by decide
  have hdescent : baseEnd_4421058 < baseStart_4421058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421070 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_4421070 : Nat := 118140960795 + 4421070 * 2 ^ 59
def prefixEnd_4421070 : Nat := 4983230072969 + 3 ^ 40 * 4421070 * 2
def baseEnd_4421070 : Nat := 756711305724374258997625

theorem tailTrace_4421070 : CollatzResearch.WordTrace tailWord_4421070 prefixEnd_4421070 756711305724374258997625 := by
  unfold tailWord_4421070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20156208761653240435977583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107499780062150615658547109 20156208761653240435977583)
  ·
    refine ⟨30234313142479860653966375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20156208761653240435977583 30234313142479860653966375)
    ·
      refine ⟨45351469713719790980949563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30234313142479860653966375 45351469713719790980949563)
      ·
        refine ⟨68027204570579686471424345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45351469713719790980949563 68027204570579686471424345)
        ·
          refine ⟨51020403427934764853568259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68027204570579686471424345 51020403427934764853568259)
          ·
            refine ⟨76530605141902147280352389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51020403427934764853568259 76530605141902147280352389)
            ·
              refine ⟨14349488464106652615066073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76530605141902147280352389 14349488464106652615066073)
              ·
                refine ⟨10762116348079989461299555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14349488464106652615066073 10762116348079989461299555)
                ·
                  refine ⟨16143174522119984191949333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10762116348079989461299555 16143174522119984191949333)
                  ·
                    refine ⟨756711305724374258997625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16143174522119984191949333 756711305724374258997625)
                    ·
                      rfl

theorem cell23_4421070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_4421070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421070 prefixEnd_4421070 := by exact prefixLift 4421070
  have htrace : WordTrace (prefixWord ++ tailWord_4421070) baseStart_4421070 baseEnd_4421070 := by
    simpa [prefixWord, tailWord_4421070, baseEnd_4421070] using wordTrace_append hprefix tailTrace_4421070
  have hstable : (prefixWord ++ tailWord_4421070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421070).length < 2 ^ (prefixWord ++ tailWord_4421070).sum := by decide
  have hdescent : baseEnd_4421070 < baseStart_4421070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421073 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_4421073 : Nat := 118140960795 + 4421073 * 2 ^ 59
def prefixEnd_4421073 : Nat := 4983230072969 + 3 ^ 40 * 4421073 * 2
def baseEnd_4421073 : Nat := 2270135457615086265255361

theorem tailTrace_4421073 : CollatzResearch.WordTrace tailWord_4421073 prefixEnd_4421073 2270135457615086265255361 := by
  unfold tailWord_4421073
  simp only [CollatzResearch.WordTrace]
  refine ⟨161249779512215055000179873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107499853008143370000119915 161249779512215055000179873)
  ·
    refine ⟨120937334634161291250134905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161249779512215055000179873 120937334634161291250134905)
    ·
      refine ⟨90703000975620968437601179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120937334634161291250134905 90703000975620968437601179)
      ·
        refine ⟨136054501463431452656401769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90703000975620968437601179 136054501463431452656401769)
        ·
          refine ⟨102040876097573589492301327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136054501463431452656401769 102040876097573589492301327)
          ·
            refine ⟨153061314146360384238451991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102040876097573589492301327 153061314146360384238451991)
            ·
              refine ⟨229591971219540576357677987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153061314146360384238451991 229591971219540576357677987)
              ·
                refine ⟨344387956829310864536516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229591971219540576357677987 344387956829310864536516981)
                ·
                  refine ⟨32286370952747893550298467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 344387956829310864536516981 32286370952747893550298467)
                  ·
                    refine ⟨48429556429121840325447701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32286370952747893550298467 48429556429121840325447701)
                    ·
                      refine ⟨2270135457615086265255361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48429556429121840325447701 2270135457615086265255361)
                      ·
                        rfl

theorem cell23_4421073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_4421073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421073 prefixEnd_4421073 := by exact prefixLift 4421073
  have htrace : WordTrace (prefixWord ++ tailWord_4421073) baseStart_4421073 baseEnd_4421073 := by
    simpa [prefixWord, tailWord_4421073, baseEnd_4421073] using wordTrace_append hprefix tailTrace_4421073
  have hstable : (prefixWord ++ tailWord_4421073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421073).length < 2 ^ (prefixWord ++ tailWord_4421073).sum := by decide
  have hdescent : baseEnd_4421073 < baseStart_4421073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421077 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4421077 : Nat := 118140960795 + 4421077 * 2 ^ 59
def prefixEnd_4421077 : Nat := 4983230072969 + 3 ^ 40 * 4421077 * 2
def baseEnd_4421077 : Nat := 2270137511537704249605343

theorem tailTrace_4421077 : CollatzResearch.WordTrace tailWord_4421077 prefixEnd_4421077 2270137511537704249605343 := by
  unfold tailWord_4421077
  simp only [CollatzResearch.WordTrace]
  refine ⟨161249925404200563683325485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107499950269467042455550323 161249925404200563683325485)
  ·
    refine ⟨60468722026575211381247057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161249925404200563683325485 60468722026575211381247057)
    ·
      refine ⟨45351541519931408535935293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60468722026575211381247057 45351541519931408535935293)
      ·
        refine ⟨17006828069974278200975735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45351541519931408535935293 17006828069974278200975735)
        ·
          refine ⟨25510242104961417301463603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17006828069974278200975735 25510242104961417301463603)
          ·
            refine ⟨38265363157442125952195405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25510242104961417301463603 38265363157442125952195405)
            ·
              refine ⟨14349511184040797232073277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38265363157442125952195405 14349511184040797232073277)
              ·
                refine ⟨5381066694015298962027479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14349511184040797232073277 5381066694015298962027479)
                ·
                  refine ⟨8071600041022948443041219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381066694015298962027479 8071600041022948443041219)
                  ·
                    refine ⟨12107400061534422664561829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8071600041022948443041219 12107400061534422664561829)
                    ·
                      refine ⟨2270137511537704249605343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12107400061534422664561829 2270137511537704249605343)
                      ·
                        rfl

theorem cell23_4421077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4421077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421077 prefixEnd_4421077 := by exact prefixLift 4421077
  have htrace : WordTrace (prefixWord ++ tailWord_4421077) baseStart_4421077 baseEnd_4421077 := by
    simpa [prefixWord, tailWord_4421077, baseEnd_4421077] using wordTrace_append hprefix tailTrace_4421077
  have hstable : (prefixWord ++ tailWord_4421077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421077).length < 2 ^ (prefixWord ++ tailWord_4421077).sum := by decide
  have hdescent : baseEnd_4421077 < baseStart_4421077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421104 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 2, 4]
def baseStart_4421104 : Nat := 118140960795 + 4421104 * 2 ^ 59
def prefixEnd_4421104 : Nat := 4983230072969 + 3 ^ 40 * 4421104 * 2
def baseEnd_4421104 : Nat := 756717125171791881322573

theorem tailTrace_4421104 : CollatzResearch.WordTrace tailWord_4421104 prefixEnd_4421104 756717125171791881322573 := by
  unfold tailWord_4421104
  simp only [CollatzResearch.WordTrace]
  refine ⟨80625455087551373647279183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107500606783401831529705577 80625455087551373647279183)
  ·
    refine ⟨120938182631327060470918775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80625455087551373647279183 120938182631327060470918775)
    ·
      refine ⟨181407273946990590706378163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120938182631327060470918775 181407273946990590706378163)
      ·
        refine ⟨272110910920485886059567245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181407273946990590706378163 272110910920485886059567245)
        ·
          refine ⟨102041591595182207272337717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272110910920485886059567245 102041591595182207272337717)
          ·
            refine ⟨9566399212048331931781661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102041591595182207272337717 9566399212048331931781661)
            ·
              refine ⟨3587399704518124474418123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9566399212048331931781661 3587399704518124474418123)
              ·
                refine ⟨5381099556777186711627185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587399704518124474418123 5381099556777186711627185)
                ·
                  refine ⟨4035824667582890033720389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5381099556777186711627185 4035824667582890033720389)
                  ·
                    refine ⟨756717125171791881322573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4035824667582890033720389 756717125171791881322573)
                    ·
                      rfl

theorem cell23_4421104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_4421104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421104 prefixEnd_4421104 := by exact prefixLift 4421104
  have htrace : WordTrace (prefixWord ++ tailWord_4421104) baseStart_4421104 baseEnd_4421104 := by
    simpa [prefixWord, tailWord_4421104, baseEnd_4421104] using wordTrace_append hprefix tailTrace_4421104
  have hstable : (prefixWord ++ tailWord_4421104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421104).length < 2 ^ (prefixWord ++ tailWord_4421104).sum := by decide
  have hdescent : baseEnd_4421104 < baseStart_4421104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421117 : List Nat := [1, 4, 1, 1, 1, 6, 2, 7]
def baseStart_4421117 : Nat := 118140960795 + 4421117 * 2 ^ 59
def prefixEnd_4421117 : Nat := 4983230072969 + 3 ^ 40 * 4421117 * 2
def baseEnd_4421117 : Nat := 84079927806069781226117

theorem tailTrace_4421117 : CollatzResearch.WordTrace tailWord_4421117 prefixEnd_4421117 84079927806069781226117 := by
  unfold tailWord_4421117
  simp only [CollatzResearch.WordTrace]
  refine ⟨161251384324055650514781605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107500922882703767009854403 161251384324055650514781605)
  ·
    refine ⟨30234634560760434471521551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161251384324055650514781605 30234634560760434471521551)
    ·
      refine ⟨45351951841140651707282327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30234634560760434471521551 45351951841140651707282327)
      ·
        refine ⟨68027927761710977560923491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45351951841140651707282327 68027927761710977560923491)
        ·
          refine ⟨102041891642566466341385237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68027927761710977560923491 102041891642566466341385237)
          ·
            refine ⟨4783213670745303109752433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102041891642566466341385237 4783213670745303109752433)
            ·
              refine ⟨3587410253058977332314325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4783213670745303109752433 3587410253058977332314325)
              ·
                refine ⟨84079927806069781226117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3587410253058977332314325 84079927806069781226117)
                ·
                  rfl

theorem cell23_4421117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 7].length) (baseStart_4421117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421117 prefixEnd_4421117 := by exact prefixLift 4421117
  have htrace : WordTrace (prefixWord ++ tailWord_4421117) baseStart_4421117 baseEnd_4421117 := by
    simpa [prefixWord, tailWord_4421117, baseEnd_4421117] using wordTrace_append hprefix tailTrace_4421117
  have hstable : (prefixWord ++ tailWord_4421117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421117).length < 2 ^ (prefixWord ++ tailWord_4421117).sum := by decide
  have hdescent : baseEnd_4421117 < baseStart_4421117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421171 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 1, 3, 2]
def baseStart_4421171 : Nat := 118140960795 + 4421171 * 2 ^ 59
def prefixEnd_4421171 : Nat := 4983230072969 + 3 ^ 40 * 4421171 * 2
def baseEnd_4421171 : Nat := 2270185778719226881829911

theorem tailTrace_4421171 : CollatzResearch.WordTrace tailWord_4421171 prefixEnd_4421171 2270185778719226881829911 := by
  unfold tailWord_4421171
  simp only [CollatzResearch.WordTrace]
  refine ⟨161253353865860017737247367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107502235910573345158164911 161253353865860017737247367)
  ·
    refine ⟨241880030798790026605871051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161253353865860017737247367 241880030798790026605871051)
    ·
      refine ⟨362820046198185039908806577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241880030798790026605871051 362820046198185039908806577)
      ·
        refine ⟨272115034648638779931604933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362820046198185039908806577 272115034648638779931604933)
        ·
          refine ⟨51021568996619771237175925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272115034648638779931604933 51021568996619771237175925)
          ·
            refine ⟨4783272093433103553485243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51021568996619771237175925 4783272093433103553485243)
            ·
              refine ⟨7174908140149655330227865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4783272093433103553485243 7174908140149655330227865)
              ·
                refine ⟨5381181105112241497670899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7174908140149655330227865 5381181105112241497670899)
                ·
                  refine ⟨8071771657668362246506349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381181105112241497670899 8071771657668362246506349)
                  ·
                    refine ⟨3026914371625635842439881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8071771657668362246506349 3026914371625635842439881)
                    ·
                      refine ⟨2270185778719226881829911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026914371625635842439881 2270185778719226881829911)
                      ·
                        rfl

theorem cell23_4421171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3, 2].length) (baseStart_4421171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421171 prefixEnd_4421171 := by exact prefixLift 4421171
  have htrace : WordTrace (prefixWord ++ tailWord_4421171) baseStart_4421171 baseEnd_4421171 := by
    simpa [prefixWord, tailWord_4421171, baseEnd_4421171] using wordTrace_append hprefix tailTrace_4421171
  have hstable : (prefixWord ++ tailWord_4421171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421171).length < 2 ^ (prefixWord ++ tailWord_4421171).sum := by decide
  have hdescent : baseEnd_4421171 < baseStart_4421171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421201 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_4421201 : Nat := 118140960795 + 4421201 * 2 ^ 59
def prefixEnd_4421201 : Nat := 4983230072969 + 3 ^ 40 * 4421201 * 2
def baseEnd_4421201 : Nat := 2270201183138861764454773

theorem tailTrace_4421201 : CollatzResearch.WordTrace tailWord_4421201 prefixEnd_4421201 2270201183138861764454773 := by
  unfold tailWord_4421201
  simp only [CollatzResearch.WordTrace]
  refine ⟨161254448055751332860839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107502965370500888573892971 161254448055751332860839457)
  ·
    refine ⟨120940836041813499645629593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161254448055751332860839457 120940836041813499645629593)
    ·
      refine ⟨90705627031360124734222195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120940836041813499645629593 90705627031360124734222195)
      ·
        refine ⟨136058440547040187101333293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90705627031360124734222195 136058440547040187101333293)
        ·
          refine ⟨51021915205140070162999985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136058440547040187101333293 51021915205140070162999985)
          ·
            refine ⟨38266436403855052622249989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51021915205140070162999985 38266436403855052622249989)
            ·
              refine ⟨7174956825722822366671873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38266436403855052622249989 7174956825722822366671873)
              ·
                refine ⟨5381217619292116775003905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7174956825722822366671873 5381217619292116775003905)
                ·
                  refine ⟨4035913214469087581252929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5381217619292116775003905 4035913214469087581252929)
                  ·
                    refine ⟨3026934910851815685939697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4035913214469087581252929 3026934910851815685939697)
                    ·
                      refine ⟨2270201183138861764454773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3026934910851815685939697 2270201183138861764454773)
                      ·
                        rfl

theorem cell23_4421201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_4421201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421201 prefixEnd_4421201 := by exact prefixLift 4421201
  have htrace : WordTrace (prefixWord ++ tailWord_4421201) baseStart_4421201 baseEnd_4421201 := by
    simpa [prefixWord, tailWord_4421201, baseEnd_4421201] using wordTrace_append hprefix tailTrace_4421201
  have hstable : (prefixWord ++ tailWord_4421201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421201).length < 2 ^ (prefixWord ++ tailWord_4421201).sum := by decide
  have hdescent : baseEnd_4421201 < baseStart_4421201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421217 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_4421217 : Nat := 118140960795 + 4421217 * 2 ^ 59
def prefixEnd_4421217 : Nat := 4983230072969 + 3 ^ 40 * 4421217 * 2
def baseEnd_4421217 : Nat := 2270209398829333701854699

theorem tailTrace_4421217 : CollatzResearch.WordTrace tailWord_4421217 prefixEnd_4421217 2270209398829333701854699 := by
  unfold tailWord_4421217
  simp only [CollatzResearch.WordTrace]
  refine ⟨161255031623693367593421905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107503354415795578395614603 161255031623693367593421905)
  ·
    refine ⟨120941273717770025695066429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161255031623693367593421905 120941273717770025695066429)
    ·
      refine ⟨45352977644163759635649911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120941273717770025695066429 45352977644163759635649911)
      ·
        refine ⟨68029466466245639453474867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45352977644163759635649911 68029466466245639453474867)
        ·
          refine ⟨102044199699368459180212301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68029466466245639453474867 102044199699368459180212301)
          ·
            refine ⟨38266574887263172192579613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102044199699368459180212301 38266574887263172192579613)
            ·
              refine ⟨14349965582723689572217355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38266574887263172192579613 14349965582723689572217355)
              ·
                refine ⟨21524948374085534358326033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14349965582723689572217355 21524948374085534358326033)
                ·
                  refine ⟨16143711280564150768744525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21524948374085534358326033 16143711280564150768744525)
                  ·
                    refine ⟨6053891730211556538279197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16143711280564150768744525 6053891730211556538279197)
                    ·
                      refine ⟨2270209398829333701854699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6053891730211556538279197 2270209398829333701854699)
                      ·
                        rfl

theorem cell23_4421217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_4421217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421217 prefixEnd_4421217 := by exact prefixLift 4421217
  have htrace : WordTrace (prefixWord ++ tailWord_4421217) baseStart_4421217 baseEnd_4421217 := by
    simpa [prefixWord, tailWord_4421217, baseEnd_4421217] using wordTrace_append hprefix tailTrace_4421217
  have hstable : (prefixWord ++ tailWord_4421217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421217).length < 2 ^ (prefixWord ++ tailWord_4421217).sum := by decide
  have hdescent : baseEnd_4421217 < baseStart_4421217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421257 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_4421257 : Nat := 118140960795 + 4421257 * 2 ^ 59
def prefixEnd_4421257 : Nat := 4983230072969 + 3 ^ 40 * 4421257 * 2
def baseEnd_4421257 : Nat := 2270229938055513545354515

theorem tailTrace_4421257 : CollatzResearch.WordTrace tailWord_4421257 prefixEnd_4421257 2270229938055513545354515 := by
  unfold tailWord_4421257
  simp only [CollatzResearch.WordTrace]
  refine ⟨161256490543548454424878025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107504327029032302949918683 161256490543548454424878025)
  ·
    refine ⟨120942367907661340818658519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161256490543548454424878025 120942367907661340818658519)
    ·
      refine ⟨181413551861492011227987779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120942367907661340818658519 181413551861492011227987779)
      ·
        refine ⟨272120327792238016841981669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181413551861492011227987779 272120327792238016841981669)
        ·
          refine ⟨51022561461044628157871563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272120327792238016841981669 51022561461044628157871563)
          ·
            refine ⟨76533842191566942236807345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51022561461044628157871563 76533842191566942236807345)
            ·
              refine ⟨57400381643675206677605509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76533842191566942236807345 57400381643675206677605509)
              ·
                refine ⟨10762571558189101252051033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57400381643675206677605509 10762571558189101252051033)
                ·
                  refine ⟨8071928668641825939038275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10762571558189101252051033 8071928668641825939038275)
                  ·
                    refine ⟨12107893002962738908557413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8071928668641825939038275 12107893002962738908557413)
                    ·
                      refine ⟨2270229938055513545354515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12107893002962738908557413 2270229938055513545354515)
                      ·
                        rfl

theorem cell23_4421257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_4421257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421257 prefixEnd_4421257 := by exact prefixLift 4421257
  have htrace : WordTrace (prefixWord ++ tailWord_4421257) baseStart_4421257 baseEnd_4421257 := by
    simpa [prefixWord, tailWord_4421257, baseEnd_4421257] using wordTrace_append hprefix tailTrace_4421257
  have hstable : (prefixWord ++ tailWord_4421257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421257).length < 2 ^ (prefixWord ++ tailWord_4421257).sum := by decide
  have hdescent : baseEnd_4421257 < baseStart_4421257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421284 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_4421284 : Nat := 118140960795 + 4421284 * 2 ^ 59
def prefixEnd_4421284 : Nat := 4983230072969 + 3 ^ 40 * 4421284 * 2
def baseEnd_4421284 : Nat := 756747934011061646572297

theorem tailTrace_4421284 : CollatzResearch.WordTrace tailWord_4421284 prefixEnd_4421284 756747934011061646572297 := by
  unfold tailWord_4421284
  simp only [CollatzResearch.WordTrace]
  refine ⟨80628737657225319018055453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107504983542967092024073937 80628737657225319018055453)
  ·
    refine ⟨30235776621459494631770795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80628737657225319018055453 30235776621459494631770795)
    ·
      refine ⟨45353664932189241947656193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30235776621459494631770795 45353664932189241947656193)
      ·
        refine ⟨34015248699141931460742145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45353664932189241947656193 34015248699141931460742145)
        ·
          refine ⟨25511436524356448595556609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34015248699141931460742145 25511436524356448595556609)
          ·
            refine ⟨19133577393267336446667457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25511436524356448595556609 19133577393267336446667457)
            ·
              refine ⟨14350183044950502335000593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19133577393267336446667457 14350183044950502335000593)
              ·
                refine ⟨10762637283712876751250445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14350183044950502335000593 10762637283712876751250445)
                ·
                  refine ⟨4035988981392328781718917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10762637283712876751250445 4035988981392328781718917)
                  ·
                    refine ⟨756747934011061646572297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4035988981392328781718917 756747934011061646572297)
                    ·
                      rfl

theorem cell23_4421284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_4421284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421284 prefixEnd_4421284 := by exact prefixLift 4421284
  have htrace : WordTrace (prefixWord ++ tailWord_4421284) baseStart_4421284 baseEnd_4421284 := by
    simpa [prefixWord, tailWord_4421284, baseEnd_4421284] using wordTrace_append hprefix tailTrace_4421284
  have hstable : (prefixWord ++ tailWord_4421284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421284).length < 2 ^ (prefixWord ++ tailWord_4421284).sum := by decide
  have hdescent : baseEnd_4421284 < baseStart_4421284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421344 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_4421344 : Nat := 118140960795 + 4421344 * 2 ^ 59
def prefixEnd_4421344 : Nat := 4983230072969 + 3 ^ 40 * 4421344 * 2
def baseEnd_4421344 : Nat := 756758203624151568322205

theorem tailTrace_4421344 : CollatzResearch.WordTrace tailWord_4421344 prefixEnd_4421344 756758203624151568322205 := by
  unfold tailWord_4421344
  simp only [CollatzResearch.WordTrace]
  refine ⟨80629831847116634141647543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107506442462822178855530057 80629831847116634141647543)
  ·
    refine ⟨120944747770674951212471315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80629831847116634141647543 120944747770674951212471315)
    ·
      refine ⟨181417121656012426818706973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120944747770674951212471315 181417121656012426818706973)
      ·
        refine ⟨68031420621004660057015115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181417121656012426818706973 68031420621004660057015115)
        ·
          refine ⟨102047130931506990085522673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68031420621004660057015115 102047130931506990085522673)
          ·
            refine ⟨76535348198630242564142005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102047130931506990085522673 76535348198630242564142005)
            ·
              refine ⟨7175188893621585240388313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76535348198630242564142005 7175188893621585240388313)
              ·
                refine ⟨5381391670216188930291235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7175188893621585240388313 5381391670216188930291235)
                ·
                  refine ⟨8072087505324283395436853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381391670216188930291235 8072087505324283395436853)
                  ·
                    refine ⟨756758203624151568322205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8072087505324283395436853 756758203624151568322205)
                    ·
                      rfl

theorem cell23_4421344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_4421344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421344 prefixEnd_4421344 := by exact prefixLift 4421344
  have htrace : WordTrace (prefixWord ++ tailWord_4421344) baseStart_4421344 baseEnd_4421344 := by
    simpa [prefixWord, tailWord_4421344, baseEnd_4421344] using wordTrace_append hprefix tailTrace_4421344
  have hstable : (prefixWord ++ tailWord_4421344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421344).length < 2 ^ (prefixWord ++ tailWord_4421344).sum := by decide
  have hdescent : baseEnd_4421344 < baseStart_4421344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421358 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_4421358 : Nat := 118140960795 + 4421358 * 2 ^ 59
def prefixEnd_4421358 : Nat := 4983230072969 + 3 ^ 40 * 4421358 * 2
def baseEnd_4421358 : Nat := 2270281799601617650191551

theorem tailTrace_4421358 : CollatzResearch.WordTrace tailWord_4421358 prefixEnd_4421358 2270281799601617650191551 := by
  unfold tailWord_4421358
  simp only [CollatzResearch.WordTrace]
  refine ⟨20157521789522818584288091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107506782877455032449536485 20157521789522818584288091)
  ·
    refine ⟨30236282684284227876432137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20157521789522818584288091 30236282684284227876432137)
    ·
      refine ⟨22677212013213170907324103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30236282684284227876432137 22677212013213170907324103)
      ·
        refine ⟨34015818019819756360986155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22677212013213170907324103 34015818019819756360986155)
        ·
          refine ⟨51023727029729634541479233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34015818019819756360986155 51023727029729634541479233)
          ·
            refine ⟨38267795272297225906109425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51023727029729634541479233 38267795272297225906109425)
            ·
              refine ⟨28700846454222919429582069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38267795272297225906109425 28700846454222919429582069)
              ·
                refine ⟨2690704355083398696523319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28700846454222919429582069 2690704355083398696523319)
                ·
                  refine ⟨4036056532625098044784979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690704355083398696523319 4036056532625098044784979)
                  ·
                    refine ⟨6054084798937647067177469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036056532625098044784979 6054084798937647067177469)
                    ·
                      refine ⟨2270281799601617650191551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054084798937647067177469 2270281799601617650191551)
                      ·
                        rfl

theorem cell23_4421358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_4421358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421358 prefixEnd_4421358 := by exact prefixLift 4421358
  have htrace : WordTrace (prefixWord ++ tailWord_4421358) baseStart_4421358 baseEnd_4421358 := by
    simpa [prefixWord, tailWord_4421358, baseEnd_4421358] using wordTrace_append hprefix tailTrace_4421358
  have hstable : (prefixWord ++ tailWord_4421358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421358).length < 2 ^ (prefixWord ++ tailWord_4421358).sum := by decide
  have hdescent : baseEnd_4421358 < baseStart_4421358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421361 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 1, 5]
def baseStart_4421361 : Nat := 118140960795 + 4421361 * 2 ^ 59
def prefixEnd_4421361 : Nat := 4983230072969 + 3 ^ 40 * 4421361 * 2
def baseEnd_4421361 : Nat := 756761113347860379484679

theorem tailTrace_4421361 : CollatzResearch.WordTrace tailWord_4421361 prefixEnd_4421361 756761113347860379484679 := by
  unfold tailWord_4421361
  simp only [CollatzResearch.WordTrace]
  refine ⟨161260283735171680186663937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107506855823447786791109291 161260283735171680186663937)
  ·
    refine ⟨120945212801378760139997953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161260283735171680186663937 120945212801378760139997953)
    ·
      refine ⟨90708909601034070104998465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120945212801378760139997953 90708909601034070104998465)
      ·
        refine ⟨68031682200775552578748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90708909601034070104998465 68031682200775552578748849)
        ·
          refine ⟨51023761650581664434061637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68031682200775552578748849 51023761650581664434061637)
          ·
            refine ⟨9566955309484062081386557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51023761650581664434061637 9566955309484062081386557)
            ·
              refine ⟨3587608241056523280519959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9566955309484062081386557 3587608241056523280519959)
              ·
                refine ⟨5381412361584784920779939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587608241056523280519959 5381412361584784920779939)
                ·
                  refine ⟨8072118542377177381169909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381412361584784920779939 8072118542377177381169909)
                  ·
                    refine ⟨756761113347860379484679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8072118542377177381169909 756761113347860379484679)
                    ·
                      rfl

theorem cell23_4421361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_4421361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421361 prefixEnd_4421361 := by exact prefixLift 4421361
  have htrace : WordTrace (prefixWord ++ tailWord_4421361) baseStart_4421361 baseEnd_4421361 := by
    simpa [prefixWord, tailWord_4421361, baseEnd_4421361] using wordTrace_append hprefix tailTrace_4421361
  have hstable : (prefixWord ++ tailWord_4421361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421361).length < 2 ^ (prefixWord ++ tailWord_4421361).sum := by decide
  have hdescent : baseEnd_4421361 < baseStart_4421361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421377 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4421377 : Nat := 118140960795 + 4421377 * 2 ^ 59
def prefixEnd_4421377 : Nat := 4983230072969 + 3 ^ 40 * 4421377 * 2
def baseEnd_4421377 : Nat := 2270291555734053075853963

theorem tailTrace_4421377 : CollatzResearch.WordTrace tailWord_4421377 prefixEnd_4421377 2270291555734053075853963 := by
  unfold tailWord_4421377
  simp only [CollatzResearch.WordTrace]
  refine ⟨161260867303113714919246385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107507244868742476612830923 161260867303113714919246385)
  ·
    refine ⟨120945650477335286189434789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161260867303113714919246385 120945650477335286189434789)
    ·
      refine ⟨22677309464500366160519023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120945650477335286189434789 22677309464500366160519023)
      ·
        refine ⟨34015964196750549240778535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22677309464500366160519023 34015964196750549240778535)
        ·
          refine ⟨51023946295125823861167803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34015964196750549240778535 51023946295125823861167803)
          ·
            refine ⟨76535919442688735791751705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51023946295125823861167803 76535919442688735791751705)
            ·
              refine ⟨57401939582016551843813779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76535919442688735791751705 57401939582016551843813779)
              ·
                refine ⟨86102909373024827765720669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57401939582016551843813779 86102909373024827765720669)
                ·
                  refine ⟨32288591014884310412145251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86102909373024827765720669 32288591014884310412145251)
                  ·
                    refine ⟨48432886522326465618217877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32288591014884310412145251 48432886522326465618217877)
                    ·
                      refine ⟨2270291555734053075853963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48432886522326465618217877 2270291555734053075853963)
                      ·
                        rfl

theorem cell23_4421377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4421377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421377 prefixEnd_4421377 := by exact prefixLift 4421377
  have htrace : WordTrace (prefixWord ++ tailWord_4421377) baseStart_4421377 baseEnd_4421377 := by
    simpa [prefixWord, tailWord_4421377, baseEnd_4421377] using wordTrace_append hprefix tailTrace_4421377
  have hstable : (prefixWord ++ tailWord_4421377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421377).length < 2 ^ (prefixWord ++ tailWord_4421377).sum := by decide
  have hdescent : baseEnd_4421377 < baseStart_4421377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421384 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_4421384 : Nat := 118140960795 + 4421384 * 2 ^ 59
def prefixEnd_4421384 : Nat := 4983230072969 + 3 ^ 40 * 4421384 * 2
def baseEnd_4421384 : Nat := 2270295150098634548466431

theorem tailTrace_4421384 : CollatzResearch.WordTrace tailWord_4421384 prefixEnd_4421384 2270295150098634548466431 := by
  unfold tailWord_4421384
  simp only [CollatzResearch.WordTrace]
  refine ⟨80630561307044177557375603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107507415076058903409834137 80630561307044177557375603)
  ·
    refine ⟨120945841960566266336063405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80630561307044177557375603 120945841960566266336063405)
    ·
      refine ⟨45354690735212349876023777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120945841960566266336063405 45354690735212349876023777)
      ·
        refine ⟨34016018051409262407017833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45354690735212349876023777 34016018051409262407017833)
        ·
          refine ⟨25512013538556946805263375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34016018051409262407017833 25512013538556946805263375)
          ·
            refine ⟨38268020307835420207895063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25512013538556946805263375 38268020307835420207895063)
            ·
              refine ⟨57402030461753130311842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38268020307835420207895063 57402030461753130311842595)
              ·
                refine ⟨86103045692629695467763893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57402030461753130311842595 86103045692629695467763893)
                ·
                  refine ⟨8072160533684033950102865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86103045692629695467763893 8072160533684033950102865)
                  ·
                    refine ⟨6054120400263025462577149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8072160533684033950102865 6054120400263025462577149)
                    ·
                      refine ⟨2270295150098634548466431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054120400263025462577149 2270295150098634548466431)
                      ·
                        rfl

theorem cell23_4421384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_4421384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421384 prefixEnd_4421384 := by exact prefixLift 4421384
  have htrace : WordTrace (prefixWord ++ tailWord_4421384) baseStart_4421384 baseEnd_4421384 := by
    simpa [prefixWord, tailWord_4421384, baseEnd_4421384] using wordTrace_append hprefix tailTrace_4421384
  have hstable : (prefixWord ++ tailWord_4421384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421384).length < 2 ^ (prefixWord ++ tailWord_4421384).sum := by decide
  have hdescent : baseEnd_4421384 < baseStart_4421384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421387 : List Nat := [1, 1, 1, 1, 5, 1, 5, 8]
def baseStart_4421387 : Nat := 118140960795 + 4421387 * 2 ^ 59
def prefixEnd_4421387 : Nat := 4983230072969 + 3 ^ 40 * 4421387 * 2
def baseEnd_4421387 : Nat := 84085062612614742101071

theorem tailTrace_4421387 : CollatzResearch.WordTrace tailWord_4421387 prefixEnd_4421387 84085062612614742101071 := by
  unfold tailWord_4421387
  simp only [CollatzResearch.WordTrace]
  refine ⟨161261232033077486627110415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107507488022051657751406943 161261232033077486627110415)
  ·
    refine ⟨241891848049616229940665623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161261232033077486627110415 241891848049616229940665623)
    ·
      refine ⟨362837772074424344910998435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241891848049616229940665623 362837772074424344910998435)
      ·
        refine ⟨544256658111636517366497653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362837772074424344910998435 544256658111636517366497653)
        ·
          refine ⟨51024061697965923503109155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 544256658111636517366497653 51024061697965923503109155)
          ·
            refine ⟨76536092546948885254663733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51024061697965923503109155 76536092546948885254663733)
            ·
              refine ⟨7175258676276457992624725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76536092546948885254663733 7175258676276457992624725)
              ·
                refine ⟨84085062612614742101071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7175258676276457992624725 84085062612614742101071)
                ·
                  rfl

theorem cell23_4421387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 8].length) (baseStart_4421387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421387 prefixEnd_4421387 := by exact prefixLift 4421387
  have htrace : WordTrace (prefixWord ++ tailWord_4421387) baseStart_4421387 baseEnd_4421387 := by
    simpa [prefixWord, tailWord_4421387, baseEnd_4421387] using wordTrace_append hprefix tailTrace_4421387
  have hstable : (prefixWord ++ tailWord_4421387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421387).length < 2 ^ (prefixWord ++ tailWord_4421387).sum := by decide
  have hdescent : baseEnd_4421387 < baseStart_4421387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421404 : List Nat := [2, 2, 3, 1, 1, 2, 5, 7]
def baseStart_4421404 : Nat := 118140960795 + 4421404 * 2 ^ 59
def prefixEnd_4421404 : Nat := 4983230072969 + 3 ^ 40 * 4421404 * 2
def baseEnd_4421404 : Nat := 84085385915249054452457

theorem tailTrace_4421404 : CollatzResearch.WordTrace tailWord_4421404 prefixEnd_4421404 84085385915249054452457 := by
  unfold tailWord_4421404
  simp only [CollatzResearch.WordTrace]
  refine ⟨80630926037007949265239633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107507901382677265686986177 80630926037007949265239633)
  ·
    refine ⟨60473194527755961948929725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80630926037007949265239633 60473194527755961948929725)
    ·
      refine ⟨22677447947908485730848647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60473194527755961948929725 22677447947908485730848647)
      ·
        refine ⟨34016171921862728596272971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22677447947908485730848647 34016171921862728596272971)
        ·
          refine ⟨51024257882794092894409457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34016171921862728596272971 51024257882794092894409457)
          ·
            refine ⟨38268193412095569670807093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51024257882794092894409457 38268193412095569670807093)
            ·
              refine ⟨3587643132383959656638165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38268193412095569670807093 3587643132383959656638165)
              ·
                refine ⟨84085385915249054452457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3587643132383959656638165 84085385915249054452457)
                ·
                  rfl

theorem cell23_4421404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 7].length) (baseStart_4421404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421404 prefixEnd_4421404 := by exact prefixLift 4421404
  have htrace : WordTrace (prefixWord ++ tailWord_4421404) baseStart_4421404 baseEnd_4421404 := by
    simpa [prefixWord, tailWord_4421404, baseEnd_4421404] using wordTrace_append hprefix tailTrace_4421404
  have hstable : (prefixWord ++ tailWord_4421404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421404).length < 2 ^ (prefixWord ++ tailWord_4421404).sum := by decide
  have hdescent : baseEnd_4421404 < baseStart_4421404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421431 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_4421431 : Nat := 118140960795 + 4421431 * 2 ^ 59
def prefixEnd_4421431 : Nat := 4983230072969 + 3 ^ 40 * 4421431 * 2
def baseEnd_4421431 : Nat := 2270319283689395864578715

theorem tailTrace_4421431 : CollatzResearch.WordTrace tailWord_4421431 prefixEnd_4421431 2270319283689395864578715 := by
  unfold tailWord_4421431
  simp only [CollatzResearch.WordTrace]
  refine ⟨161262836844918082141712147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107508557896612054761141431 161262836844918082141712147)
  ·
    refine ⟨241894255267377123212568221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161262836844918082141712147 241894255267377123212568221)
    ·
      refine ⟨90710345725266421204713083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241894255267377123212568221 90710345725266421204713083)
      ·
        refine ⟨136065518587899631807069625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90710345725266421204713083 136065518587899631807069625)
        ·
          refine ⟨102049138940924723855302219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136065518587899631807069625 102049138940924723855302219)
          ·
            refine ⟨153073708411387085782953329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102049138940924723855302219 153073708411387085782953329)
            ·
              refine ⟨114805281308540314337214997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153073708411387085782953329 114805281308540314337214997)
              ·
                refine ⟨5381497561337827234556953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114805281308540314337214997 5381497561337827234556953)
                ·
                  refine ⟨4036123171003370425917715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5381497561337827234556953 4036123171003370425917715)
                  ·
                    refine ⟨6054184756505055638876573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036123171003370425917715 6054184756505055638876573)
                    ·
                      refine ⟨2270319283689395864578715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054184756505055638876573 2270319283689395864578715)
                      ·
                        rfl

theorem cell23_4421431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_4421431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421431 prefixEnd_4421431 := by exact prefixLift 4421431
  have htrace : WordTrace (prefixWord ++ tailWord_4421431) baseStart_4421431 baseEnd_4421431 := by
    simpa [prefixWord, tailWord_4421431, baseEnd_4421431] using wordTrace_append hprefix tailTrace_4421431
  have hstable : (prefixWord ++ tailWord_4421431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421431).length < 2 ^ (prefixWord ++ tailWord_4421431).sum := by decide
  have hdescent : baseEnd_4421431 < baseStart_4421431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421458 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_4421458 : Nat := 118140960795 + 4421458 * 2 ^ 59
def prefixEnd_4421458 : Nat := 4983230072969 + 3 ^ 40 * 4421458 * 2
def baseEnd_4421458 : Nat := 2270333147667067258941091

theorem tailTrace_4421458 : CollatzResearch.WordTrace tailWord_4421458 prefixEnd_4421458 2270333147667067258941091 := by
  unfold tailWord_4421458
  simp only [CollatzResearch.WordTrace]
  refine ⟨40315955403955066438236257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107509214410546843835296685 40315955403955066438236257)
  ·
    refine ⟨30236966552966299828677193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40315955403955066438236257 30236966552966299828677193)
    ·
      refine ⟨22677724914724724871507895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30236966552966299828677193 22677724914724724871507895)
      ·
        refine ⟨34016587372087087307261843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22677724914724724871507895 34016587372087087307261843)
        ·
          refine ⟨51024881058130630960892765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34016587372087087307261843 51024881058130630960892765)
          ·
            refine ⟨19134330396798986610334787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51024881058130630960892765 19134330396798986610334787)
            ·
              refine ⟨28701495595198479915502181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19134330396798986610334787 28701495595198479915502181)
              ·
                refine ⟨5381530424099714984156659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28701495595198479915502181 5381530424099714984156659)
                ·
                  refine ⟨8072295636149572476234989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381530424099714984156659 8072295636149572476234989)
                  ·
                    refine ⟨3027110863556089678588121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8072295636149572476234989 3027110863556089678588121)
                    ·
                      refine ⟨2270333147667067258941091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027110863556089678588121 2270333147667067258941091)
                      ·
                        rfl

theorem cell23_4421458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_4421458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421458 prefixEnd_4421458 := by exact prefixLift 4421458
  have htrace : WordTrace (prefixWord ++ tailWord_4421458) baseStart_4421458 baseEnd_4421458 := by
    simpa [prefixWord, tailWord_4421458, baseEnd_4421458] using wordTrace_append hprefix tailTrace_4421458
  have hstable : (prefixWord ++ tailWord_4421458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421458).length < 2 ^ (prefixWord ++ tailWord_4421458).sum := by decide
  have hdescent : baseEnd_4421458 < baseStart_4421458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421488 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2]
def baseStart_4421488 : Nat := 118140960795 + 4421488 * 2 ^ 59
def prefixEnd_4421488 : Nat := 4983230072969 + 3 ^ 40 * 4421488 * 2
def baseEnd_4421488 : Nat := 2270348552086702141565953

theorem tailTrace_4421488 : CollatzResearch.WordTrace tailWord_4421488 prefixEnd_4421488 2270348552086702141565953 := by
  unfold tailWord_4421488
  simp only [CollatzResearch.WordTrace]
  refine ⟨80632457902855790438268559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107509943870474387251024745 80632457902855790438268559)
  ·
    refine ⟨120948686854283685657402839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80632457902855790438268559 120948686854283685657402839)
    ·
      refine ⟨181423030281425528486104259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120948686854283685657402839 181423030281425528486104259)
      ·
        refine ⟨272134545422138292729156389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181423030281425528486104259 272134545422138292729156389)
        ·
          refine ⟨51025227266650929886716823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272134545422138292729156389 51025227266650929886716823)
          ·
            refine ⟨76537840899976394830075235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51025227266650929886716823 76537840899976394830075235)
            ·
              refine ⟨114806761349964592245112853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76537840899976394830075235 114806761349964592245112853)
              ·
                refine ⟨5381566938279590261489665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114806761349964592245112853 5381566938279590261489665)
                ·
                  refine ⟨4036175203709692696117249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5381566938279590261489665 4036175203709692696117249)
                  ·
                    refine ⟨3027131402782269522087937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036175203709692696117249 3027131402782269522087937)
                    ·
                      refine ⟨2270348552086702141565953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027131402782269522087937 2270348552086702141565953)
                      ·
                        rfl

theorem cell23_4421488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 2, 2].length) (baseStart_4421488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421488 prefixEnd_4421488 := by exact prefixLift 4421488
  have htrace : WordTrace (prefixWord ++ tailWord_4421488) baseStart_4421488 baseEnd_4421488 := by
    simpa [prefixWord, tailWord_4421488, baseEnd_4421488] using wordTrace_append hprefix tailTrace_4421488
  have hstable : (prefixWord ++ tailWord_4421488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421488).length < 2 ^ (prefixWord ++ tailWord_4421488).sum := by decide
  have hdescent : baseEnd_4421488 < baseStart_4421488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421504 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_4421504 : Nat := 118140960795 + 4421504 * 2 ^ 59
def prefixEnd_4421504 : Nat := 4983230072969 + 3 ^ 40 * 4421504 * 2
def baseEnd_4421504 : Nat := 2270356767777174078965879

theorem tailTrace_4421504 : CollatzResearch.WordTrace tailWord_4421504 prefixEnd_4421504 2270356767777174078965879 := by
  unfold tailWord_4421504
  simp only [CollatzResearch.WordTrace]
  refine ⟨80632749686826807804559783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107510332915769077072746377 80632749686826807804559783)
  ·
    refine ⟨120949124530240211706839675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80632749686826807804559783 120949124530240211706839675)
    ·
      refine ⟨181423686795360317560259513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120949124530240211706839675 181423686795360317560259513)
      ·
        refine ⟨136067765096520238170194635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181423686795360317560259513 136067765096520238170194635)
        ·
          refine ⟨204101647644780357255291953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136067765096520238170194635 204101647644780357255291953)
          ·
            refine ⟨153076235733585267941468965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204101647644780357255291953 153076235733585267941468965)
            ·
              refine ⟨28701794200047237739025431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153076235733585267941468965 28701794200047237739025431)
              ·
                refine ⟨43052691300070856608538147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28701794200047237739025431 43052691300070856608538147)
                ·
                  refine ⟨64579036950106284912807221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43052691300070856608538147 64579036950106284912807221)
                  ·
                    refine ⟨6054284714072464210575677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64579036950106284912807221 6054284714072464210575677)
                    ·
                      refine ⟨2270356767777174078965879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054284714072464210575677 2270356767777174078965879)
                      ·
                        rfl

theorem cell23_4421504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_4421504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421504 prefixEnd_4421504 := by exact prefixLift 4421504
  have htrace : WordTrace (prefixWord ++ tailWord_4421504) baseStart_4421504 baseEnd_4421504 := by
    simpa [prefixWord, tailWord_4421504, baseEnd_4421504] using wordTrace_append hprefix tailTrace_4421504
  have hstable : (prefixWord ++ tailWord_4421504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421504).length < 2 ^ (prefixWord ++ tailWord_4421504).sum := by decide
  have hdescent : baseEnd_4421504 < baseStart_4421504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421526 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4421526 : Nat := 118140960795 + 4421526 * 2 ^ 59
def prefixEnd_4421526 : Nat := 4983230072969 + 3 ^ 40 * 4421526 * 2
def baseEnd_4421526 : Nat := 2270368064351572992890779

theorem tailTrace_4421526 : CollatzResearch.WordTrace tailWord_4421526 prefixEnd_4421526 2270368064351572992890779 := by
  unfold tailWord_4421526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079143861223369585401277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107510867853049275577613621 10079143861223369585401277)
  ·
    refine ⟨3779678947958763594525479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10079143861223369585401277 3779678947958763594525479)
    ·
      refine ⟨5669518421938145391788219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779678947958763594525479 5669518421938145391788219)
      ·
        refine ⟨8504277632907218087682329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5669518421938145391788219 8504277632907218087682329)
        ·
          refine ⟨6378208224680413565761747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8504277632907218087682329 6378208224680413565761747)
          ·
            refine ⟨9567312337020620348642621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378208224680413565761747 9567312337020620348642621)
            ·
              refine ⟨3587742126382732630740983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9567312337020620348642621 3587742126382732630740983)
              ·
                refine ⟨5381613189574098946111475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587742126382732630740983 5381613189574098946111475)
                ·
                  refine ⟨8072419784361148419167213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381613189574098946111475 8072419784361148419167213)
                  ·
                    refine ⟨3027157419135430657187705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8072419784361148419167213 3027157419135430657187705)
                    ·
                      refine ⟨2270368064351572992890779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027157419135430657187705 2270368064351572992890779)
                      ·
                        rfl

theorem cell23_4421526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4421526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421526 prefixEnd_4421526 := by exact prefixLift 4421526
  have htrace : WordTrace (prefixWord ++ tailWord_4421526) baseStart_4421526 baseEnd_4421526 := by
    simpa [prefixWord, tailWord_4421526, baseEnd_4421526] using wordTrace_append hprefix tailTrace_4421526
  have hstable : (prefixWord ++ tailWord_4421526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421526).length < 2 ^ (prefixWord ++ tailWord_4421526).sum := by decide
  have hdescent : baseEnd_4421526 < baseStart_4421526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421601 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 6]
def baseStart_4421601 : Nat := 118140960795 + 4421601 * 2 ^ 59
def prefixEnd_4421601 : Nat := 4983230072969 + 3 ^ 40 * 4421601 * 2
def baseEnd_4421601 : Nat := 252267397266740022161437

theorem tailTrace_4421601 : CollatzResearch.WordTrace tailWord_4421601 prefixEnd_4421601 252267397266740022161437 := by
  unfold tailWord_4421601
  simp only [CollatzResearch.WordTrace]
  refine ⟨161269037254302201175400657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107512691502868134116933771 161269037254302201175400657)
  ·
    refine ⟨120951777940726650881550493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161269037254302201175400657 120951777940726650881550493)
    ·
      refine ⟨45356916727772494080581435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120951777940726650881550493 45356916727772494080581435)
      ·
        refine ⟨68035375091658741120872153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45356916727772494080581435 68035375091658741120872153)
        ·
          refine ⟨51026531318744055840654115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68035375091658741120872153 51026531318744055840654115)
          ·
            refine ⟨76539796978116083760981173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51026531318744055840654115 76539796978116083760981173)
            ·
              refine ⟨7175605966698382852591985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76539796978116083760981173 7175605966698382852591985)
              ·
                refine ⟨5381704475023787139443989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7175605966698382852591985 5381704475023787139443989)
                ·
                  refine ⟨252267397266740022161437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5381704475023787139443989 252267397266740022161437)
                  ·
                    rfl

theorem cell23_4421601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_4421601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421601 prefixEnd_4421601 := by exact prefixLift 4421601
  have htrace : WordTrace (prefixWord ++ tailWord_4421601) baseStart_4421601 baseEnd_4421601 := by
    simpa [prefixWord, tailWord_4421601, baseEnd_4421601] using wordTrace_append hprefix tailTrace_4421601
  have hstable : (prefixWord ++ tailWord_4421601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421601).length < 2 ^ (prefixWord ++ tailWord_4421601).sum := by decide
  have hdescent : baseEnd_4421601 < baseStart_4421601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421604 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_4421604 : Nat := 118140960795 + 4421604 * 2 ^ 59
def prefixEnd_4421604 : Nat := 4983230072969 + 3 ^ 40 * 4421604 * 2
def baseEnd_4421604 : Nat := 2270408115842623687715419

theorem tailTrace_4421604 : CollatzResearch.WordTrace tailWord_4421604 prefixEnd_4421604 2270408115842623687715419 := by
  unfold tailWord_4421604
  simp only [CollatzResearch.WordTrace]
  refine ⟨80634573336645666343879933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107512764448860888458506577 80634573336645666343879933)
  ·
    refine ⟨30237965001242124878954975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80634573336645666343879933 30237965001242124878954975)
    ·
      refine ⟨45356947501863187318432463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30237965001242124878954975 45356947501863187318432463)
      ·
        refine ⟨68035421252794780977648695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45356947501863187318432463 68035421252794780977648695)
        ·
          refine ⟨102053131879192171466473043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68035421252794780977648695 102053131879192171466473043)
          ·
            refine ⟨153079697818788257199709565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102053131879192171466473043 153079697818788257199709565)
            ·
              refine ⟨57404886682045596449891087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153079697818788257199709565 57404886682045596449891087)
              ·
                refine ⟨86107330023068394674836631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57404886682045596449891087 86107330023068394674836631)
                ·
                  refine ⟨129160995034602592012254947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86107330023068394674836631 129160995034602592012254947)
                  ·
                    refine ⟨193741492551903888018382421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129160995034602592012254947 193741492551903888018382421)
                    ·
                      refine ⟨2270408115842623687715419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 193741492551903888018382421 2270408115842623687715419)
                      ·
                        rfl

theorem cell23_4421604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_4421604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421604 prefixEnd_4421604 := by exact prefixLift 4421604
  have htrace : WordTrace (prefixWord ++ tailWord_4421604) baseStart_4421604 baseEnd_4421604 := by
    simpa [prefixWord, tailWord_4421604, baseEnd_4421604] using wordTrace_append hprefix tailTrace_4421604
  have hstable : (prefixWord ++ tailWord_4421604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421604).length < 2 ^ (prefixWord ++ tailWord_4421604).sum := by decide
  have hdescent : baseEnd_4421604 < baseStart_4421604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421624 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_4421624 : Nat := 118140960795 + 4421624 * 2 ^ 59
def prefixEnd_4421624 : Nat := 4983230072969 + 3 ^ 40 * 4421624 * 2
def baseEnd_4421624 : Nat := 2270418385455713609465327

theorem tailTrace_4421624 : CollatzResearch.WordTrace tailWord_4421624 prefixEnd_4421624 2270418385455713609465327 := by
  unfold tailWord_4421624
  simp only [CollatzResearch.WordTrace]
  refine ⟨80634938066609438051743963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107513250755479250735658617 80634938066609438051743963)
  ·
    refine ⟨120952407099914157077615945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80634938066609438051743963 120952407099914157077615945)
    ·
      refine ⟨90714305324935617808211959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120952407099914157077615945 90714305324935617808211959)
      ·
        refine ⟨136071457987403426712317939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90714305324935617808211959 136071457987403426712317939)
        ·
          refine ⟨204107186981105140068476909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136071457987403426712317939 204107186981105140068476909)
          ·
            refine ⟨76540195117914427525678841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204107186981105140068476909 76540195117914427525678841)
            ·
              refine ⟨57405146338435820644259131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76540195117914427525678841 57405146338435820644259131)
              ·
                refine ⟨86107719507653730966388697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57405146338435820644259131 86107719507653730966388697)
                ·
                  refine ⟨64580789630740298224791523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86107719507653730966388697 64580789630740298224791523)
                  ·
                    refine ⟨96871184446110447337187285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64580789630740298224791523 96871184446110447337187285)
                    ·
                      refine ⟨2270418385455713609465327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96871184446110447337187285 2270418385455713609465327)
                      ·
                        rfl

theorem cell23_4421624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_4421624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421624 prefixEnd_4421624 := by exact prefixLift 4421624
  have htrace : WordTrace (prefixWord ++ tailWord_4421624) baseStart_4421624 baseEnd_4421624 := by
    simpa [prefixWord, tailWord_4421624, baseEnd_4421624] using wordTrace_append hprefix tailTrace_4421624
  have hstable : (prefixWord ++ tailWord_4421624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421624).length < 2 ^ (prefixWord ++ tailWord_4421624).sum := by decide
  have hdescent : baseEnd_4421624 < baseStart_4421624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421628 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_4421628 : Nat := 118140960795 + 4421628 * 2 ^ 59
def prefixEnd_4421628 : Nat := 4983230072969 + 3 ^ 40 * 4421628 * 2
def baseEnd_4421628 : Nat := 2270420439378331593815309

theorem tailTrace_4421628 : CollatzResearch.WordTrace tailWord_4421628 prefixEnd_4421628 2270420439378331593815309 := by
  unfold tailWord_4421628
  simp only [CollatzResearch.WordTrace]
  refine ⟨80635011012602192393316769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107513348016802923191089025 80635011012602192393316769)
  ·
    refine ⟨60476258259451644294987577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80635011012602192393316769 60476258259451644294987577)
    ·
      refine ⟨45357193694588733221240683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60476258259451644294987577 45357193694588733221240683)
      ·
        refine ⟨68035790541883099831861025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45357193694588733221240683 68035790541883099831861025)
        ·
          refine ⟨51026842906412324873895769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68035790541883099831861025 51026842906412324873895769)
          ·
            refine ⟨38270132179809243655421827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51026842906412324873895769 38270132179809243655421827)
            ·
              refine ⟨57405198269713865483132741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38270132179809243655421827 57405198269713865483132741)
              ·
                refine ⟨10763474675571349778087389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57405198269713865483132741 10763474675571349778087389)
                ·
                  refine ⟨4036303003339256166782771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10763474675571349778087389 4036303003339256166782771)
                  ·
                    refine ⟨6054454505008884250174157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036303003339256166782771 6054454505008884250174157)
                    ·
                      refine ⟨2270420439378331593815309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054454505008884250174157 2270420439378331593815309)
                      ·
                        rfl

theorem cell23_4421628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_4421628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421628 prefixEnd_4421628 := by exact prefixLift 4421628
  have htrace : WordTrace (prefixWord ++ tailWord_4421628) baseStart_4421628 baseEnd_4421628 := by
    simpa [prefixWord, tailWord_4421628, baseEnd_4421628] using wordTrace_append hprefix tailTrace_4421628
  have hstable : (prefixWord ++ tailWord_4421628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421628).length < 2 ^ (prefixWord ++ tailWord_4421628).sum := by decide
  have hdescent : baseEnd_4421628 < baseStart_4421628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421681 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_4421681 : Nat := 118140960795 + 4421681 * 2 ^ 59
def prefixEnd_4421681 : Nat := 4983230072969 + 3 ^ 40 * 4421681 * 2
def baseEnd_4421681 : Nat := 2270447653853019886452565

theorem tailTrace_4421681 : CollatzResearch.WordTrace tailWord_4421681 prefixEnd_4421681 2270447653853019886452565 := by
  unfold tailWord_4421681
  simp only [CollatzResearch.WordTrace]
  refine ⟨161271955094012374838312897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107514636729341583225541931 161271955094012374838312897)
  ·
    refine ⟨120953966320509281128734673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161271955094012374838312897 120953966320509281128734673)
    ·
      refine ⟨90715474740381960846551005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120953966320509281128734673 90715474740381960846551005)
      ·
        refine ⟨34018303027643235317456627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90715474740381960846551005 34018303027643235317456627)
        ·
          refine ⟨51027454541464852976184941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34018303027643235317456627 51027454541464852976184941)
          ·
            refine ⟨19135295453049319866069353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51027454541464852976184941 19135295453049319866069353)
            ·
              refine ⟨14351471589786989899552015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19135295453049319866069353 14351471589786989899552015)
              ·
                refine ⟨21527207384680484849328023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14351471589786989899552015 21527207384680484849328023)
                ·
                  refine ⟨32290811077020727273992035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21527207384680484849328023 32290811077020727273992035)
                  ·
                    refine ⟨48436216615531090910988053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32290811077020727273992035 48436216615531090910988053)
                    ·
                      refine ⟨2270447653853019886452565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48436216615531090910988053 2270447653853019886452565)
                      ·
                        rfl

theorem cell23_4421681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_4421681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421681 prefixEnd_4421681 := by exact prefixLift 4421681
  have htrace : WordTrace (prefixWord ++ tailWord_4421681) baseStart_4421681 baseEnd_4421681 := by
    simpa [prefixWord, tailWord_4421681, baseEnd_4421681] using wordTrace_append hprefix tailTrace_4421681
  have hstable : (prefixWord ++ tailWord_4421681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421681).length < 2 ^ (prefixWord ++ tailWord_4421681).sum := by decide
  have hdescent : baseEnd_4421681 < baseStart_4421681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421685 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_4421685 : Nat := 118140960795 + 4421685 * 2 ^ 59
def prefixEnd_4421685 : Nat := 4983230072969 + 3 ^ 40 * 4421685 * 2
def baseEnd_4421685 : Nat := 2270449707775637870802547

theorem tailTrace_4421685 : CollatzResearch.WordTrace tailWord_4421685 prefixEnd_4421685 2270449707775637870802547 := by
  unfold tailWord_4421685
  simp only [CollatzResearch.WordTrace]
  refine ⟨161272100985997883521458509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107514733990665255680972339 161272100985997883521458509)
  ·
    refine ⟨60477037869749206320546941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161272100985997883521458509 60477037869749206320546941)
    ·
      refine ⟨22678889201155952370205103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60477037869749206320546941 22678889201155952370205103)
      ·
        refine ⟨34018333801733928555307655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22678889201155952370205103 34018333801733928555307655)
        ·
          refine ⟨51027500702600892832961483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34018333801733928555307655 51027500702600892832961483)
          ·
            refine ⟨76541251053901339249442225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51027500702600892832961483 76541251053901339249442225)
            ·
              refine ⟨57405938290426004437081669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76541251053901339249442225 57405938290426004437081669)
              ·
                refine ⟨10763613429454875831952813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57405938290426004437081669 10763613429454875831952813)
                ·
                  refine ⟨4036355036045578436982305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10763613429454875831952813 4036355036045578436982305)
                  ·
                    refine ⟨3027266277034183827736729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036355036045578436982305 3027266277034183827736729)
                    ·
                      refine ⟨2270449707775637870802547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027266277034183827736729 2270449707775637870802547)
                      ·
                        rfl

theorem cell23_4421685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_4421685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421685 prefixEnd_4421685 := by exact prefixLift 4421685
  have htrace : WordTrace (prefixWord ++ tailWord_4421685) baseStart_4421685 baseEnd_4421685 := by
    simpa [prefixWord, tailWord_4421685, baseEnd_4421685] using wordTrace_append hprefix tailTrace_4421685
  have hstable : (prefixWord ++ tailWord_4421685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421685).length < 2 ^ (prefixWord ++ tailWord_4421685).sum := by decide
  have hdescent : baseEnd_4421685 < baseStart_4421685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421705 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 1, 2, 3]
def baseStart_4421705 : Nat := 118140960795 + 4421705 * 2 ^ 59
def prefixEnd_4421705 : Nat := 4983230072969 + 3 ^ 40 * 4421705 * 2
def baseEnd_4421705 : Nat := 2270459977388727792552455

theorem tailTrace_4421705 : CollatzResearch.WordTrace tailWord_4421705 prefixEnd_4421705 2270459977388727792552455 := by
  unfold tailWord_4421705
  simp only [CollatzResearch.WordTrace]
  refine ⟨161272830445925426937186569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107515220297283617958124379 161272830445925426937186569)
  ·
    refine ⟨120954622834444070202889927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161272830445925426937186569 120954622834444070202889927)
    ·
      refine ⟨181431934251666105304334891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120954622834444070202889927 181431934251666105304334891)
      ·
        refine ⟨272147901377499157956502337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181431934251666105304334891 272147901377499157956502337)
        ·
          refine ⟨204110926033124368467376753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272147901377499157956502337 204110926033124368467376753)
          ·
            refine ⟨153083194524843276350532565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204110926033124368467376753 153083194524843276350532565)
            ·
              refine ⟨3587887371676014289465607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 153083194524843276350532565 3587887371676014289465607)
              ·
                refine ⟨5381831057514021434198411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587887371676014289465607 5381831057514021434198411)
                ·
                  refine ⟨8072746586271032151297617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381831057514021434198411 8072746586271032151297617)
                  ·
                    refine ⟨6054559939703274113473213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8072746586271032151297617 6054559939703274113473213)
                    ·
                      refine ⟨2270459977388727792552455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054559939703274113473213 2270459977388727792552455)
                      ·
                        rfl

theorem cell23_4421705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 2, 3].length) (baseStart_4421705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421705 prefixEnd_4421705 := by exact prefixLift 4421705
  have htrace : WordTrace (prefixWord ++ tailWord_4421705) baseStart_4421705 baseEnd_4421705 := by
    simpa [prefixWord, tailWord_4421705, baseEnd_4421705] using wordTrace_append hprefix tailTrace_4421705
  have hstable : (prefixWord ++ tailWord_4421705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421705).length < 2 ^ (prefixWord ++ tailWord_4421705).sum := by decide
  have hdescent : baseEnd_4421705 < baseStart_4421705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421719 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 1, 2, 2]
def baseStart_4421719 : Nat := 118140960795 + 4421719 * 2 ^ 59
def prefixEnd_4421719 : Nat := 4983230072969 + 3 ^ 40 * 4421719 * 2
def baseEnd_4421719 : Nat := 2270467166117890737777391

theorem tailTrace_4421719 : CollatzResearch.WordTrace tailWord_4421719 prefixEnd_4421719 2270467166117890737777391 := by
  unfold tailWord_4421719
  simp only [CollatzResearch.WordTrace]
  refine ⟨161273341067874707328196211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107515560711916471552130807 161273341067874707328196211)
  ·
    refine ⟨241910011601812060992294317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161273341067874707328196211 241910011601812060992294317)
    ·
      refine ⟨90716254350679522872110369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241910011601812060992294317 90716254350679522872110369)
      ·
        refine ⟨68037190763009642154082777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90716254350679522872110369 68037190763009642154082777)
        ·
          refine ⟨51027893072257231615562083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68037190763009642154082777 51027893072257231615562083)
          ·
            refine ⟨76541839608385847423343125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51027893072257231615562083 76541839608385847423343125)
            ·
              refine ⟨3587898731643086597969209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76541839608385847423343125 3587898731643086597969209)
              ·
                refine ⟨2690924048732314948476907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587898731643086597969209 2690924048732314948476907)
                ·
                  refine ⟨4036386073098472422715361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690924048732314948476907 4036386073098472422715361)
                  ·
                    refine ⟨3027289554823854317036521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036386073098472422715361 3027289554823854317036521)
                    ·
                      refine ⟨2270467166117890737777391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027289554823854317036521 2270467166117890737777391)
                      ·
                        rfl

theorem cell23_4421719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_4421719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421719 prefixEnd_4421719 := by exact prefixLift 4421719
  have htrace : WordTrace (prefixWord ++ tailWord_4421719) baseStart_4421719 baseEnd_4421719 := by
    simpa [prefixWord, tailWord_4421719, baseEnd_4421719] using wordTrace_append hprefix tailTrace_4421719
  have hstable : (prefixWord ++ tailWord_4421719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421719).length < 2 ^ (prefixWord ++ tailWord_4421719).sum := by decide
  have hdescent : baseEnd_4421719 < baseStart_4421719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421725 : List Nat := [1, 4, 4, 1, 1, 3, 1, 8]
def baseStart_4421725 : Nat := 118140960795 + 4421725 * 2 ^ 59
def prefixEnd_4421725 : Nat := 4983230072969 + 3 ^ 40 * 4421725 * 2
def baseEnd_4421725 : Nat := 84091490629696952381569

theorem tailTrace_4421725 : CollatzResearch.WordTrace tailWord_4421725 prefixEnd_4421725 84091490629696952381569 := by
  unfold tailWord_4421725
  simp only [CollatzResearch.WordTrace]
  refine ⟨161273559905852970352914629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107515706603901980235276419 161273559905852970352914629)
  ·
    refine ⟨30238792482347431941171493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161273559905852970352914629 30238792482347431941171493)
    ·
      refine ⟨5669773590440143488969655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30238792482347431941171493 5669773590440143488969655)
      ·
        refine ⟨8504660385660215233454483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5669773590440143488969655 8504660385660215233454483)
        ·
          refine ⟨12756990578490322850181725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8504660385660215233454483 12756990578490322850181725)
          ·
            refine ⟨4783871466933871068818147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12756990578490322850181725 4783871466933871068818147)
            ·
              refine ⟨7175807200400806603227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4783871466933871068818147 7175807200400806603227221)
              ·
                refine ⟨84091490629696952381569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7175807200400806603227221 84091490629696952381569)
                ·
                  rfl

theorem cell23_4421725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 8].length) (baseStart_4421725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421725 prefixEnd_4421725 := by exact prefixLift 4421725
  have htrace : WordTrace (prefixWord ++ tailWord_4421725) baseStart_4421725 baseEnd_4421725 := by
    simpa [prefixWord, tailWord_4421725, baseEnd_4421725] using wordTrace_append hprefix tailTrace_4421725
  have hstable : (prefixWord ++ tailWord_4421725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421725).length < 2 ^ (prefixWord ++ tailWord_4421725).sum := by decide
  have hdescent : baseEnd_4421725 < baseStart_4421725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421735 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_4421735 : Nat := 118140960795 + 4421735 * 2 ^ 59
def prefixEnd_4421735 : Nat := 4983230072969 + 3 ^ 40 * 4421735 * 2
def baseEnd_4421735 : Nat := 2270475381808362675177317

theorem tailTrace_4421735 : CollatzResearch.WordTrace tailWord_4421735 prefixEnd_4421735 2270475381808362675177317 := by
  unfold tailWord_4421735
  simp only [CollatzResearch.WordTrace]
  refine ⟨161273924635816742060778659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107515949757211161373852439 161273924635816742060778659)
  ·
    refine ⟨241910886953725113091167989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161273924635816742060778659 241910886953725113091167989)
    ·
      refine ⟨22679145651911729352296999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241910886953725113091167989 22679145651911729352296999)
      ·
        refine ⟨34018718477867594028445499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22679145651911729352296999 34018718477867594028445499)
        ·
          refine ⟨51028077716801391042668249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34018718477867594028445499 51028077716801391042668249)
          ·
            refine ⟨38271058287601043282001187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51028077716801391042668249 38271058287601043282001187)
            ·
              refine ⟨57406587431401564923001781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38271058287601043282001187 57406587431401564923001781)
              ·
                refine ⟨5381867571693896711531417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57406587431401564923001781 5381867571693896711531417)
                ·
                  refine ⟨4036400678770422533648563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5381867571693896711531417 4036400678770422533648563)
                  ·
                    refine ⟨6054601018155633800472845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036400678770422533648563 6054601018155633800472845)
                    ·
                      refine ⟨2270475381808362675177317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054601018155633800472845 2270475381808362675177317)
                      ·
                        rfl

theorem cell23_4421735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_4421735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421735 prefixEnd_4421735 := by exact prefixLift 4421735
  have htrace : WordTrace (prefixWord ++ tailWord_4421735) baseStart_4421735 baseEnd_4421735 := by
    simpa [prefixWord, tailWord_4421735, baseEnd_4421735] using wordTrace_append hprefix tailTrace_4421735
  have hstable : (prefixWord ++ tailWord_4421735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421735).length < 2 ^ (prefixWord ++ tailWord_4421735).sum := by decide
  have hdescent : baseEnd_4421735 < baseStart_4421735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421745 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_4421745 : Nat := 118140960795 + 4421745 * 2 ^ 59
def prefixEnd_4421745 : Nat := 4983230072969 + 3 ^ 40 * 4421745 * 2
def baseEnd_4421745 : Nat := 2270480516614907636052271

theorem tailTrace_4421745 : CollatzResearch.WordTrace tailWord_4421745 prefixEnd_4421745 2270480516614907636052271 := by
  unfold tailWord_4421745
  simp only [CollatzResearch.WordTrace]
  refine ⟨161274289365780513768642689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107516192910520342512428459 161274289365780513768642689)
  ·
    refine ⟨120955717024335385326482017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161274289365780513768642689 120955717024335385326482017)
    ·
      refine ⟨90716787768251538994861513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120955717024335385326482017 90716787768251538994861513)
      ·
        refine ⟨68037590826188654246146135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90716787768251538994861513 68037590826188654246146135)
        ·
          refine ⟨102056386239282981369219203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68037590826188654246146135 102056386239282981369219203)
          ·
            refine ⟨153084579358924472053828805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102056386239282981369219203 153084579358924472053828805)
            ·
              refine ⟨28703358629798338510092901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153084579358924472053828805 28703358629798338510092901)
              ·
                refine ⟨5381879743087188470642419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28703358629798338510092901 5381879743087188470642419)
                ·
                  refine ⟨8072819614630782705963629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381879743087188470642419 8072819614630782705963629)
                  ·
                    refine ⟨3027307355486543514736361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8072819614630782705963629 3027307355486543514736361)
                    ·
                      refine ⟨2270480516614907636052271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027307355486543514736361 2270480516614907636052271)
                      ·
                        rfl

theorem cell23_4421745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_4421745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421745 prefixEnd_4421745 := by exact prefixLift 4421745
  have htrace : WordTrace (prefixWord ++ tailWord_4421745) baseStart_4421745 baseEnd_4421745 := by
    simpa [prefixWord, tailWord_4421745, baseEnd_4421745] using wordTrace_append hprefix tailTrace_4421745
  have hstable : (prefixWord ++ tailWord_4421745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421745).length < 2 ^ (prefixWord ++ tailWord_4421745).sum := by decide
  have hdescent : baseEnd_4421745 < baseStart_4421745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421768 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_4421768 : Nat := 118140960795 + 4421768 * 2 ^ 59
def prefixEnd_4421768 : Nat := 4983230072969 + 3 ^ 40 * 4421768 * 2
def baseEnd_4421768 : Nat := 756830775556653682021555

theorem tailTrace_4421768 : CollatzResearch.WordTrace tailWord_4421768 prefixEnd_4421768 756830775556653682021555 := by
  unfold tailWord_4421768
  simp only [CollatzResearch.WordTrace]
  refine ⟨80637564122348594348364979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107516752163131459131153305 80637564122348594348364979)
  ·
    refine ⟨120956346183522891522547469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80637564122348594348364979 120956346183522891522547469)
    ·
      refine ⟨45358629818821084320955301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120956346183522891522547469 45358629818821084320955301)
      ·
        refine ⟨8504743091028953310179119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45358629818821084320955301 8504743091028953310179119)
        ·
          refine ⟨12757114636543429965268679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8504743091028953310179119 12757114636543429965268679)
          ·
            refine ⟨19135671954815144947903019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12757114636543429965268679 19135671954815144947903019)
            ·
              refine ⟨28703507932222717421854529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19135671954815144947903019 28703507932222717421854529)
              ·
                refine ⟨21527630949167038066390897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28703507932222717421854529 21527630949167038066390897)
                ·
                  refine ⟨16145723211875278549793173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21527630949167038066390897 16145723211875278549793173)
                  ·
                    refine ⟨756830775556653682021555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16145723211875278549793173 756830775556653682021555)
                    ·
                      rfl

theorem cell23_4421768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_4421768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421768 prefixEnd_4421768 := by exact prefixLift 4421768
  have htrace : WordTrace (prefixWord ++ tailWord_4421768) baseStart_4421768 baseEnd_4421768 := by
    simpa [prefixWord, tailWord_4421768, baseEnd_4421768] using wordTrace_append hprefix tailTrace_4421768
  have hstable : (prefixWord ++ tailWord_4421768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421768).length < 2 ^ (prefixWord ++ tailWord_4421768).sum := by decide
  have hdescent : baseEnd_4421768 < baseStart_4421768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421788 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4421788 : Nat := 118140960795 + 4421788 * 2 ^ 59
def prefixEnd_4421788 : Nat := 4983230072969 + 3 ^ 40 * 4421788 * 2
def baseEnd_4421788 : Nat := 2270502596283050967814573

theorem tailTrace_4421788 : CollatzResearch.WordTrace tailWord_4421788 prefixEnd_4421788 2270502596283050967814573 := by
  unfold tailWord_4421788
  simp only [CollatzResearch.WordTrace]
  refine ⟨80637928852312366056229009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107517238469749821408305345 80637928852312366056229009)
  ·
    refine ⟨60478446639234274542171757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80637928852312366056229009 60478446639234274542171757)
    ·
      refine ⟨22679417489712852953314409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60478446639234274542171757 22679417489712852953314409)
      ·
        refine ⟨17009563117284639714985807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22679417489712852953314409 17009563117284639714985807)
        ·
          refine ⟨25514344675926959572478711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17009563117284639714985807 25514344675926959572478711)
          ·
            refine ⟨38271517013890439358718067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25514344675926959572478711 38271517013890439358718067)
            ·
              refine ⟨57407275520835659038077101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38271517013890439358718067 57407275520835659038077101)
              ·
                refine ⟨21527728320313372139278913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57407275520835659038077101 21527728320313372139278913)
                ·
                  refine ⟨16145796240235029104459185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21527728320313372139278913 16145796240235029104459185)
                  ·
                    refine ⟨12109347180176271828344389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16145796240235029104459185 12109347180176271828344389)
                    ·
                      refine ⟨2270502596283050967814573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12109347180176271828344389 2270502596283050967814573)
                      ·
                        rfl

theorem cell23_4421788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4421788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421788 prefixEnd_4421788 := by exact prefixLift 4421788
  have htrace : WordTrace (prefixWord ++ tailWord_4421788) baseStart_4421788 baseEnd_4421788 := by
    simpa [prefixWord, tailWord_4421788, baseEnd_4421788] using wordTrace_append hprefix tailTrace_4421788
  have hstable : (prefixWord ++ tailWord_4421788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421788).length < 2 ^ (prefixWord ++ tailWord_4421788).sum := by decide
  have hdescent : baseEnd_4421788 < baseStart_4421788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421792 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2]
def baseStart_4421792 : Nat := 118140960795 + 4421792 * 2 ^ 59
def prefixEnd_4421792 : Nat := 4983230072969 + 3 ^ 40 * 4421792 * 2
def baseEnd_4421792 : Nat := 2270504650205668952164555

theorem tailTrace_4421792 : CollatzResearch.WordTrace tailWord_4421792 prefixEnd_4421792 2270504650205668952164555 := by
  unfold tailWord_4421792
  simp only [CollatzResearch.WordTrace]
  refine ⟨80638001798305120397801815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107517335731073493863735753 80638001798305120397801815)
  ·
    refine ⟨120957002697457680596702723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80638001798305120397801815 120957002697457680596702723)
    ·
      refine ⟨181435504046186520895054085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120957002697457680596702723 181435504046186520895054085)
      ·
        refine ⟨34019157008659972667822641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181435504046186520895054085 34019157008659972667822641)
        ·
          refine ⟨25514367756494979500866981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34019157008659972667822641 25514367756494979500866981)
          ·
            refine ⟨4783943954342808656412559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25514367756494979500866981 4783943954342808656412559)
            ·
              refine ⟨7175915931514212984618839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4783943954342808656412559 7175915931514212984618839)
              ·
                refine ⟨10763873897271319476928259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7175915931514212984618839 10763873897271319476928259)
                ·
                  refine ⟨16145810845906979215392389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10763873897271319476928259 16145810845906979215392389)
                  ·
                    refine ⟨3027339533607558602886073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16145810845906979215392389 3027339533607558602886073)
                    ·
                      refine ⟨2270504650205668952164555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027339533607558602886073 2270504650205668952164555)
                      ·
                        rfl

theorem cell23_4421792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_4421792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421792 prefixEnd_4421792 := by exact prefixLift 4421792
  have htrace : WordTrace (prefixWord ++ tailWord_4421792) baseStart_4421792 baseEnd_4421792 := by
    simpa [prefixWord, tailWord_4421792, baseEnd_4421792] using wordTrace_append hprefix tailTrace_4421792
  have hstable : (prefixWord ++ tailWord_4421792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421792).length < 2 ^ (prefixWord ++ tailWord_4421792).sum := by decide
  have hdescent : baseEnd_4421792 < baseStart_4421792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421815 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 5]
def baseStart_4421815 : Nat := 118140960795 + 4421815 * 2 ^ 59
def prefixEnd_4421815 : Nat := 4983230072969 + 3 ^ 40 * 4421815 * 2
def baseEnd_4421815 : Nat := 252279606695635818019661

theorem tailTrace_4421815 : CollatzResearch.WordTrace tailWord_4421815 prefixEnd_4421815 252279606695635818019661 := by
  unfold tailWord_4421815
  simp only [CollatzResearch.WordTrace]
  refine ⟨161276842475526915723690899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107517894983684610482460599 161276842475526915723690899)
  ·
    refine ⟨241915263713290373585536349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161276842475526915723690899 241915263713290373585536349)
    ·
      refine ⟨90718223892483890094576131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241915263713290373585536349 90718223892483890094576131)
      ·
        refine ⟨136077335838725835141864197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90718223892483890094576131 136077335838725835141864197)
        ·
          refine ⟨25514500469761094089099537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136077335838725835141864197 25514500469761094089099537)
          ·
            refine ⟨19135875352320820566824653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25514500469761094089099537 19135875352320820566824653)
            ·
              refine ⟨7175953257120307712559245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19135875352320820566824653 7175953257120307712559245)
              ·
                refine ⟨2690982471420115392209717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7175953257120307712559245 2690982471420115392209717)
                ·
                  refine ⟨252279606695635818019661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2690982471420115392209717 252279606695635818019661)
                  ·
                    rfl

theorem cell23_4421815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 5].length) (baseStart_4421815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421815 prefixEnd_4421815 := by exact prefixLift 4421815
  have htrace : WordTrace (prefixWord ++ tailWord_4421815) baseStart_4421815 baseEnd_4421815 := by
    simpa [prefixWord, tailWord_4421815, baseEnd_4421815] using wordTrace_append hprefix tailTrace_4421815
  have hstable : (prefixWord ++ tailWord_4421815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421815).length < 2 ^ (prefixWord ++ tailWord_4421815).sum := by decide
  have hdescent : baseEnd_4421815 < baseStart_4421815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421826 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4421826 : Nat := 118140960795 + 4421826 * 2 ^ 59
def prefixEnd_4421826 : Nat := 4983230072969 + 3 ^ 40 * 4421826 * 2
def baseEnd_4421826 : Nat := 2270522108547921819139399

theorem tailTrace_4421826 : CollatzResearch.WordTrace tailWord_4421826 prefixEnd_4421826 2270522108547921819139399 := by
  unfold tailWord_4421826
  simp only [CollatzResearch.WordTrace]
  refine ⟨40319310919621766150585333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107518162452324709734894221 40319310919621766150585333)
  ·
    refine ⟨3779935398714540576617375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40319310919621766150585333 3779935398714540576617375)
    ·
      refine ⟨5669903098071810864926063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779935398714540576617375 5669903098071810864926063)
      ·
        refine ⟨8504854647107716297389095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5669903098071810864926063 8504854647107716297389095)
        ·
          refine ⟨12757281970661574446083643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8504854647107716297389095 12757281970661574446083643)
          ·
            refine ⟨19135922955992361669125465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12757281970661574446083643 19135922955992361669125465)
            ·
              refine ⟨14351942216994271251844099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19135922955992361669125465 14351942216994271251844099)
              ·
                refine ⟨21527913325491406877766149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14351942216994271251844099 21527913325491406877766149)
                ·
                  refine ⟨4036483748529638789581153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21527913325491406877766149 4036483748529638789581153)
                  ·
                    refine ⟨3027362811397229092185865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036483748529638789581153 3027362811397229092185865)
                    ·
                      refine ⟨2270522108547921819139399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027362811397229092185865 2270522108547921819139399)
                      ·
                        rfl

theorem cell23_4421826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4421826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421826 prefixEnd_4421826 := by exact prefixLift 4421826
  have htrace : WordTrace (prefixWord ++ tailWord_4421826) baseStart_4421826 baseEnd_4421826 := by
    simpa [prefixWord, tailWord_4421826, baseEnd_4421826] using wordTrace_append hprefix tailTrace_4421826
  have hstable : (prefixWord ++ tailWord_4421826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421826).length < 2 ^ (prefixWord ++ tailWord_4421826).sum := by decide
  have hdescent : baseEnd_4421826 < baseStart_4421826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421831 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_4421831 : Nat := 118140960795 + 4421831 * 2 ^ 59
def prefixEnd_4421831 : Nat := 4983230072969 + 3 ^ 40 * 4421831 * 2
def baseEnd_4421831 : Nat := 2270524675951194299576875

theorem tailTrace_4421831 : CollatzResearch.WordTrace tailWord_4421831 prefixEnd_4421831 2270524675951194299576875 := by
  unfold tailWord_4421831
  simp only [CollatzResearch.WordTrace]
  refine ⟨161277426043468950456273347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107518284028979300304182231 161277426043468950456273347)
  ·
    refine ⟨241916139065203425684410021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161277426043468950456273347 241916139065203425684410021)
    ·
      refine ⟨45359276074725642315826879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241916139065203425684410021 45359276074725642315826879)
      ·
        refine ⟨68038914112088463473740319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45359276074725642315826879 68038914112088463473740319)
        ·
          refine ⟨102058371168132695210610479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68038914112088463473740319 102058371168132695210610479)
          ·
            refine ⟨153087556752199042815915719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102058371168132695210610479 153087556752199042815915719)
            ·
              refine ⟨229631335128298564223873579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153087556752199042815915719 229631335128298564223873579)
              ·
                refine ⟨344447002692447846335810369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229631335128298564223873579 344447002692447846335810369)
                ·
                  refine ⟨258335252019335884751857777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344447002692447846335810369 258335252019335884751857777)
                  ·
                    refine ⟨193751439014501913563893333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258335252019335884751857777 193751439014501913563893333)
                    ·
                      refine ⟨2270524675951194299576875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 193751439014501913563893333 2270524675951194299576875)
                      ·
                        rfl

theorem cell23_4421831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_4421831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421831 prefixEnd_4421831 := by exact prefixLift 4421831
  have htrace : WordTrace (prefixWord ++ tailWord_4421831) baseStart_4421831 baseEnd_4421831 := by
    simpa [prefixWord, tailWord_4421831, baseEnd_4421831] using wordTrace_append hprefix tailTrace_4421831
  have hstable : (prefixWord ++ tailWord_4421831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421831).length < 2 ^ (prefixWord ++ tailWord_4421831).sum := by decide
  have hdescent : baseEnd_4421831 < baseStart_4421831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421838 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_4421838 : Nat := 118140960795 + 4421838 * 2 ^ 59
def prefixEnd_4421838 : Nat := 4983230072969 + 3 ^ 40 * 4421838 * 2
def baseEnd_4421838 : Nat := 2270528270315775772189343

theorem tailTrace_4421838 : CollatzResearch.WordTrace tailWord_4421838 prefixEnd_4421838 2270528270315775772189343 := by
  unfold tailWord_4421838
  simp only [CollatzResearch.WordTrace]
  refine ⟨20159710169305448831472271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107518454236295727101185445 20159710169305448831472271)
  ·
    refine ⟨30239565253958173247208407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20159710169305448831472271 30239565253958173247208407)
    ·
      refine ⟨45359347880937259870812611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30239565253958173247208407 45359347880937259870812611)
      ·
        refine ⟨68039021821405889806218917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45359347880937259870812611 68039021821405889806218917)
        ·
          refine ⟨12757316591513604338666047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68039021821405889806218917 12757316591513604338666047)
          ·
            refine ⟨19135974887270406507999071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12757316591513604338666047 19135974887270406507999071)
            ·
              refine ⟨28703962330905609761998607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19135974887270406507999071 28703962330905609761998607)
              ·
                refine ⟨43055943496358414642997911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28703962330905609761998607 43055943496358414642997911)
                ·
                  refine ⟨64583915244537621964496867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43055943496358414642997911 64583915244537621964496867)
                  ·
                    refine ⟨96875872866806432946745301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64583915244537621964496867 96875872866806432946745301)
                    ·
                      refine ⟨2270528270315775772189343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96875872866806432946745301 2270528270315775772189343)
                      ·
                        rfl

theorem cell23_4421838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_4421838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421838 prefixEnd_4421838 := by exact prefixLift 4421838
  have htrace : WordTrace (prefixWord ++ tailWord_4421838) baseStart_4421838 baseEnd_4421838 := by
    simpa [prefixWord, tailWord_4421838, baseEnd_4421838] using wordTrace_append hprefix tailTrace_4421838
  have hstable : (prefixWord ++ tailWord_4421838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421838).length < 2 ^ (prefixWord ++ tailWord_4421838).sum := by decide
  have hdescent : baseEnd_4421838 < baseStart_4421838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421888 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 6]
def baseStart_4421888 : Nat := 118140960795 + 4421888 * 2 ^ 59
def prefixEnd_4421888 : Nat := 4983230072969 + 3 ^ 40 * 4421888 * 2
def baseEnd_4421888 : Nat := 252283771594277841840457

theorem tailTrace_4421888 : CollatzResearch.WordTrace tailWord_4421888 prefixEnd_4421888 252283771594277841840457 := by
  unfold tailWord_4421888
  simp only [CollatzResearch.WordTrace]
  refine ⟨80639752502131224595549159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107519670002841632794065545 80639752502131224595549159)
  ·
    refine ⟨120959628753196836893323739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80639752502131224595549159 120959628753196836893323739)
    ·
      refine ⟨181439443129795255339985609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120959628753196836893323739 181439443129795255339985609)
      ·
        refine ⟨136079582347346441504989207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181439443129795255339985609 136079582347346441504989207)
        ·
          refine ⟨204119373521019662257483811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136079582347346441504989207 204119373521019662257483811)
          ·
            refine ⟨306179060281529493386225717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204119373521019662257483811 306179060281529493386225717)
            ·
              refine ⟨28704286901393390004958661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 306179060281529493386225717 28704286901393390004958661)
              ·
                refine ⟨5382053794011260625929749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28704286901393390004958661 5382053794011260625929749)
                ·
                  refine ⟨252283771594277841840457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5382053794011260625929749 252283771594277841840457)
                  ·
                    rfl

theorem cell23_4421888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_4421888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421888 prefixEnd_4421888 := by exact prefixLift 4421888
  have htrace : WordTrace (prefixWord ++ tailWord_4421888) baseStart_4421888 baseEnd_4421888 := by
    simpa [prefixWord, tailWord_4421888, baseEnd_4421888] using wordTrace_append hprefix tailTrace_4421888
  have hstable : (prefixWord ++ tailWord_4421888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421888).length < 2 ^ (prefixWord ++ tailWord_4421888).sum := by decide
  have hdescent : baseEnd_4421888 < baseStart_4421888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421915 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 3]
def baseStart_4421915 : Nat := 118140960795 + 4421915 * 2 ^ 59
def prefixEnd_4421915 : Nat := 4983230072969 + 3 ^ 40 * 4421915 * 2
def baseEnd_4421915 : Nat := 2270567808326171970926489

theorem tailTrace_4421915 : CollatzResearch.WordTrace tailWord_4421915 prefixEnd_4421915 2270567808326171970926489 := by
  unfold tailWord_4421915
  simp only [CollatzResearch.WordTrace]
  refine ⟨161280489775164632802331199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107520326516776421868220799 161280489775164632802331199)
  ·
    refine ⟨241920734662746949203496799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161280489775164632802331199 241920734662746949203496799)
    ·
      refine ⟨362881101994120423805245199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241920734662746949203496799 362881101994120423805245199)
      ·
        refine ⟨544321652991180635707867799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362881101994120423805245199 544321652991180635707867799)
        ·
          refine ⟨816482479486770953561801699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544321652991180635707867799 816482479486770953561801699)
          ·
            refine ⟨1224723719230156430342702549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816482479486770953561801699 1224723719230156430342702549)
            ·
              refine ⟨28704462169456791336157091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1224723719230156430342702549 28704462169456791336157091)
              ·
                refine ⟨43056693254185187004235637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28704462169456791336157091 43056693254185187004235637)
                ·
                  refine ⟨4036564992579861281647091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43056693254185187004235637 4036564992579861281647091)
                  ·
                    refine ⟨6054847488869791922470637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036564992579861281647091 6054847488869791922470637)
                    ·
                      refine ⟨2270567808326171970926489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6054847488869791922470637 2270567808326171970926489)
                      ·
                        rfl

theorem cell23_4421915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 3].length) (baseStart_4421915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421915 prefixEnd_4421915 := by exact prefixLift 4421915
  have htrace : WordTrace (prefixWord ++ tailWord_4421915) baseStart_4421915 baseEnd_4421915 := by
    simpa [prefixWord, tailWord_4421915, baseEnd_4421915] using wordTrace_append hprefix tailTrace_4421915
  have hstable : (prefixWord ++ tailWord_4421915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421915).length < 2 ^ (prefixWord ++ tailWord_4421915).sum := by decide
  have hdescent : baseEnd_4421915 < baseStart_4421915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421972 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_4421972 : Nat := 118140960795 + 4421972 * 2 ^ 59
def prefixEnd_4421972 : Nat := 4983230072969 + 3 ^ 40 * 4421972 * 2
def baseEnd_4421972 : Nat := 2270597076723478247913727

theorem tailTrace_4421972 : CollatzResearch.WordTrace tailWord_4421972 prefixEnd_4421972 2270597076723478247913727 := by
  unfold tailWord_4421972
  simp only [CollatzResearch.WordTrace]
  refine ⟨80641284367979065768578085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107521712490638754358104113 80641284367979065768578085)
  ·
    refine ⟨15120240818996074831608391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80641284367979065768578085 15120240818996074831608391)
    ·
      refine ⟨22680361228494112247412587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15120240818996074831608391 22680361228494112247412587)
      ·
        refine ⟨34020541842741168371118881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22680361228494112247412587 34020541842741168371118881)
        ·
          refine ⟨25515406382055876278339161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34020541842741168371118881 25515406382055876278339161)
          ·
            refine ⟨19136554786541907208754371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25515406382055876278339161 19136554786541907208754371)
            ·
              refine ⟨28704832179812860813131557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19136554786541907208754371 28704832179812860813131557)
              ·
                refine ⟨5382156033714911402462167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28704832179812860813131557 5382156033714911402462167)
                ·
                  refine ⟨8073234050572367103693251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382156033714911402462167 8073234050572367103693251)
                  ·
                    refine ⟨12109851075858550655539877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8073234050572367103693251 12109851075858550655539877)
                    ·
                      refine ⟨2270597076723478247913727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12109851075858550655539877 2270597076723478247913727)
                      ·
                        rfl

theorem cell23_4421972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_4421972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421972 prefixEnd_4421972 := by exact prefixLift 4421972
  have htrace : WordTrace (prefixWord ++ tailWord_4421972) baseStart_4421972 baseEnd_4421972 := by
    simpa [prefixWord, tailWord_4421972, baseEnd_4421972] using wordTrace_append hprefix tailTrace_4421972
  have hstable : (prefixWord ++ tailWord_4421972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421972).length < 2 ^ (prefixWord ++ tailWord_4421972).sum := by decide
  have hdescent : baseEnd_4421972 < baseStart_4421972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4421992 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4421992 : Nat := 118140960795 + 4421992 * 2 ^ 59
def prefixEnd_4421992 : Nat := 4983230072969 + 3 ^ 40 * 4421992 * 2
def baseEnd_4421992 : Nat := 2270607346336568169663635

theorem tailTrace_4421992 : CollatzResearch.WordTrace tailWord_4421992 prefixEnd_4421992 2270607346336568169663635 := by
  unfold tailWord_4421992
  simp only [CollatzResearch.WordTrace]
  refine ⟨80641649097942837476442115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107522198797257116635256153 80641649097942837476442115)
  ·
    refine ⟨120962473646914256214663173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80641649097942837476442115 120962473646914256214663173)
    ·
      refine ⟨22680463808796423040249345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120962473646914256214663173 22680463808796423040249345)
      ·
        refine ⟨17010347856597317280187009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22680463808796423040249345 17010347856597317280187009)
        ·
          refine ⟨12757760892447987960140257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17010347856597317280187009 12757760892447987960140257)
          ·
            refine ⟨9568320669335990970105193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12757760892447987960140257 9568320669335990970105193)
            ·
              refine ⟨7176240502001993227578895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9568320669335990970105193 7176240502001993227578895)
              ·
                refine ⟨10764360753002989841368343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7176240502001993227578895 10764360753002989841368343)
                ·
                  refine ⟨16146541129504484762052515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10764360753002989841368343 16146541129504484762052515)
                  ·
                    refine ⟨24219811694256727143078773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16146541129504484762052515 24219811694256727143078773)
                    ·
                      refine ⟨2270607346336568169663635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24219811694256727143078773 2270607346336568169663635)
                      ·
                        rfl

theorem cell23_4421992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4421992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4421992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4421992 prefixEnd_4421992 := by exact prefixLift 4421992
  have htrace : WordTrace (prefixWord ++ tailWord_4421992) baseStart_4421992 baseEnd_4421992 := by
    simpa [prefixWord, tailWord_4421992, baseEnd_4421992] using wordTrace_append hprefix tailTrace_4421992
  have hstable : (prefixWord ++ tailWord_4421992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4421992).length < 2 ^ (prefixWord ++ tailWord_4421992).sum := by decide
  have hdescent : baseEnd_4421992 < baseStart_4421992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4421992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422056 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4422056 : Nat := 118140960795 + 4422056 * 2 ^ 59
def prefixEnd_4422056 : Nat := 4983230072969 + 3 ^ 40 * 4422056 * 2
def baseEnd_4422056 : Nat := 2270640209098455919263341

theorem tailTrace_4422056 : CollatzResearch.WordTrace tailWord_4422056 prefixEnd_4422056 2270640209098455919263341 := by
  unfold tailWord_4422056
  simp only [CollatzResearch.WordTrace]
  refine ⟨80642816233826906941607011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107523754978435875922142681 80642816233826906941607011)
  ·
    refine ⟨120964224350740360412410517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80642816233826906941607011 120964224350740360412410517)
    ·
      refine ⟨5670198016440954394331743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120964224350740360412410517 5670198016440954394331743)
      ·
        refine ⟨8505297024661431591497615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670198016440954394331743 8505297024661431591497615)
        ·
          refine ⟨12757945536992147387246423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505297024661431591497615 12757945536992147387246423)
          ·
            refine ⟨19136918305488221080869635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12757945536992147387246423 19136918305488221080869635)
            ·
              refine ⟨28705377458232331621304453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19136918305488221080869635 28705377458232331621304453)
              ·
                refine ⟨5382258273418562178994585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28705377458232331621304453 5382258273418562178994585)
                ·
                  refine ⟨4036693705063921634245939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5382258273418562178994585 4036693705063921634245939)
                  ·
                    refine ⟨6055040557595882451368909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036693705063921634245939 6055040557595882451368909)
                    ·
                      refine ⟨2270640209098455919263341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055040557595882451368909 2270640209098455919263341)
                      ·
                        rfl

theorem cell23_4422056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4422056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422056 prefixEnd_4422056 := by exact prefixLift 4422056
  have htrace : WordTrace (prefixWord ++ tailWord_4422056) baseStart_4422056 baseEnd_4422056 := by
    simpa [prefixWord, tailWord_4422056, baseEnd_4422056] using wordTrace_append hprefix tailTrace_4422056
  have hstable : (prefixWord ++ tailWord_4422056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422056).length < 2 ^ (prefixWord ++ tailWord_4422056).sum := by decide
  have hdescent : baseEnd_4422056 < baseStart_4422056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422095 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_4422095 : Nat := 118140960795 + 4422095 * 2 ^ 59
def prefixEnd_4422095 : Nat := 4983230072969 + 3 ^ 40 * 4422095 * 2
def baseEnd_4422095 : Nat := 2270660234843981266675661

theorem tailTrace_4422095 : CollatzResearch.WordTrace tailWord_4422095 prefixEnd_4422095 2270660234843981266675661 := by
  unfold tailWord_4422095
  simp only [CollatzResearch.WordTrace]
  refine ⟨161287054914512523543883739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107524703276341682362589159 161287054914512523543883739)
  ·
    refine ⟨241930582371768785315825609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161287054914512523543883739 241930582371768785315825609)
    ·
      refine ⟨181447936778826588986869207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241930582371768785315825609 181447936778826588986869207)
      ·
        refine ⟨272171905168239883480303811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181447936778826588986869207 272171905168239883480303811)
        ·
          refine ⟨408257857752359825220455717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272171905168239883480303811 408257857752359825220455717)
          ·
            refine ⟨76548348328567467228835447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 408257857752359825220455717 76548348328567467228835447)
            ·
              refine ⟨114822522492851200843253171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76548348328567467228835447 114822522492851200843253171)
              ·
                refine ⟨172233783739276801264879757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114822522492851200843253171 172233783739276801264879757)
                ·
                  refine ⟨64587668902228800474329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172233783739276801264879757 64587668902228800474329909)
                  ·
                    refine ⟨6055093959583950044468429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64587668902228800474329909 6055093959583950044468429)
                    ·
                      refine ⟨2270660234843981266675661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055093959583950044468429 2270660234843981266675661)
                      ·
                        rfl

theorem cell23_4422095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_4422095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422095 prefixEnd_4422095 := by exact prefixLift 4422095
  have htrace : WordTrace (prefixWord ++ tailWord_4422095) baseStart_4422095 baseEnd_4422095 := by
    simpa [prefixWord, tailWord_4422095, baseEnd_4422095] using wordTrace_append hprefix tailTrace_4422095
  have hstable : (prefixWord ++ tailWord_4422095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422095).length < 2 ^ (prefixWord ++ tailWord_4422095).sum := by decide
  have hdescent : baseEnd_4422095 < baseStart_4422095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422102 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4422102 : Nat := 118140960795 + 4422102 * 2 ^ 59
def prefixEnd_4422102 : Nat := 4983230072969 + 3 ^ 40 * 4422102 * 2
def baseEnd_4422102 : Nat := 252295981023173637698681

theorem tailTrace_4422102 : CollatzResearch.WordTrace tailWord_4422102 prefixEnd_4422102 252295981023173637698681 := by
  unfold tailWord_4422102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080456889092947733711785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107524873483658109159592373 10080456889092947733711785)
  ·
    refine ⟨7560342666819710800283839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10080456889092947733711785 7560342666819710800283839)
    ·
      refine ⟨11340514000229566200425759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7560342666819710800283839 11340514000229566200425759)
      ·
        refine ⟨17010771000344349300638639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11340514000229566200425759 17010771000344349300638639)
        ·
          refine ⟨25516156500516523950957959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17010771000344349300638639 25516156500516523950957959)
          ·
            refine ⟨38274234750774785926436939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25516156500516523950957959 38274234750774785926436939)
            ·
              refine ⟨57411352126162178889655409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38274234750774785926436939 57411352126162178889655409)
              ·
                refine ⟨43058514094621634167241557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57411352126162178889655409 43058514094621634167241557)
                ·
                  refine ⟨252295981023173637698681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43058514094621634167241557 252295981023173637698681)
                  ·
                    rfl

theorem cell23_4422102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4422102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422102 prefixEnd_4422102 := by exact prefixLift 4422102
  have htrace : WordTrace (prefixWord ++ tailWord_4422102) baseStart_4422102 baseEnd_4422102 := by
    simpa [prefixWord, tailWord_4422102, baseEnd_4422102] using wordTrace_append hprefix tailTrace_4422102
  have hstable : (prefixWord ++ tailWord_4422102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422102).length < 2 ^ (prefixWord ++ tailWord_4422102).sum := by decide
  have hdescent : baseEnd_4422102 < baseStart_4422102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422130 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4422130 : Nat := 118140960795 + 4422130 * 2 ^ 59
def prefixEnd_4422130 : Nat := 4983230072969 + 3 ^ 40 * 4422130 * 2
def baseEnd_4422130 : Nat := 2270678206666888629738001

theorem tailTrace_4422130 : CollatzResearch.WordTrace tailWord_4422130 prefixEnd_4422130 2270678206666888629738001 := by
  unfold tailWord_4422130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322082867346431130351961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107525554312923816347605229 40322082867346431130351961)
  ·
    refine ⟨30241562150509823347763971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40322082867346431130351961 30241562150509823347763971)
    ·
      refine ⟨45362343225764735021645957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30241562150509823347763971 45362343225764735021645957)
      ·
        refine ⟨8505439354830887816558617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45362343225764735021645957 8505439354830887816558617)
        ·
          refine ⟨6379079516123165862418963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8505439354830887816558617 6379079516123165862418963)
          ·
            refine ⟨9568619274184748793628445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379079516123165862418963 9568619274184748793628445)
            ·
              refine ⟨3588232227819280797610667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9568619274184748793628445 3588232227819280797610667)
              ·
                refine ⟨5382348341728921196416001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588232227819280797610667 5382348341728921196416001)
                ·
                  refine ⟨4036761256296690897312001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5382348341728921196416001 4036761256296690897312001)
                  ·
                    refine ⟨3027570942222518172984001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036761256296690897312001 3027570942222518172984001)
                    ·
                      refine ⟨2270678206666888629738001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027570942222518172984001 2270678206666888629738001)
                      ·
                        rfl

theorem cell23_4422130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4422130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422130 prefixEnd_4422130 := by exact prefixLift 4422130
  have htrace : WordTrace (prefixWord ++ tailWord_4422130) baseStart_4422130 baseEnd_4422130 := by
    simpa [prefixWord, tailWord_4422130, baseEnd_4422130] using wordTrace_append hprefix tailTrace_4422130
  have hstable : (prefixWord ++ tailWord_4422130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422130).length < 2 ^ (prefixWord ++ tailWord_4422130).sum := by decide
  have hdescent : baseEnd_4422130 < baseStart_4422130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422152 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_4422152 : Nat := 118140960795 + 4422152 * 2 ^ 59
def prefixEnd_4422152 : Nat := 4983230072969 + 3 ^ 40 * 4422152 * 2
def baseEnd_4422152 : Nat := 2270689503241287543662899

theorem tailTrace_4422152 : CollatzResearch.WordTrace tailWord_4422152 prefixEnd_4422152 2270689503241287543662899 := by
  unfold tailWord_4422152
  simp only [CollatzResearch.WordTrace]
  refine ⟨80644566937653011139354355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107526089250204014852472473 80644566937653011139354355)
  ·
    refine ⟨120966850406479516709031533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80644566937653011139354355 120966850406479516709031533)
    ·
      refine ⟨45362568902429818765886825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120966850406479516709031533 45362568902429818765886825)
      ·
        refine ⟨34021926676822364074415119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45362568902429818765886825 34021926676822364074415119)
        ·
          refine ⟨51032890015233546111622679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34021926676822364074415119 51032890015233546111622679)
          ·
            refine ⟨76549335022850319167434019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51032890015233546111622679 76549335022850319167434019)
            ·
              refine ⟨114824002534275478751151029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76549335022850319167434019 114824002534275478751151029)
              ·
                refine ⟨10764750237588326132920409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114824002534275478751151029 10764750237588326132920409)
                ·
                  refine ⟨8073562678191244599690307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10764750237588326132920409 8073562678191244599690307)
                  ·
                    refine ⟨12110344017286866899535461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8073562678191244599690307 12110344017286866899535461)
                    ·
                      refine ⟨2270689503241287543662899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12110344017286866899535461 2270689503241287543662899)
                      ·
                        rfl

theorem cell23_4422152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_4422152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422152 prefixEnd_4422152 := by exact prefixLift 4422152
  have htrace : WordTrace (prefixWord ++ tailWord_4422152) baseStart_4422152 baseEnd_4422152 := by
    simpa [prefixWord, tailWord_4422152, baseEnd_4422152] using wordTrace_append hprefix tailTrace_4422152
  have hstable : (prefixWord ++ tailWord_4422152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422152).length < 2 ^ (prefixWord ++ tailWord_4422152).sum := by decide
  have hdescent : baseEnd_4422152 < baseStart_4422152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422179 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 3, 4]
def baseStart_4422179 : Nat := 118140960795 + 4422179 * 2 ^ 59
def prefixEnd_4422179 : Nat := 4983230072969 + 3 ^ 40 * 4422179 * 2
def baseEnd_4422179 : Nat := 756901122406319646008425

theorem tailTrace_4422179 : CollatzResearch.WordTrace tailWord_4422179 prefixEnd_4422179 756901122406319646008425 := by
  unfold tailWord_4422179
  simp only [CollatzResearch.WordTrace]
  refine ⟨161290118646208205889941591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107526745764138803926627727 161290118646208205889941591)
  ·
    refine ⟨241935177969312308834912387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161290118646208205889941591 241935177969312308834912387)
    ·
      refine ⟨362902766953968463252368581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241935177969312308834912387 362902766953968463252368581)
      ·
        refine ⟨68044268803869086859819109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 362902766953968463252368581 68044268803869086859819109)
        ·
          refine ⟨12758300400725453786216083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68044268803869086859819109 12758300400725453786216083)
          ·
            refine ⟨19137450601088180679324125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12758300400725453786216083 19137450601088180679324125)
            ·
              refine ⟨7176543975408067754746547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19137450601088180679324125 7176543975408067754746547)
              ·
                refine ⟨10764815963112101632119821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7176543975408067754746547 10764815963112101632119821)
                ·
                  refine ⟨4036805986167038112044933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10764815963112101632119821 4036805986167038112044933)
                  ·
                    refine ⟨756901122406319646008425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4036805986167038112044933 756901122406319646008425)
                    ·
                      rfl

theorem cell23_4422179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 4].length) (baseStart_4422179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422179 prefixEnd_4422179 := by exact prefixLift 4422179
  have htrace : WordTrace (prefixWord ++ tailWord_4422179) baseStart_4422179 baseEnd_4422179 := by
    simpa [prefixWord, tailWord_4422179, baseEnd_4422179] using wordTrace_append hprefix tailTrace_4422179
  have hstable : (prefixWord ++ tailWord_4422179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422179).length < 2 ^ (prefixWord ++ tailWord_4422179).sum := by decide
  have hdescent : baseEnd_4422179 < baseStart_4422179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422252 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_4422252 : Nat := 118140960795 + 4422252 * 2 ^ 59
def prefixEnd_4422252 : Nat := 4983230072969 + 3 ^ 40 * 4422252 * 2
def baseEnd_4422252 : Nat := 756913617102245717470813

theorem tailTrace_4422252 : CollatzResearch.WordTrace tailWord_4422252 prefixEnd_4422252 756913617102245717470813 := by
  unfold tailWord_4422252
  simp only [CollatzResearch.WordTrace]
  refine ⟨80646390587471869678674505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107528520783295826238232673 80646390587471869678674505)
  ·
    refine ⟨60484792940603902259005879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80646390587471869678674505 60484792940603902259005879)
    ·
      refine ⟨90727189410905853388508819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60484792940603902259005879 90727189410905853388508819)
      ·
        refine ⟨136090784116358780082763229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90727189410905853388508819 136090784116358780082763229)
        ·
          refine ⟨51034044043634542531036211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136090784116358780082763229 51034044043634542531036211)
          ·
            refine ⟨76551066065451813796554317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51034044043634542531036211 76551066065451813796554317)
            ·
              refine ⟨28706649774544430173707869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76551066065451813796554317 28706649774544430173707869)
              ·
                refine ⟨10764993665454161315140451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28706649774544430173707869 10764993665454161315140451)
                ·
                  refine ⟨16147490498181241972710677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10764993665454161315140451 16147490498181241972710677)
                  ·
                    refine ⟨756913617102245717470813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16147490498181241972710677 756913617102245717470813)
                    ·
                      rfl

theorem cell23_4422252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_4422252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422252 prefixEnd_4422252 := by exact prefixLift 4422252
  have htrace : WordTrace (prefixWord ++ tailWord_4422252) baseStart_4422252 baseEnd_4422252 := by
    simpa [prefixWord, tailWord_4422252, baseEnd_4422252] using wordTrace_append hprefix tailTrace_4422252
  have hstable : (prefixWord ++ tailWord_4422252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422252).length < 2 ^ (prefixWord ++ tailWord_4422252).sum := by decide
  have hdescent : baseEnd_4422252 < baseStart_4422252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422276 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_4422276 : Nat := 118140960795 + 4422276 * 2 ^ 59
def prefixEnd_4422276 : Nat := 4983230072969 + 3 ^ 40 * 4422276 * 2
def baseEnd_4422276 : Nat := 2270753174842445058512329

theorem tailTrace_4422276 : CollatzResearch.WordTrace tailWord_4422276 prefixEnd_4422276 2270753174842445058512329 := by
  unfold tailWord_4422276
  simp only [CollatzResearch.WordTrace]
  refine ⟨80646828263428395728111341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107529104351237860970815121 80646828263428395728111341)
  ·
    refine ⟨30242560598785648398041753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80646828263428395728111341 30242560598785648398041753)
    ·
      refine ⟨22681920449089236298531315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30242560598785648398041753 22681920449089236298531315)
      ·
        refine ⟨34022880673633854447796973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22681920449089236298531315 34022880673633854447796973)
        ·
          refine ⟨12758580252612695417923865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34022880673633854447796973 12758580252612695417923865)
          ·
            refine ⟨9568935189459521563442899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12758580252612695417923865 9568935189459521563442899)
            ·
              refine ⟨14353402784189282345164349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9568935189459521563442899 14353402784189282345164349)
              ·
                refine ⟨5382526044070980879436631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14353402784189282345164349 5382526044070980879436631)
                ·
                  refine ⟨8073789066106471319154947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382526044070980879436631 8073789066106471319154947)
                  ·
                    refine ⟨12110683599159706978732421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8073789066106471319154947 12110683599159706978732421)
                    ·
                      refine ⟨2270753174842445058512329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12110683599159706978732421 2270753174842445058512329)
                      ·
                        rfl

theorem cell23_4422276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_4422276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422276 prefixEnd_4422276 := by exact prefixLift 4422276
  have htrace : WordTrace (prefixWord ++ tailWord_4422276) baseStart_4422276 baseEnd_4422276 := by
    simpa [prefixWord, tailWord_4422276, baseEnd_4422276] using wordTrace_append hprefix tailTrace_4422276
  have hstable : (prefixWord ++ tailWord_4422276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422276).length < 2 ^ (prefixWord ++ tailWord_4422276).sum := by decide
  have hdescent : baseEnd_4422276 < baseStart_4422276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422327 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 1, 2, 2]
def baseStart_4422327 : Nat := 118140960795 + 4422327 * 2 ^ 59
def prefixEnd_4422327 : Nat := 4983230072969 + 3 ^ 40 * 4422327 * 2
def baseEnd_4422327 : Nat := 2270779362355824358974595

theorem tailTrace_4422327 : CollatzResearch.WordTrace tailWord_4422327 prefixEnd_4422327 2270779362355824358974595 := by
  unfold tailWord_4422327
  simp only [CollatzResearch.WordTrace]
  refine ⟨161295516649672027166329235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107530344433114684777552823 161295516649672027166329235)
  ·
    refine ⟨241943274974508040749493853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161295516649672027166329235 241943274974508040749493853)
    ·
      refine ⟨90728728115440515281060195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241943274974508040749493853 90728728115440515281060195)
      ·
        refine ⟨136093092173160772921590293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90728728115440515281060195 136093092173160772921590293)
        ·
          refine ⟨6379363695616911230699545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136093092173160772921590293 6379363695616911230699545)
          ·
            refine ⟨4784522771712683423024659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6379363695616911230699545 4784522771712683423024659)
            ·
              refine ⟨7176784157569025134536989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4784522771712683423024659 7176784157569025134536989)
              ·
                refine ⟨2691294059088384425451371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7176784157569025134536989 2691294059088384425451371)
                ·
                  refine ⟨4036941088632576638177057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691294059088384425451371 4036941088632576638177057)
                  ·
                    refine ⟨3027705816474432478632793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036941088632576638177057 3027705816474432478632793)
                    ·
                      refine ⟨2270779362355824358974595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027705816474432478632793 2270779362355824358974595)
                      ·
                        rfl

theorem cell23_4422327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_4422327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422327 prefixEnd_4422327 := by exact prefixLift 4422327
  have htrace : WordTrace (prefixWord ++ tailWord_4422327) baseStart_4422327 baseEnd_4422327 := by
    simpa [prefixWord, tailWord_4422327, baseEnd_4422327] using wordTrace_append hprefix tailTrace_4422327
  have hstable : (prefixWord ++ tailWord_4422327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422327).length < 2 ^ (prefixWord ++ tailWord_4422327).sum := by decide
  have hdescent : baseEnd_4422327 < baseStart_4422327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422360 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_4422360 : Nat := 118140960795 + 4422360 * 2 ^ 59
def prefixEnd_4422360 : Nat := 4983230072969 + 3 ^ 40 * 4422360 * 2
def baseEnd_4422360 : Nat := 2270796307217422729861943

theorem tailTrace_4422360 : CollatzResearch.WordTrace tailWord_4422360 prefixEnd_4422360 2270796307217422729861943 := by
  unfold tailWord_4422360
  simp only [CollatzResearch.WordTrace]
  refine ⟨80648360129276236901140267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107531146839034982534853689 80648360129276236901140267)
  ·
    refine ⟨120972540193914355351710401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80648360129276236901140267 120972540193914355351710401)
    ·
      refine ⟨90729405145435766513782801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120972540193914355351710401 90729405145435766513782801)
      ·
        refine ⟨68047053859076824885337101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90729405145435766513782801 68047053859076824885337101)
        ·
          refine ⟨25517645197153809332001413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68047053859076824885337101 25517645197153809332001413)
          ·
            refine ⟨4784558474466339249750265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25517645197153809332001413 4784558474466339249750265)
            ·
              refine ⟨3588418855849754437312699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4784558474466339249750265 3588418855849754437312699)
              ·
                refine ⟨5382628283774631655969049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588418855849754437312699 5382628283774631655969049)
                ·
                  refine ⟨4036971212830973741976787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5382628283774631655969049 4036971212830973741976787)
                  ·
                    refine ⟨6055456819246460612965181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036971212830973741976787 6055456819246460612965181)
                    ·
                      refine ⟨2270796307217422729861943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055456819246460612965181 2270796307217422729861943)
                      ·
                        rfl

theorem cell23_4422360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_4422360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422360 prefixEnd_4422360 := by exact prefixLift 4422360
  have htrace : WordTrace (prefixWord ++ tailWord_4422360) baseStart_4422360 baseEnd_4422360 := by
    simpa [prefixWord, tailWord_4422360, baseEnd_4422360] using wordTrace_append hprefix tailTrace_4422360
  have hstable : (prefixWord ++ tailWord_4422360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422360).length < 2 ^ (prefixWord ++ tailWord_4422360).sum := by decide
  have hdescent : baseEnd_4422360 < baseStart_4422360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422369 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_4422369 : Nat := 118140960795 + 4422369 * 2 ^ 59
def prefixEnd_4422369 : Nat := 4983230072969 + 3 ^ 40 * 4422369 * 2
def baseEnd_4422369 : Nat := 2270800928543313194649401

theorem tailTrace_4422369 : CollatzResearch.WordTrace tailWord_4422369 prefixEnd_4422369 2270800928543313194649401 := by
  unfold tailWord_4422369
  simp only [CollatzResearch.WordTrace]
  refine ⟨161297048515519868339358161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107531365677013245559572107 161297048515519868339358161)
  ·
    refine ⟨120972786386639901254518621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161297048515519868339358161 120972786386639901254518621)
    ·
      refine ⟨45364794894989962970444483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120972786386639901254518621 45364794894989962970444483)
      ·
        refine ⟨68047192342484944455666725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45364794894989962970444483 68047192342484944455666725)
        ·
          refine ⟨12758848564215927085437511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68047192342484944455666725 12758848564215927085437511)
          ·
            refine ⟨19138272846323890628156267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12758848564215927085437511 19138272846323890628156267)
            ·
              refine ⟨28707409269485835942234401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19138272846323890628156267 28707409269485835942234401)
              ·
                refine ⟨21530556952114376956675801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28707409269485835942234401 21530556952114376956675801)
                ·
                  refine ⟨16147917714085782717506851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21530556952114376956675801 16147917714085782717506851)
                  ·
                    refine ⟨24221876571128674076260277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16147917714085782717506851 24221876571128674076260277)
                    ·
                      refine ⟨2270800928543313194649401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24221876571128674076260277 2270800928543313194649401)
                      ·
                        rfl

theorem cell23_4422369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_4422369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422369 prefixEnd_4422369 := by exact prefixLift 4422369
  have htrace : WordTrace (prefixWord ++ tailWord_4422369) baseStart_4422369 baseEnd_4422369 := by
    simpa [prefixWord, tailWord_4422369, baseEnd_4422369] using wordTrace_append hprefix tailTrace_4422369
  have hstable : (prefixWord ++ tailWord_4422369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422369).length < 2 ^ (prefixWord ++ tailWord_4422369).sum := by decide
  have hdescent : baseEnd_4422369 < baseStart_4422369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422399 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_4422399 : Nat := 118140960795 + 4422399 * 2 ^ 59
def prefixEnd_4422399 : Nat := 4983230072969 + 3 ^ 40 * 4422399 * 2
def baseEnd_4422399 : Nat := 2270816332962948077274263

theorem tailTrace_4422399 : CollatzResearch.WordTrace tailWord_4422399 prefixEnd_4422399 2270816332962948077274263 := by
  unfold tailWord_4422399
  simp only [CollatzResearch.WordTrace]
  refine ⟨161298142705411183462950251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107532095136940788975300167 161298142705411183462950251)
  ·
    refine ⟨241947214058116775194425377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161298142705411183462950251 241947214058116775194425377)
    ·
      refine ⟨181460410543587581395819033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241947214058116775194425377 181460410543587581395819033)
      ·
        refine ⟨136095307907690686046864275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181460410543587581395819033 136095307907690686046864275)
        ·
          refine ⟨204142961861536029070296413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136095307907690686046864275 204142961861536029070296413)
          ·
            refine ⟨76553610698076010901361155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204142961861536029070296413 76553610698076010901361155)
            ·
              refine ⟨114830416047114016352041733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76553610698076010901361155 114830416047114016352041733)
              ·
                refine ⟨21530703008833878066007825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114830416047114016352041733 21530703008833878066007825)
                ·
                  refine ⟨16148027256625408549505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21530703008833878066007825 16148027256625408549505869)
                  ·
                    refine ⟨6055510221234528206064701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16148027256625408549505869 6055510221234528206064701)
                    ·
                      refine ⟨2270816332962948077274263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055510221234528206064701 2270816332962948077274263)
                      ·
                        rfl

theorem cell23_4422399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_4422399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422399 prefixEnd_4422399 := by exact prefixLift 4422399
  have htrace : WordTrace (prefixWord ++ tailWord_4422399) baseStart_4422399 baseEnd_4422399 := by
    simpa [prefixWord, tailWord_4422399, baseEnd_4422399] using wordTrace_append hprefix tailTrace_4422399
  have hstable : (prefixWord ++ tailWord_4422399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422399).length < 2 ^ (prefixWord ++ tailWord_4422399).sum := by decide
  have hdescent : baseEnd_4422399 < baseStart_4422399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422426 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_4422426 : Nat := 118140960795 + 4422426 * 2 ^ 59
def prefixEnd_4422426 : Nat := 4983230072969 + 3 ^ 40 * 4422426 * 2
def baseEnd_4422426 : Nat := 2270830196940619471636639

theorem tailTrace_4422426 : CollatzResearch.WordTrace tailWord_4422426 prefixEnd_4422426 2270830196940619471636639 := by
  unfold tailWord_4422426
  simp only [CollatzResearch.WordTrace]
  refine ⟨40324781869078341768545783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107532751650875578049455421 40324781869078341768545783)
  ·
    refine ⟨60487172803617512652818675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40324781869078341768545783 60487172803617512652818675)
    ·
      refine ⟨90730759205426268979228013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60487172803617512652818675 90730759205426268979228013)
      ·
        refine ⟨34024034702034850867210505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90730759205426268979228013 34024034702034850867210505)
        ·
          refine ⟨25518026026526138150407879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34024034702034850867210505 25518026026526138150407879)
          ·
            refine ⟨38277039039789207225611819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25518026026526138150407879 38277039039789207225611819)
            ·
              refine ⟨57415558559683810838417729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38277039039789207225611819 57415558559683810838417729)
              ·
                refine ⟨43061668919762858128813297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57415558559683810838417729 43061668919762858128813297)
                ·
                  refine ⟨32296251689822143596609973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43061668919762858128813297 32296251689822143596609973)
                  ·
                    refine ⟨3027773595920825962182185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32296251689822143596609973 3027773595920825962182185)
                    ·
                      refine ⟨2270830196940619471636639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027773595920825962182185 2270830196940619471636639)
                      ·
                        rfl

theorem cell23_4422426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_4422426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422426 prefixEnd_4422426 := by exact prefixLift 4422426
  have htrace : WordTrace (prefixWord ++ tailWord_4422426) baseStart_4422426 baseEnd_4422426 := by
    simpa [prefixWord, tailWord_4422426, baseEnd_4422426] using wordTrace_append hprefix tailTrace_4422426
  have hstable : (prefixWord ++ tailWord_4422426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422426).length < 2 ^ (prefixWord ++ tailWord_4422426).sum := by decide
  have hdescent : baseEnd_4422426 < baseStart_4422426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422436 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_4422436 : Nat := 118140960795 + 4422436 * 2 ^ 59
def prefixEnd_4422436 : Nat := 4983230072969 + 3 ^ 40 * 4422436 * 2
def baseEnd_4422436 : Nat := 756945110582388144170531

theorem tailTrace_4422436 : CollatzResearch.WordTrace tailWord_4422436 prefixEnd_4422436 756945110582388144170531 := by
  unfold tailWord_4422436
  simp only [CollatzResearch.WordTrace]
  refine ⟨80649746103138569391023581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107532994804184759188031441 80649746103138569391023581)
  ·
    refine ⟨30243654788676963521633843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80649746103138569391023581 30243654788676963521633843)
    ·
      refine ⟨45365482183015445282450765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30243654788676963521633843 45365482183015445282450765)
      ·
        refine ⟨17012055818630791980919037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45365482183015445282450765 17012055818630791980919037)
        ·
          refine ⟨6379520931986546992844639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17012055818630791980919037 6379520931986546992844639)
          ·
            refine ⟨9569281397979820489266959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379520931986546992844639 9569281397979820489266959)
            ·
              refine ⟨14353922096969730733900439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569281397979820489266959 14353922096969730733900439)
              ·
                refine ⟨21530883145454596100850659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14353922096969730733900439 21530883145454596100850659)
                ·
                  refine ⟨32296324718181894151275989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21530883145454596100850659 32296324718181894151275989)
                  ·
                    refine ⟨756945110582388144170531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32296324718181894151275989 756945110582388144170531)
                    ·
                      rfl

theorem cell23_4422436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_4422436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422436 prefixEnd_4422436 := by exact prefixLift 4422436
  have htrace : WordTrace (prefixWord ++ tailWord_4422436) baseStart_4422436 baseEnd_4422436 := by
    simpa [prefixWord, tailWord_4422436, baseEnd_4422436] using wordTrace_append hprefix tailTrace_4422436
  have hstable : (prefixWord ++ tailWord_4422436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422436).length < 2 ^ (prefixWord ++ tailWord_4422436).sum := by decide
  have hdescent : baseEnd_4422436 < baseStart_4422436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422456 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_4422456 : Nat := 118140960795 + 4422456 * 2 ^ 59
def prefixEnd_4422456 : Nat := 4983230072969 + 3 ^ 40 * 4422456 * 2
def baseEnd_4422456 : Nat := 2270845601360254354261501

theorem tailTrace_4422456 : CollatzResearch.WordTrace tailWord_4422456 prefixEnd_4422456 2270845601360254354261501 := by
  unfold tailWord_4422456
  simp only [CollatzResearch.WordTrace]
  refine ⟨80650110833102341098887611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107533481110803121465183481 80650110833102341098887611)
  ·
    refine ⟨120975166249653511648331417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80650110833102341098887611 120975166249653511648331417)
    ·
      refine ⟨90731374687240133736248563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120975166249653511648331417 90731374687240133736248563)
      ·
        refine ⟨136097062030860200604372845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90731374687240133736248563 136097062030860200604372845)
        ·
          refine ⟨51036398261572575226639817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136097062030860200604372845 51036398261572575226639817)
          ·
            refine ⟨38277298696179431419979863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51036398261572575226639817 38277298696179431419979863)
            ·
              refine ⟨57415948044269147129969795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38277298696179431419979863 57415948044269147129969795)
              ·
                refine ⟨86123922066403720694954693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57415948044269147129969795 86123922066403720694954693)
                ·
                  refine ⟨16148235387450697630304005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86123922066403720694954693 16148235387450697630304005)
                  ·
                    refine ⟨3027794135147005805682001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16148235387450697630304005 3027794135147005805682001)
                    ·
                      refine ⟨2270845601360254354261501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027794135147005805682001 2270845601360254354261501)
                      ·
                        rfl

theorem cell23_4422456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_4422456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422456 prefixEnd_4422456 := by exact prefixLift 4422456
  have htrace : WordTrace (prefixWord ++ tailWord_4422456) baseStart_4422456 baseEnd_4422456 := by
    simpa [prefixWord, tailWord_4422456, baseEnd_4422456] using wordTrace_append hprefix tailTrace_4422456
  have hstable : (prefixWord ++ tailWord_4422456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422456).length < 2 ^ (prefixWord ++ tailWord_4422456).sum := by decide
  have hdescent : baseEnd_4422456 < baseStart_4422456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422476 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4422476 : Nat := 118140960795 + 4422476 * 2 ^ 59
def prefixEnd_4422476 : Nat := 4983230072969 + 3 ^ 40 * 4422476 * 2
def baseEnd_4422476 : Nat := 2270855870973344276011409

theorem tailTrace_4422476 : CollatzResearch.WordTrace tailWord_4422476 prefixEnd_4422476 2270855870973344276011409 := by
  unfold tailWord_4422476
  simp only [CollatzResearch.WordTrace]
  refine ⟨80650475563066112806751641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107533967417421483742335521 80650475563066112806751641)
  ·
    refine ⟨60487856672299584605063731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80650475563066112806751641 60487856672299584605063731)
    ·
      refine ⟨90731785008449376907595597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60487856672299584605063731 90731785008449376907595597)
      ·
        refine ⟨34024419378168516340348349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90731785008449376907595597 34024419378168516340348349)
        ·
          refine ⟨12759157266813193627630631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34024419378168516340348349 12759157266813193627630631)
          ·
            refine ⟨19138735900219790441445947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759157266813193627630631 19138735900219790441445947)
            ·
              refine ⟨28708103850329685662168921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19138735900219790441445947 28708103850329685662168921)
              ·
                refine ⟨21531077887747264246626691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28708103850329685662168921 21531077887747264246626691)
                ·
                  refine ⟨32296616831620896369940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21531077887747264246626691 32296616831620896369940037)
                  ·
                    refine ⟨6055615655928918069363757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32296616831620896369940037 6055615655928918069363757)
                    ·
                      refine ⟨2270855870973344276011409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055615655928918069363757 2270855870973344276011409)
                      ·
                        rfl

theorem cell23_4422476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4422476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422476 prefixEnd_4422476 := by exact prefixLift 4422476
  have htrace : WordTrace (prefixWord ++ tailWord_4422476) baseStart_4422476 baseEnd_4422476 := by
    simpa [prefixWord, tailWord_4422476, baseEnd_4422476] using wordTrace_append hprefix tailTrace_4422476
  have hstable : (prefixWord ++ tailWord_4422476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422476).length < 2 ^ (prefixWord ++ tailWord_4422476).sum := by decide
  have hdescent : baseEnd_4422476 < baseStart_4422476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422500 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_4422500 : Nat := 118140960795 + 4422500 * 2 ^ 59
def prefixEnd_4422500 : Nat := 4983230072969 + 3 ^ 40 * 4422500 * 2
def baseEnd_4422500 : Nat := 756956064836350727370433

theorem tailTrace_4422500 : CollatzResearch.WordTrace tailWord_4422500 prefixEnd_4422500 756956064836350727370433 := by
  unfold tailWord_4422500
  simp only [CollatzResearch.WordTrace]
  refine ⟨80650913239022638856188477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107534550985363518474917969 80650913239022638856188477)
  ·
    refine ⟨30244092464633489571070679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80650913239022638856188477 30244092464633489571070679)
    ·
      refine ⟨45366138696950234356606019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30244092464633489571070679 45366138696950234356606019)
      ·
        refine ⟨68049208045425351534909029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45366138696950234356606019 68049208045425351534909029)
        ·
          refine ⟨12759226508517253412795443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68049208045425351534909029 12759226508517253412795443)
          ·
            refine ⟨19138839762775880119193165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759226508517253412795443 19138839762775880119193165)
            ·
              refine ⟨7177064911040955044697437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19138839762775880119193165 7177064911040955044697437)
              ·
                refine ⟨2691399341640358141761539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177064911040955044697437 2691399341640358141761539)
                ·
                  refine ⟨4037099012460537212642309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691399341640358141761539 4037099012460537212642309)
                  ·
                    refine ⟨756956064836350727370433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037099012460537212642309 756956064836350727370433)
                    ·
                      rfl

theorem cell23_4422500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_4422500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422500 prefixEnd_4422500 := by exact prefixLift 4422500
  have htrace : WordTrace (prefixWord ++ tailWord_4422500) baseStart_4422500 baseEnd_4422500 := by
    simpa [prefixWord, tailWord_4422500, baseEnd_4422500] using wordTrace_append hprefix tailTrace_4422500
  have hstable : (prefixWord ++ tailWord_4422500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422500).length < 2 ^ (prefixWord ++ tailWord_4422500).sum := by decide
  have hdescent : baseEnd_4422500 < baseStart_4422500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422510 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4422510 : Nat := 118140960795 + 4422510 * 2 ^ 59
def prefixEnd_4422510 : Nat := 4983230072969 + 3 ^ 40 * 4422510 * 2
def baseEnd_4422510 : Nat := 2270873329315597142986253

theorem tailTrace_4422510 : CollatzResearch.WordTrace tailWord_4422510 prefixEnd_4422510 2270873329315597142986253 := by
  unfold tailWord_4422510
  simp only [CollatzResearch.WordTrace]
  refine ⟨20162773901001131177530123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107534794138672699613493989 20162773901001131177530123)
  ·
    refine ⟨30244160851501696766295185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20162773901001131177530123 30244160851501696766295185)
    ·
      refine ⟨22683120638626272574721389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30244160851501696766295185 22683120638626272574721389)
      ·
        refine ⟨8506170239484852215520521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22683120638626272574721389 8506170239484852215520521)
        ·
          refine ⟨6379627679613639161640391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8506170239484852215520521 6379627679613639161640391)
          ·
            refine ⟨9569441519420458742460587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379627679613639161640391 9569441519420458742460587)
            ·
              refine ⟨14354162279130688113690881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569441519420458742460587 14354162279130688113690881)
              ·
                refine ⟨10765621709348016085268161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14354162279130688113690881 10765621709348016085268161)
                ·
                  refine ⟨8074216282011012063951121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10765621709348016085268161 8074216282011012063951121)
                  ·
                    refine ⟨6055662211508259047963341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8074216282011012063951121 6055662211508259047963341)
                    ·
                      refine ⟨2270873329315597142986253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055662211508259047963341 2270873329315597142986253)
                      ·
                        rfl

theorem cell23_4422510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4422510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422510 prefixEnd_4422510 := by exact prefixLift 4422510
  have htrace : WordTrace (prefixWord ++ tailWord_4422510) baseStart_4422510 baseEnd_4422510 := by
    simpa [prefixWord, tailWord_4422510, baseEnd_4422510] using wordTrace_append hprefix tailTrace_4422510
  have hstable : (prefixWord ++ tailWord_4422510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422510).length < 2 ^ (prefixWord ++ tailWord_4422510).sum := by decide
  have hdescent : baseEnd_4422510 < baseStart_4422510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422517 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4422517 : Nat := 118140960795 + 4422517 * 2 ^ 59
def prefixEnd_4422517 : Nat := 4983230072969 + 3 ^ 40 * 4422517 * 2
def baseEnd_4422517 : Nat := 756958974560059538532907

theorem tailTrace_4422517 : CollatzResearch.WordTrace tailWord_4422517 prefixEnd_4422517 756958974560059538532907 := by
  unfold tailWord_4422517
  simp only [CollatzResearch.WordTrace]
  refine ⟨161302446518983689615745805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107534964345989126410497203 161302446518983689615745805)
  ·
    refine ⟨60488417444618883605904677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161302446518983689615745805 60488417444618883605904677)
    ·
      refine ⟨11341578270866040676107127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60488417444618883605904677 11341578270866040676107127)
      ·
        refine ⟨17012367406299061014160691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11341578270866040676107127 17012367406299061014160691)
        ·
          refine ⟨25518551109448591521241037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17012367406299061014160691 25518551109448591521241037)
          ·
            refine ⟨9569456666043221820465389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25518551109448591521241037 9569456666043221820465389)
            ·
              refine ⟨3588546249766208182674521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9569456666043221820465389 3588546249766208182674521)
              ·
                refine ⟨2691409687324656137005891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588546249766208182674521 2691409687324656137005891)
                ·
                  refine ⟨4037114530986984205508837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691409687324656137005891 4037114530986984205508837)
                  ·
                    refine ⟨756958974560059538532907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037114530986984205508837 756958974560059538532907)
                    ·
                      rfl

theorem cell23_4422517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4422517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422517 prefixEnd_4422517 := by exact prefixLift 4422517
  have htrace : WordTrace (prefixWord ++ tailWord_4422517) baseStart_4422517 baseEnd_4422517 := by
    simpa [prefixWord, tailWord_4422517, baseEnd_4422517] using wordTrace_append hprefix tailTrace_4422517
  have hstable : (prefixWord ++ tailWord_4422517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422517).length < 2 ^ (prefixWord ++ tailWord_4422517).sum := by decide
  have hdescent : baseEnd_4422517 < baseStart_4422517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422523 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 3]
def baseStart_4422523 : Nat := 118140960795 + 4422523 * 2 ^ 59
def prefixEnd_4422523 : Nat := 4983230072969 + 3 ^ 40 * 4422523 * 2
def baseEnd_4422523 : Nat := 2270880004564105592123693

theorem tailTrace_4422523 : CollatzResearch.WordTrace tailWord_4422523 prefixEnd_4422523 2270880004564105592123693 := by
  unfold tailWord_4422523
  simp only [CollatzResearch.WordTrace]
  refine ⟨161302665356961952640464223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107535110237974635093642815 161302665356961952640464223)
  ·
    refine ⟨241953998035442928960696335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161302665356961952640464223 241953998035442928960696335)
    ·
      refine ⟨362930997053164393441044503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241953998035442928960696335 362930997053164393441044503)
      ·
        refine ⟨544396495579746590161566755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362930997053164393441044503 544396495579746590161566755)
        ·
          refine ⟨816594743369619885242350133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544396495579746590161566755 816594743369619885242350133)
          ·
            refine ⟨76555757190901864241470325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 816594743369619885242350133 76555757190901864241470325)
            ·
              refine ⟨7177102236647049772637843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76555757190901864241470325 7177102236647049772637843)
              ·
                refine ⟨10765653354970574658956765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7177102236647049772637843 10765653354970574658956765)
                ·
                  refine ⟨4037120008113965497108787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10765653354970574658956765 4037120008113965497108787)
                  ·
                    refine ⟨6055680012170948245663181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4037120008113965497108787 6055680012170948245663181)
                    ·
                      refine ⟨2270880004564105592123693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055680012170948245663181 2270880004564105592123693)
                      ·
                        rfl

theorem cell23_4422523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 3].length) (baseStart_4422523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422523 prefixEnd_4422523 := by exact prefixLift 4422523
  have htrace : WordTrace (prefixWord ++ tailWord_4422523) baseStart_4422523 baseEnd_4422523 := by
    simpa [prefixWord, tailWord_4422523, baseEnd_4422523] using wordTrace_append hprefix tailTrace_4422523
  have hstable : (prefixWord ++ tailWord_4422523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422523).length < 2 ^ (prefixWord ++ tailWord_4422523).sum := by decide
  have hdescent : baseEnd_4422523 < baseStart_4422523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_4422579 : Nat := 118140960795 + 4422579 * 2 ^ 59
def prefixEnd_4422579 : Nat := 4983230072969 + 3 ^ 40 * 4422579 * 2
def baseEnd_4422579 : Nat := 2270908759480757373023435

theorem tailTrace_4422579 : CollatzResearch.WordTrace tailWord_4422579 prefixEnd_4422579 2270908759480757373023435 := by
  unfold tailWord_4422579
  simp only [CollatzResearch.WordTrace]
  refine ⟨161304707844759074204502791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107536471896506049469668527 161304707844759074204502791)
  ·
    refine ⟨241957061767138611306754187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161304707844759074204502791 241957061767138611306754187)
    ·
      refine ⟨362935592650707916960131281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241957061767138611306754187 362935592650707916960131281)
      ·
        refine ⟨272201694488030937720098461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362935592650707916960131281 272201694488030937720098461)
        ·
          refine ⟨102075635433011601645036923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272201694488030937720098461 102075635433011601645036923)
          ·
            refine ⟨153113453149517402467555385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102075635433011601645036923 153113453149517402467555385)
            ·
              refine ⟨114835089862138051850666539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153113453149517402467555385 114835089862138051850666539)
              ·
                refine ⟨172252634793207077775999809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114835089862138051850666539 172252634793207077775999809)
                ·
                  refine ⟨129189476094905308331999857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172252634793207077775999809 129189476094905308331999857)
                  ·
                    refine ⟨96892107071178981248999893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129189476094905308331999857 96892107071178981248999893)
                    ·
                      refine ⟨2270908759480757373023435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96892107071178981248999893 2270908759480757373023435)
                      ·
                        rfl

theorem cell23_4422579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_4422579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422579 prefixEnd_4422579 := by exact prefixLift 4422579
  have htrace : WordTrace (prefixWord ++ tailWord_4422579) baseStart_4422579 baseEnd_4422579 := by
    simpa [prefixWord, tailWord_4422579, baseEnd_4422579] using wordTrace_append hprefix tailTrace_4422579
  have hstable : (prefixWord ++ tailWord_4422579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422579).length < 2 ^ (prefixWord ++ tailWord_4422579).sum := by decide
  have hdescent : baseEnd_4422579 < baseStart_4422579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422580 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4422580 : Nat := 118140960795 + 4422580 * 2 ^ 59
def prefixEnd_4422580 : Nat := 4983230072969 + 3 ^ 40 * 4422580 * 2
def baseEnd_4422580 : Nat := 2270909272961411869110931

theorem tailTrace_4422580 : CollatzResearch.WordTrace tailWord_4422580 prefixEnd_4422580 2270909272961411869110931 := by
  unfold tailWord_4422580
  simp only [CollatzResearch.WordTrace]
  refine ⟨80652372158877725687644597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107536496211836967583526129 80652372158877725687644597)
  ·
    refine ⟨7561159889894786783216681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80652372158877725687644597 7561159889894786783216681)
    ·
      refine ⟨5670869917421090087412511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7561159889894786783216681 5670869917421090087412511)
      ·
        refine ⟨8506304876131635131118767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670869917421090087412511 8506304876131635131118767)
        ·
          refine ⟨12759457314197452696678151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506304876131635131118767 12759457314197452696678151)
          ·
            refine ⟨19139185971296179045017227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759457314197452696678151 19139185971296179045017227)
            ·
              refine ⟨28708778956944268567525841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19139185971296179045017227 28708778956944268567525841)
              ·
                refine ⟨21531584217708201425644381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28708778956944268567525841 21531584217708201425644381)
                ·
                  refine ⟨8074344081640575534616643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21531584217708201425644381 8074344081640575534616643)
                  ·
                    refine ⟨12111516122460863301924965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8074344081640575534616643 12111516122460863301924965)
                    ·
                      refine ⟨2270909272961411869110931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12111516122460863301924965 2270909272961411869110931)
                      ·
                        rfl

theorem cell23_4422580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4422580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422580 prefixEnd_4422580 := by exact prefixLift 4422580
  have htrace : WordTrace (prefixWord ++ tailWord_4422580) baseStart_4422580 baseEnd_4422580 := by
    simpa [prefixWord, tailWord_4422580, baseEnd_4422580] using wordTrace_append hprefix tailTrace_4422580
  have hstable : (prefixWord ++ tailWord_4422580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422580).length < 2 ^ (prefixWord ++ tailWord_4422580).sum := by decide
  have hdescent : baseEnd_4422580 < baseStart_4422580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422614 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4422614 : Nat := 118140960795 + 4422614 * 2 ^ 59
def prefixEnd_4422614 : Nat := 4983230072969 + 3 ^ 40 * 4422614 * 2
def baseEnd_4422614 : Nat := 2270926731303664736085775

theorem tailTrace_4422614 : CollatzResearch.WordTrace tailWord_4422614 prefixEnd_4422614 2270926731303664736085775 := by
  unfold tailWord_4422614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081624024977017198876681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107537322933088183454684597 10081624024977017198876681)
  ·
    refine ⟨7561218018732762899157511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10081624024977017198876681 7561218018732762899157511)
    ·
      refine ⟨11341827028099144348736267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7561218018732762899157511 11341827028099144348736267)
      ·
        refine ⟨17012740542148716523104401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11341827028099144348736267 17012740542148716523104401)
        ·
          refine ⟨12759555406611537392328301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17012740542148716523104401 12759555406611537392328301)
          ·
            refine ⟨4784833277479326522123113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12759555406611537392328301 4784833277479326522123113)
            ·
              refine ⟨3588624958109494891592335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4784833277479326522123113 3588624958109494891592335)
              ·
                refine ⟨5382937437164242337388503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588624958109494891592335 5382937437164242337388503)
                ·
                  refine ⟨8074406155746363506082755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382937437164242337388503 8074406155746363506082755)
                  ·
                    refine ⟨12111609233619545259124133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8074406155746363506082755 12111609233619545259124133)
                    ·
                      refine ⟨2270926731303664736085775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12111609233619545259124133 2270926731303664736085775)
                      ·
                        rfl

theorem cell23_4422614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4422614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422614 prefixEnd_4422614 := by exact prefixLift 4422614
  have htrace : WordTrace (prefixWord ++ tailWord_4422614) baseStart_4422614 baseEnd_4422614 := by
    simpa [prefixWord, tailWord_4422614, baseEnd_4422614] using wordTrace_append hprefix tailTrace_4422614
  have hstable : (prefixWord ++ tailWord_4422614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422614).length < 2 ^ (prefixWord ++ tailWord_4422614).sum := by decide
  have hdescent : baseEnd_4422614 < baseStart_4422614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422617 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 1, 2, 3]
def baseStart_4422617 : Nat := 118140960795 + 4422617 * 2 ^ 59
def prefixEnd_4422617 : Nat := 4983230072969 + 3 ^ 40 * 4422617 * 2
def baseEnd_4422617 : Nat := 2270928271745628224348261

theorem tailTrace_4422617 : CollatzResearch.WordTrace tailWord_4422617 prefixEnd_4422617 2270928271745628224348261 := by
  unfold tailWord_4422617
  simp only [CollatzResearch.WordTrace]
  refine ⟨161306093818621406694386105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107537395879080937796257403 161306093818621406694386105)
  ·
    refine ⟨120979570363966055020789579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161306093818621406694386105 120979570363966055020789579)
    ·
      refine ⟨181469355545949082531184369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120979570363966055020789579 181469355545949082531184369)
      ·
        refine ⟨136102016659461811898388277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181469355545949082531184369 136102016659461811898388277)
        ·
          refine ⟨12759564061824544865473901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136102016659461811898388277 12759564061824544865473901)
          ·
            refine ⟨4784836523184204324552713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12759564061824544865473901 4784836523184204324552713)
            ·
              refine ⟨3588627392388153243414535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4784836523184204324552713 3588627392388153243414535)
              ·
                refine ⟨5382941088582229865121803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588627392388153243414535 5382941088582229865121803)
                ·
                  refine ⟨8074411632873344797682705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382941088582229865121803 8074411632873344797682705)
                  ·
                    refine ⟨6055808724655008598262029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8074411632873344797682705 6055808724655008598262029)
                    ·
                      refine ⟨2270928271745628224348261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055808724655008598262029 2270928271745628224348261)
                      ·
                        rfl

theorem cell23_4422617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_4422617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422617 prefixEnd_4422617 := by exact prefixLift 4422617
  have htrace : WordTrace (prefixWord ++ tailWord_4422617) baseStart_4422617 baseEnd_4422617 := by
    simpa [prefixWord, tailWord_4422617, baseEnd_4422617] using wordTrace_append hprefix tailTrace_4422617
  have hstable : (prefixWord ++ tailWord_4422617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422617).length < 2 ^ (prefixWord ++ tailWord_4422617).sum := by decide
  have hdescent : baseEnd_4422617 < baseStart_4422617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422644 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4422644 : Nat := 118140960795 + 4422644 * 2 ^ 59
def prefixEnd_4422644 : Nat := 4983230072969 + 3 ^ 40 * 4422644 * 2
def baseEnd_4422644 : Nat := 2270942135723299618710637

theorem tailTrace_4422644 : CollatzResearch.WordTrace tailWord_4422644 prefixEnd_4422644 2270942135723299618710637 := by
  unfold tailWord_4422644
  simp only [CollatzResearch.WordTrace]
  refine ⟨80653539294761795152809493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107538052393015726870412657 80653539294761795152809493)
  ·
    refine ⟨3780634654441959147787945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80653539294761795152809493 3780634654441959147787945)
    ·
      refine ⟨2835475990831469360840959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3780634654441959147787945 2835475990831469360840959)
      ·
        refine ⟨4253213986247204041261439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835475990831469360840959 4253213986247204041261439)
        ·
          refine ⟨6379820979370806061892159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4253213986247204041261439 6379820979370806061892159)
          ·
            refine ⟨9569731469056209092838239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379820979370806061892159 9569731469056209092838239)
            ·
              refine ⟨14354597203584313639257359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569731469056209092838239 14354597203584313639257359)
              ·
                refine ⟨21531895805376470458886039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14354597203584313639257359 21531895805376470458886039)
                ·
                  refine ⟨32297843708064705688329059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21531895805376470458886039 32297843708064705688329059)
                  ·
                    refine ⟨48446765562097058532493589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32297843708064705688329059 48446765562097058532493589)
                    ·
                      refine ⟨2270942135723299618710637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48446765562097058532493589 2270942135723299618710637)
                      ·
                        rfl

theorem cell23_4422644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4422644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422644 prefixEnd_4422644 := by exact prefixLift 4422644
  have htrace : WordTrace (prefixWord ++ tailWord_4422644) baseStart_4422644 baseEnd_4422644 := by
    simpa [prefixWord, tailWord_4422644, baseEnd_4422644] using wordTrace_append hprefix tailTrace_4422644
  have hstable : (prefixWord ++ tailWord_4422644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422644).length < 2 ^ (prefixWord ++ tailWord_4422644).sum := by decide
  have hdescent : baseEnd_4422644 < baseStart_4422644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422656 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_4422656 : Nat := 118140960795 + 4422656 * 2 ^ 59
def prefixEnd_4422656 : Nat := 4983230072969 + 3 ^ 40 * 4422656 * 2
def baseEnd_4422656 : Nat := 2270948297491153571760581

theorem tailTrace_4422656 : CollatzResearch.WordTrace tailWord_4422656 prefixEnd_4422656 2270948297491153571760581 := by
  unfold tailWord_4422656
  simp only [CollatzResearch.WordTrace]
  refine ⟨80653758132740058177527911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107538344176986744236703881 80653758132740058177527911)
  ·
    refine ⟨120980637199110087266291867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80653758132740058177527911 120980637199110087266291867)
    ·
      refine ⟨181470955798665130899437801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120980637199110087266291867 181470955798665130899437801)
      ·
        refine ⟨136103216848998848174578351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181470955798665130899437801 136103216848998848174578351)
        ·
          refine ⟨204154825273498272261867527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136103216848998848174578351 204154825273498272261867527)
          ·
            refine ⟨306232237910247408392801291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204154825273498272261867527 306232237910247408392801291)
            ·
              refine ⟨459348356865371112589201937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306232237910247408392801291 459348356865371112589201937)
              ·
                refine ⟨344511267649028334441901453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459348356865371112589201937 344511267649028334441901453)
                ·
                  refine ⟨129191725368385625415713045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344511267649028334441901453 129191725368385625415713045)
                  ·
                    refine ⟨6055862126643076191361549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 129191725368385625415713045 6055862126643076191361549)
                    ·
                      refine ⟨2270948297491153571760581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6055862126643076191361549 2270948297491153571760581)
                      ·
                        rfl

theorem cell23_4422656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_4422656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422656 prefixEnd_4422656 := by exact prefixLift 4422656
  have htrace : WordTrace (prefixWord ++ tailWord_4422656) baseStart_4422656 baseEnd_4422656 := by
    simpa [prefixWord, tailWord_4422656, baseEnd_4422656] using wordTrace_append hprefix tailTrace_4422656
  have hstable : (prefixWord ++ tailWord_4422656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422656).length < 2 ^ (prefixWord ++ tailWord_4422656).sum := by decide
  have hdescent : baseEnd_4422656 < baseStart_4422656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422657 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_4422657 : Nat := 118140960795 + 4422657 * 2 ^ 59
def prefixEnd_4422657 : Nat := 4983230072969 + 3 ^ 40 * 4422657 * 2
def baseEnd_4422657 : Nat := 2270948810971808067848077

theorem tailTrace_4422657 : CollatzResearch.WordTrace tailWord_4422657 prefixEnd_4422657 2270948810971808067848077 := by
  unfold tailWord_4422657
  simp only [CollatzResearch.WordTrace]
  refine ⟨161307552738476493525842225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107538368492317662350561483 161307552738476493525842225)
  ·
    refine ⟨120980664553857370144381669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161307552738476493525842225 120980664553857370144381669)
    ·
      refine ⟨22683874603848256902071563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120980664553857370144381669 22683874603848256902071563)
      ·
        refine ⟨34025811905772385353107345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22683874603848256902071563 34025811905772385353107345)
        ·
          refine ⟨25519358929329289014830509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34025811905772385353107345 25519358929329289014830509)
          ·
            refine ⟨9569759598498483380561441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25519358929329289014830509 9569759598498483380561441)
            ·
              refine ⟨7177319698873862535421081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9569759598498483380561441 7177319698873862535421081)
              ·
                refine ⟨5382989774155396901565811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7177319698873862535421081 5382989774155396901565811)
                ·
                  refine ⟨8074484661233095352348717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382989774155396901565811 8074484661233095352348717)
                  ·
                    refine ⟨3027931747962410757130769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8074484661233095352348717 3027931747962410757130769)
                    ·
                      refine ⟨2270948810971808067848077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3027931747962410757130769 2270948810971808067848077)
                      ·
                        rfl

theorem cell23_4422657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_4422657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422657 prefixEnd_4422657 := by exact prefixLift 4422657
  have htrace : WordTrace (prefixWord ++ tailWord_4422657) baseStart_4422657 baseEnd_4422657 := by
    simpa [prefixWord, tailWord_4422657, baseEnd_4422657] using wordTrace_append hprefix tailTrace_4422657
  have hstable : (prefixWord ++ tailWord_4422657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422657).length < 2 ^ (prefixWord ++ tailWord_4422657).sum := by decide
  have hdescent : baseEnd_4422657 < baseStart_4422657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422723 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 2, 5]
def baseStart_4422723 : Nat := 118140960795 + 4422723 * 2 ^ 59
def prefixEnd_4422723 : Nat := 4983230072969 + 3 ^ 40 * 4422723 * 2
def baseEnd_4422723 : Nat := 756994233565001603207591

theorem tailTrace_4422723 : CollatzResearch.WordTrace tailWord_4422723 prefixEnd_4422723 756994233565001603207591 := by
  unfold tailWord_4422723
  simp only [CollatzResearch.WordTrace]
  refine ⟨161309959956237386797744823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107539973304158257865163215 161309959956237386797744823)
  ·
    refine ⟨241964939934356080196617235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161309959956237386797744823 241964939934356080196617235)
    ·
      refine ⟨362947409901534120294925853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241964939934356080196617235 362947409901534120294925853)
      ·
        refine ⟨136105278713075295110597195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362947409901534120294925853 136105278713075295110597195)
        ·
          refine ⟨204157918069612942665895793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136105278713075295110597195 204157918069612942665895793)
          ·
            refine ⟨153118438552209706999421845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204157918069612942665895793 153118438552209706999421845)
            ·
              refine ⟨7177426807134830015597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153118438552209706999421845 7177426807134830015597899)
              ·
                refine ⟨10766140210702245023396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7177426807134830015597899 10766140210702245023396849)
                ·
                  refine ⟨8074605158026683767547637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10766140210702245023396849 8074605158026683767547637)
                  ·
                    refine ⟨756994233565001603207591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8074605158026683767547637 756994233565001603207591)
                    ·
                      rfl

theorem cell23_4422723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 5].length) (baseStart_4422723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422723 prefixEnd_4422723 := by exact prefixLift 4422723
  have htrace : WordTrace (prefixWord ++ tailWord_4422723) baseStart_4422723 baseEnd_4422723 := by
    simpa [prefixWord, tailWord_4422723, baseEnd_4422723] using wordTrace_append hprefix tailTrace_4422723
  have hstable : (prefixWord ++ tailWord_4422723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422723).length < 2 ^ (prefixWord ++ tailWord_4422723).sum := by decide
  have hdescent : baseEnd_4422723 < baseStart_4422723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422770 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_4422770 : Nat := 118140960795 + 4422770 * 2 ^ 59
def prefixEnd_4422770 : Nat := 4983230072969 + 3 ^ 40 * 4422770 * 2
def baseEnd_4422770 : Nat := 757002278095255375245019

theorem tailTrace_4422770 : CollatzResearch.WordTrace tailWord_4422770 prefixEnd_4422770 757002278095255375245019 := by
  unfold tailWord_4422770
  simp only [CollatzResearch.WordTrace]
  refine ⟨40327918546766778456176441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107541116124711409216470509 40327918546766778456176441)
  ·
    refine ⟨30245938910075083842132331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40327918546766778456176441 30245938910075083842132331)
    ·
      refine ⟨45368908365112625763198497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30245938910075083842132331 45368908365112625763198497)
      ·
        refine ⟨34026681273834469322398873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45368908365112625763198497 34026681273834469322398873)
        ·
          refine ⟨25520010955375851991799155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34026681273834469322398873 25520010955375851991799155)
          ·
            refine ⟨38280016433063777987698733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25520010955375851991799155 38280016433063777987698733)
            ·
              refine ⟨14355006162398916745387025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38280016433063777987698733 14355006162398916745387025)
              ·
                refine ⟨10766254621799187559040269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14355006162398916745387025 10766254621799187559040269)
                ·
                  refine ⟨4037345483174695334640101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10766254621799187559040269 4037345483174695334640101)
                  ·
                    refine ⟨757002278095255375245019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037345483174695334640101 757002278095255375245019)
                    ·
                      rfl

theorem cell23_4422770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_4422770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422770 prefixEnd_4422770 := by exact prefixLift 4422770
  have htrace : WordTrace (prefixWord ++ tailWord_4422770) baseStart_4422770 baseEnd_4422770 := by
    simpa [prefixWord, tailWord_4422770, baseEnd_4422770] using wordTrace_append hprefix tailTrace_4422770
  have hstable : (prefixWord ++ tailWord_4422770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422770).length < 2 ^ (prefixWord ++ tailWord_4422770).sum := by decide
  have hdescent : baseEnd_4422770 < baseStart_4422770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422777 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_4422777 : Nat := 118140960795 + 4422777 * 2 ^ 59
def prefixEnd_4422777 : Nat := 4983230072969 + 3 ^ 40 * 4422777 * 2
def baseEnd_4422777 : Nat := 2271010428650347598347525

theorem tailTrace_4422777 : CollatzResearch.WordTrace tailWord_4422777 prefixEnd_4422777 2271010428650347598347525 := by
  unfold tailWord_4422777
  simp only [CollatzResearch.WordTrace]
  refine ⟨161311929498041754020210585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107541286332027836013473723 161311929498041754020210585)
  ·
    refine ⟨120983947123531315515157939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161311929498041754020210585 120983947123531315515157939)
    ·
      refine ⟨181475920685296973272736909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120983947123531315515157939 181475920685296973272736909)
      ·
        refine ⟨68053470256986364977276341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181475920685296973272736909 68053470256986364977276341)
        ·
          refine ⟨6380012836592471716619657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68053470256986364977276341 6380012836592471716619657)
          ·
            refine ⟨4785009627444353787464743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6380012836592471716619657 4785009627444353787464743)
            ·
              refine ⟨7177514441166530681197115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4785009627444353787464743 7177514441166530681197115)
              ·
                refine ⟨10766271661749796021795673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7177514441166530681197115 10766271661749796021795673)
                ·
                  refine ⟨8074703746312347016346755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10766271661749796021795673 8074703746312347016346755)
                  ·
                    refine ⟨12112055619468520524520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8074703746312347016346755 12112055619468520524520133)
                    ·
                      refine ⟨2271010428650347598347525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12112055619468520524520133 2271010428650347598347525)
                      ·
                        rfl

theorem cell23_4422777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_4422777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422777 prefixEnd_4422777 := by exact prefixLift 4422777
  have htrace : WordTrace (prefixWord ++ tailWord_4422777) baseStart_4422777 baseEnd_4422777 := by
    simpa [prefixWord, tailWord_4422777, baseEnd_4422777] using wordTrace_append hprefix tailTrace_4422777
  have hstable : (prefixWord ++ tailWord_4422777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422777).length < 2 ^ (prefixWord ++ tailWord_4422777).sum := by decide
  have hdescent : baseEnd_4422777 < baseStart_4422777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422787 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 1, 4]
def baseStart_4422787 : Nat := 118140960795 + 4422787 * 2 ^ 59
def prefixEnd_4422787 : Nat := 4983230072969 + 3 ^ 40 * 4422787 * 2
def baseEnd_4422787 : Nat := 757005187818964186407493

theorem tailTrace_4422787 : CollatzResearch.WordTrace tailWord_4422787 prefixEnd_4422787 757005187818964186407493 := by
  unfold tailWord_4422787
  simp only [CollatzResearch.WordTrace]
  refine ⟨161312294228005525728074615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107541529485337017152049743 161312294228005525728074615)
  ·
    refine ⟨241968441342008288592111923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161312294228005525728074615 241968441342008288592111923)
    ·
      refine ⟨362952662013012432888167885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241968441342008288592111923 362952662013012432888167885)
      ·
        refine ⟨136107248254879662333062957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362952662013012432888167885 136107248254879662333062957)
        ·
          refine ⟨51040218095579873374898609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136107248254879662333062957 51040218095579873374898609)
          ·
            refine ⟨38280163571684905031173957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51040218095579873374898609 38280163571684905031173957)
            ·
              refine ⟨7177530669690919693345117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38280163571684905031173957 7177530669690919693345117)
              ·
                refine ⟨2691574001134094885004419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177530669690919693345117 2691574001134094885004419)
                ·
                  refine ⟨4037361001701142327506629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691574001134094885004419 4037361001701142327506629)
                  ·
                    refine ⟨757005187818964186407493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037361001701142327506629 757005187818964186407493)
                    ·
                      rfl

theorem cell23_4422787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 4].length) (baseStart_4422787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422787 prefixEnd_4422787 := by exact prefixLift 4422787
  have htrace : WordTrace (prefixWord ++ tailWord_4422787) baseStart_4422787 baseEnd_4422787 := by
    simpa [prefixWord, tailWord_4422787, baseEnd_4422787] using wordTrace_append hprefix tailTrace_4422787
  have hstable : (prefixWord ++ tailWord_4422787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422787).length < 2 ^ (prefixWord ++ tailWord_4422787).sum := by decide
  have hdescent : baseEnd_4422787 < baseStart_4422787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422863 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_4422863 : Nat := 118140960795 + 4422863 * 2 ^ 59
def prefixEnd_4422863 : Nat := 4983230072969 + 3 ^ 40 * 4422863 * 2
def baseEnd_4422863 : Nat := 2271054587986634261872129

theorem tailTrace_4422863 : CollatzResearch.WordTrace tailWord_4422863 prefixEnd_4422863 2271054587986634261872129 := by
  unfold tailWord_4422863
  simp only [CollatzResearch.WordTrace]
  refine ⟨161315066175730190707841243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107543377450486793805227495 161315066175730190707841243)
  ·
    refine ⟨241972599263595286061761865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161315066175730190707841243 241972599263595286061761865)
    ·
      refine ⟨181479449447696464546321399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241972599263595286061761865 181479449447696464546321399)
      ·
        refine ⟨272219174171544696819482099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181479449447696464546321399 272219174171544696819482099)
        ·
          refine ⟨408328761257317045229223149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272219174171544696819482099 408328761257317045229223149)
          ·
            refine ⟨153123285471493891960958681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408328761257317045229223149 153123285471493891960958681)
            ·
              refine ⟨114842464103620418970719011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153123285471493891960958681 114842464103620418970719011)
              ·
                refine ⟨172263696155430628456078517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114842464103620418970719011 172263696155430628456078517)
                ·
                  refine ⟨16149721514571621417757361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172263696155430628456078517 16149721514571621417757361)
                  ·
                    refine ⟨12112291135928716063318021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16149721514571621417757361 12112291135928716063318021)
                    ·
                      refine ⟨2271054587986634261872129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12112291135928716063318021 2271054587986634261872129)
                      ·
                        rfl

theorem cell23_4422863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_4422863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422863 prefixEnd_4422863 := by exact prefixLift 4422863
  have htrace : WordTrace (prefixWord ++ tailWord_4422863) baseStart_4422863 baseEnd_4422863 := by
    simpa [prefixWord, tailWord_4422863, baseEnd_4422863] using wordTrace_append hprefix tailTrace_4422863
  have hstable : (prefixWord ++ tailWord_4422863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422863).length < 2 ^ (prefixWord ++ tailWord_4422863).sum := by decide
  have hdescent : baseEnd_4422863 < baseStart_4422863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422953 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_4422953 : Nat := 118140960795 + 4422953 * 2 ^ 59
def prefixEnd_4422953 : Nat := 4983230072969 + 3 ^ 40 * 4422953 * 2
def baseEnd_4422953 : Nat := 2271100801245538909746715

theorem tailTrace_4422953 : CollatzResearch.WordTrace tailWord_4422953 prefixEnd_4422953 2271100801245538909746715 := by
  unfold tailWord_4422953
  simp only [CollatzResearch.WordTrace]
  refine ⟨161318348745404136078617513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107545565830269424052411675 161318348745404136078617513)
  ·
    refine ⟨120988761559053102058963135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161318348745404136078617513 120988761559053102058963135)
    ·
      refine ⟨181483142338579653088444703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120988761559053102058963135 181483142338579653088444703)
      ·
        refine ⟨272224713507869479632667055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181483142338579653088444703 272224713507869479632667055)
        ·
          refine ⟨408337070261804219449000583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272224713507869479632667055 408337070261804219449000583)
          ·
            refine ⟨612505605392706329173500875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408337070261804219449000583 612505605392706329173500875)
            ·
              refine ⟨918758408089059493760251313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612505605392706329173500875 918758408089059493760251313)
              ·
                refine ⟨689068806066794620320188485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918758408089059493760251313 689068806066794620320188485)
                ·
                  refine ⟨129200401137523991310035341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689068806066794620320188485 129200401137523991310035341)
                  ·
                    refine ⟨48450150426571496741263253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129200401137523991310035341 48450150426571496741263253)
                    ·
                      refine ⟨2271100801245538909746715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48450150426571496741263253 2271100801245538909746715)
                      ·
                        rfl

theorem cell23_4422953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_4422953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422953 prefixEnd_4422953 := by exact prefixLift 4422953
  have htrace : WordTrace (prefixWord ++ tailWord_4422953) baseStart_4422953 baseEnd_4422953 := by
    simpa [prefixWord, tailWord_4422953, baseEnd_4422953] using wordTrace_append hprefix tailTrace_4422953
  have hstable : (prefixWord ++ tailWord_4422953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422953).length < 2 ^ (prefixWord ++ tailWord_4422953).sum := by decide
  have hdescent : baseEnd_4422953 < baseStart_4422953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422961 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_4422961 : Nat := 118140960795 + 4422961 * 2 ^ 59
def prefixEnd_4422961 : Nat := 4983230072969 + 3 ^ 40 * 4422961 * 2
def baseEnd_4422961 : Nat := 2271104909090774878446679

theorem tailTrace_4422961 : CollatzResearch.WordTrace tailWord_4422961 prefixEnd_4422961 2271104909090774878446679 := by
  unfold tailWord_4422961
  simp only [CollatzResearch.WordTrace]
  refine ⟨161318640529375153444908737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107545760352916768963272491 161318640529375153444908737)
  ·
    refine ⟨120988980397031365083681553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161318640529375153444908737 120988980397031365083681553)
    ·
      refine ⟨90741735297773523812761165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120988980397031365083681553 90741735297773523812761165)
      ·
        refine ⟨34028150736665071429785437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90741735297773523812761165 34028150736665071429785437)
        ·
          refine ⟨12760556526249401786169539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34028150736665071429785437 12760556526249401786169539)
          ·
            refine ⟨19140834789374102679254309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760556526249401786169539 19140834789374102679254309)
            ·
              refine ⟨3588906523007644252360183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19140834789374102679254309 3588906523007644252360183)
              ·
                refine ⟨5383359784511466378540275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588906523007644252360183 5383359784511466378540275)
                ·
                  refine ⟨8075039676767199567810413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383359784511466378540275 8075039676767199567810413)
                  ·
                    refine ⟨3028139878787699837928905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8075039676767199567810413 3028139878787699837928905)
                    ·
                      refine ⟨2271104909090774878446679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028139878787699837928905 2271104909090774878446679)
                      ·
                        rfl

theorem cell23_4422961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_4422961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422961 prefixEnd_4422961 := by exact prefixLift 4422961
  have htrace : WordTrace (prefixWord ++ tailWord_4422961) baseStart_4422961 baseEnd_4422961 := by
    simpa [prefixWord, tailWord_4422961, baseEnd_4422961] using wordTrace_append hprefix tailTrace_4422961
  have hstable : (prefixWord ++ tailWord_4422961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422961).length < 2 ^ (prefixWord ++ tailWord_4422961).sum := by decide
  have hdescent : baseEnd_4422961 < baseStart_4422961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4422970 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_4422970 : Nat := 118140960795 + 4422970 * 2 ^ 59
def prefixEnd_4422970 : Nat := 4983230072969 + 3 ^ 40 * 4422970 * 2
def baseEnd_4422970 : Nat := 2271109530416665343234137

theorem tailTrace_4422970 : CollatzResearch.WordTrace tailWord_4422970 prefixEnd_4422970 2271109530416665343234137 := by
  unfold tailWord_4422970
  simp only [CollatzResearch.WordTrace]
  refine ⟨40329742196585636995496591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107545979190895031987990909 40329742196585636995496591)
  ·
    refine ⟨60494613294878455493244887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40329742196585636995496591 60494613294878455493244887)
    ·
      refine ⟨90741919942317683239867331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60494613294878455493244887 90741919942317683239867331)
      ·
        refine ⟨136112879913476524859800997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90741919942317683239867331 136112879913476524859800997)
        ·
          refine ⟨25521164983776848411212687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136112879913476524859800997 25521164983776848411212687)
          ·
            refine ⟨38281747475665272616819031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25521164983776848411212687 38281747475665272616819031)
            ·
              refine ⟨57422621213497908925228547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38281747475665272616819031 57422621213497908925228547)
              ·
                refine ⟨86133931820246863387842821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57422621213497908925228547 86133931820246863387842821)
                ·
                  refine ⟨16150112216296286885220529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86133931820246863387842821 16150112216296286885220529)
                  ·
                    refine ⟨12112584162222215163915397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16150112216296286885220529 12112584162222215163915397)
                    ·
                      refine ⟨2271109530416665343234137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12112584162222215163915397 2271109530416665343234137)
                      ·
                        rfl

theorem cell23_4422970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_4422970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4422970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4422970 prefixEnd_4422970 := by exact prefixLift 4422970
  have htrace : WordTrace (prefixWord ++ tailWord_4422970) baseStart_4422970 baseEnd_4422970 := by
    simpa [prefixWord, tailWord_4422970, baseEnd_4422970] using wordTrace_append hprefix tailTrace_4422970
  have hstable : (prefixWord ++ tailWord_4422970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4422970).length < 2 ^ (prefixWord ++ tailWord_4422970).sum := by decide
  have hdescent : baseEnd_4422970 < baseStart_4422970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4422970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423042 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4423042 : Nat := 118140960795 + 4423042 * 2 ^ 59
def prefixEnd_4423042 : Nat := 4983230072969 + 3 ^ 40 * 4423042 * 2
def baseEnd_4423042 : Nat := 2271146501023789061533807

theorem tailTrace_4423042 : CollatzResearch.WordTrace tailWord_4423042 prefixEnd_4423042 2271146501023789061533807 := by
  unfold tailWord_4423042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330398710520426069651845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107547729894721136185738253 40330398710520426069651845)
  ·
    refine ⟨7561949758222579888059721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40330398710520426069651845 7561949758222579888059721)
    ·
      refine ⟨5671462318666934916044791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7561949758222579888059721 5671462318666934916044791)
      ·
        refine ⟨8507193478000402374067187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671462318666934916044791 8507193478000402374067187)
        ·
          refine ⟨12760790217000603561100781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507193478000402374067187 12760790217000603561100781)
          ·
            refine ⟨4785296331375226335412793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12760790217000603561100781 4785296331375226335412793)
            ·
              refine ⟨3588972248531419751559595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785296331375226335412793 3588972248531419751559595)
              ·
                refine ⟨5383458372797129627339393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588972248531419751559595 5383458372797129627339393)
                ·
                  refine ⟨4037593779597847220504545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5383458372797129627339393 4037593779597847220504545)
                  ·
                    refine ⟨3028195334698385415378409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4037593779597847220504545 3028195334698385415378409)
                    ·
                      refine ⟨2271146501023789061533807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028195334698385415378409 2271146501023789061533807)
                      ·
                        rfl

theorem cell23_4423042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4423042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423042 prefixEnd_4423042 := by exact prefixLift 4423042
  have htrace : WordTrace (prefixWord ++ tailWord_4423042) baseStart_4423042 baseEnd_4423042 := by
    simpa [prefixWord, tailWord_4423042, baseEnd_4423042] using wordTrace_append hprefix tailTrace_4423042
  have hstable : (prefixWord ++ tailWord_4423042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423042).length < 2 ^ (prefixWord ++ tailWord_4423042).sum := by decide
  have hdescent : baseEnd_4423042 < baseStart_4423042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423114 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_4423114 : Nat := 118140960795 + 4423114 * 2 ^ 59
def prefixEnd_4423114 : Nat := 4983230072969 + 3 ^ 40 * 4423114 * 2
def baseEnd_4423114 : Nat := 2271183471630912779833475

theorem tailTrace_4423114 : CollatzResearch.WordTrace tailWord_4423114 prefixEnd_4423114 2271183471630912779833475 := by
  unfold tailWord_4423114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40331055224455215143807099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107549480598547240383485597 40331055224455215143807099)
  ·
    refine ⟨60496582836682822715710649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40331055224455215143807099 60496582836682822715710649)
    ·
      refine ⟨45372437127512117036782987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60496582836682822715710649 45372437127512117036782987)
      ·
        refine ⟨68058655691268175555174481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45372437127512117036782987 68058655691268175555174481)
        ·
          refine ⟨51043991768451131666380861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68058655691268175555174481 51043991768451131666380861)
          ·
            refine ⟨19141496913169174374892823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51043991768451131666380861 19141496913169174374892823)
            ·
              refine ⟨28712245369753761562339235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19141496913169174374892823 28712245369753761562339235)
              ·
                refine ⟨43068368054630642343508853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28712245369753761562339235 43068368054630642343508853)
                ·
                  refine ⟨4037659505121622719703955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43068368054630642343508853 4037659505121622719703955)
                  ·
                    refine ⟨6056489257682434079555933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4037659505121622719703955 6056489257682434079555933)
                    ·
                      refine ⟨2271183471630912779833475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6056489257682434079555933 2271183471630912779833475)
                      ·
                        rfl

theorem cell23_4423114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_4423114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423114 prefixEnd_4423114 := by exact prefixLift 4423114
  have htrace : WordTrace (prefixWord ++ tailWord_4423114) baseStart_4423114 baseEnd_4423114 := by
    simpa [prefixWord, tailWord_4423114, baseEnd_4423114] using wordTrace_append hprefix tailTrace_4423114
  have hstable : (prefixWord ++ tailWord_4423114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423114).length < 2 ^ (prefixWord ++ tailWord_4423114).sum := by decide
  have hdescent : baseEnd_4423114 < baseStart_4423114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423164 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_4423164 : Nat := 118140960795 + 4423164 * 2 ^ 59
def prefixEnd_4423164 : Nat := 4983230072969 + 3 ^ 40 * 4423164 * 2
def baseEnd_4423164 : Nat := 757069715221212528069415

theorem tailTrace_4423164 : CollatzResearch.WordTrace tailWord_4423164 prefixEnd_4423164 757069715221212528069415 := by
  unfold tailWord_4423164
  simp only [CollatzResearch.WordTrace]
  refine ⟨80663022273819859557274273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107550696365093146076365697 80663022273819859557274273)
  ·
    refine ⟨60497266705364894667955705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80663022273819859557274273 60497266705364894667955705)
    ·
      refine ⟨45372950029023671000966779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60497266705364894667955705 45372950029023671000966779)
      ·
        refine ⟨68059425043535506501450169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45372950029023671000966779 68059425043535506501450169)
        ·
          refine ⟨51044568782651629876087627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68059425043535506501450169 51044568782651629876087627)
          ·
            refine ⟨76566853173977444814131441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51044568782651629876087627 76566853173977444814131441)
            ·
              refine ⟨57425139880483083610598581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76566853173977444814131441 57425139880483083610598581)
              ·
                refine ⟨5383606863795289088493617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57425139880483083610598581 5383606863795289088493617)
                ·
                  refine ⟨4037705147846466816370213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5383606863795289088493617 4037705147846466816370213)
                  ·
                    refine ⟨757069715221212528069415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037705147846466816370213 757069715221212528069415)
                    ·
                      rfl

theorem cell23_4423164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_4423164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423164 prefixEnd_4423164 := by exact prefixLift 4423164
  have htrace : WordTrace (prefixWord ++ tailWord_4423164) baseStart_4423164 baseEnd_4423164 := by
    simpa [prefixWord, tailWord_4423164, baseEnd_4423164] using wordTrace_append hprefix tailTrace_4423164
  have hstable : (prefixWord ++ tailWord_4423164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423164).length < 2 ^ (prefixWord ++ tailWord_4423164).sum := by decide
  have hdescent : baseEnd_4423164 < baseStart_4423164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423167 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_4423167 : Nat := 118140960795 + 4423167 * 2 ^ 59
def prefixEnd_4423167 : Nat := 4983230072969 + 3 ^ 40 * 4423167 * 2
def baseEnd_4423167 : Nat := 2271210686105601072470731

theorem tailTrace_4423167 : CollatzResearch.WordTrace tailWord_4423167 prefixEnd_4423167 2271210686105601072470731 := by
  unfold tailWord_4423167
  simp only [CollatzResearch.WordTrace]
  refine ⟨161326153966628850626907755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107550769311085900417938503 161326153966628850626907755)
  ·
    refine ⟨241989230949943275940361633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161326153966628850626907755 241989230949943275940361633)
    ·
      refine ⟨181491923212457456955271225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241989230949943275940361633 181491923212457456955271225)
      ·
        refine ⟨136118942409343092716453419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181491923212457456955271225 136118942409343092716453419)
        ·
          refine ⟨204178413614014639074680129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136118942409343092716453419 204178413614014639074680129)
          ·
            refine ⟨153133810210510979306010097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204178413614014639074680129 153133810210510979306010097)
            ·
              refine ⟨114850357657883234479507573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153133810210510979306010097 114850357657883234479507573)
              ·
                refine ⟨10767221030426553232453835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114850357657883234479507573 10767221030426553232453835)
                ·
                  refine ⟨16150831545639829848680753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10767221030426553232453835 16150831545639829848680753)
                  ·
                    refine ⟨12113123659229872386510565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16150831545639829848680753 12113123659229872386510565)
                    ·
                      refine ⟨2271210686105601072470731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12113123659229872386510565 2271210686105601072470731)
                      ·
                        rfl

theorem cell23_4423167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_4423167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423167 prefixEnd_4423167 := by exact prefixLift 4423167
  have htrace : WordTrace (prefixWord ++ tailWord_4423167) baseStart_4423167 baseEnd_4423167 := by
    simpa [prefixWord, tailWord_4423167, baseEnd_4423167] using wordTrace_append hprefix tailTrace_4423167
  have hstable : (prefixWord ++ tailWord_4423167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423167).length < 2 ^ (prefixWord ++ tailWord_4423167).sum := by decide
  have hdescent : baseEnd_4423167 < baseStart_4423167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423182 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4423182 : Nat := 118140960795 + 4423182 * 2 ^ 59
def prefixEnd_4423182 : Nat := 4983230072969 + 3 ^ 40 * 4423182 * 2
def baseEnd_4423182 : Nat := 2271218388315418513783163

theorem tailTrace_4423182 : CollatzResearch.WordTrace tailWord_4423182 prefixEnd_4423182 2271218388315418513783163 := by
  unfold tailWord_4423182
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165837632696813523587975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107551134041049672125802533 20165837632696813523587975)
  ·
    refine ⟨30248756449045220285381963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20165837632696813523587975 30248756449045220285381963)
    ·
      refine ⟨45373134673567830428072945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30248756449045220285381963 45373134673567830428072945)
      ·
        refine ⟨34029851005175872821054709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45373134673567830428072945 34029851005175872821054709)
        ·
          refine ⟨3190298531735238076973879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34029851005175872821054709 3190298531735238076973879)
          ·
            refine ⟨4785447797602857115460819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190298531735238076973879 4785447797602857115460819)
            ·
              refine ⟨7178171696404285673191229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4785447797602857115460819 7178171696404285673191229)
              ·
                refine ⟨2691814386151607127446711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7178171696404285673191229 2691814386151607127446711)
                ·
                  refine ⟨4037721579227410691170067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691814386151607127446711 4037721579227410691170067)
                  ·
                    refine ⟨6056582368841116036755101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4037721579227410691170067 6056582368841116036755101)
                    ·
                      refine ⟨2271218388315418513783163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6056582368841116036755101 2271218388315418513783163)
                      ·
                        rfl

theorem cell23_4423182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4423182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423182 prefixEnd_4423182 := by exact prefixLift 4423182
  have htrace : WordTrace (prefixWord ++ tailWord_4423182) baseStart_4423182 baseEnd_4423182 := by
    simpa [prefixWord, tailWord_4423182, baseEnd_4423182] using wordTrace_append hprefix tailTrace_4423182
  have hstable : (prefixWord ++ tailWord_4423182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423182).length < 2 ^ (prefixWord ++ tailWord_4423182).sum := by decide
  have hdescent : baseEnd_4423182 < baseStart_4423182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423231 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 3, 3, 2]
def baseStart_4423231 : Nat := 118140960795 + 4423231 * 2 ^ 59
def prefixEnd_4423231 : Nat := 4983230072969 + 3 ^ 40 * 4423231 * 2
def baseEnd_4423231 : Nat := 2271243548867488822070437

theorem tailTrace_4423231 : CollatzResearch.WordTrace tailWord_4423231 prefixEnd_4423231 2271243548867488822070437 := by
  unfold tailWord_4423231
  simp only [CollatzResearch.WordTrace]
  refine ⟨161328488238396989557237547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107552325492264659704825031 161328488238396989557237547)
  ·
    refine ⟨241992732357595484335856321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161328488238396989557237547 241992732357595484335856321)
    ·
      refine ⟨181494549268196613251892241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241992732357595484335856321 181494549268196613251892241)
      ·
        refine ⟨136120911951147459938919181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181494549268196613251892241 136120911951147459938919181)
        ·
          refine ⟨51045341981680297477094693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136120911951147459938919181 51045341981680297477094693)
          ·
            refine ⟨9571001621565055776955255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51045341981680297477094693 9571001621565055776955255)
            ·
              refine ⟨14356502432347583665432883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9571001621565055776955255 14356502432347583665432883)
              ·
                refine ⟨21534753648521375498149325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14356502432347583665432883 21534753648521375498149325)
                ·
                  refine ⟨8075532618195515811805997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21534753648521375498149325 8075532618195515811805997)
                  ·
                    refine ⟨3028324731823318429427249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8075532618195515811805997 3028324731823318429427249)
                    ·
                      refine ⟨2271243548867488822070437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028324731823318429427249 2271243548867488822070437)
                      ·
                        rfl

theorem cell23_4423231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_4423231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423231 prefixEnd_4423231 := by exact prefixLift 4423231
  have htrace : WordTrace (prefixWord ++ tailWord_4423231) baseStart_4423231 baseEnd_4423231 := by
    simpa [prefixWord, tailWord_4423231, baseEnd_4423231] using wordTrace_append hprefix tailTrace_4423231
  have hstable : (prefixWord ++ tailWord_4423231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423231).length < 2 ^ (prefixWord ++ tailWord_4423231).sum := by decide
  have hdescent : baseEnd_4423231 < baseStart_4423231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423248 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2]
def baseStart_4423248 : Nat := 118140960795 + 4423248 * 2 ^ 59
def prefixEnd_4423248 : Nat := 4983230072969 + 3 ^ 40 * 4423248 * 2
def baseEnd_4423248 : Nat := 2271252278038615255557859

theorem tailTrace_4423248 : CollatzResearch.WordTrace tailWord_4423248 prefixEnd_4423248 2271252278038615255557859 := by
  unfold tailWord_4423248
  simp only [CollatzResearch.WordTrace]
  refine ⟨80664554139667700730303199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107552738852890267640404265 80664554139667700730303199)
  ·
    refine ⟨120996831209501551095454799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80664554139667700730303199 120996831209501551095454799)
    ·
      refine ⟨181495246814252326643182199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120996831209501551095454799 181495246814252326643182199)
      ·
        refine ⟨272242870221378489964773299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181495246814252326643182199 272242870221378489964773299)
        ·
          refine ⟨408364305332067734947159949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272242870221378489964773299 408364305332067734947159949)
          ·
            refine ⟨153136614499525400605184981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408364305332067734947159949 153136614499525400605184981)
            ·
              refine ⟨3589139402332626576684023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 153136614499525400605184981 3589139402332626576684023)
              ·
                refine ⟨5383709103498939865026035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589139402332626576684023 5383709103498939865026035)
                ·
                  refine ⟨8075563655248409797539053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383709103498939865026035 8075563655248409797539053)
                  ·
                    refine ⟨3028336370718153674077145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8075563655248409797539053 3028336370718153674077145)
                    ·
                      refine ⟨2271252278038615255557859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028336370718153674077145 2271252278038615255557859)
                      ·
                        rfl

theorem cell23_4423248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2].length) (baseStart_4423248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423248 prefixEnd_4423248 := by exact prefixLift 4423248
  have htrace : WordTrace (prefixWord ++ tailWord_4423248) baseStart_4423248 baseEnd_4423248 := by
    simpa [prefixWord, tailWord_4423248, baseEnd_4423248] using wordTrace_append hprefix tailTrace_4423248
  have hstable : (prefixWord ++ tailWord_4423248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423248).length < 2 ^ (prefixWord ++ tailWord_4423248).sum := by decide
  have hdescent : baseEnd_4423248 < baseStart_4423248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423257 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_4423257 : Nat := 118140960795 + 4423257 * 2 ^ 59
def prefixEnd_4423257 : Nat := 4983230072969 + 3 ^ 40 * 4423257 * 2
def baseEnd_4423257 : Nat := 2271256899364505720345317

theorem tailTrace_4423257 : CollatzResearch.WordTrace tailWord_4423257 prefixEnd_4423257 2271256899364505720345317 := by
  unfold tailWord_4423257
  simp only [CollatzResearch.WordTrace]
  refine ⟨161329436536302795997684025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107552957690868530665122683 161329436536302795997684025)
  ·
    refine ⟨120997077402227096998263019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161329436536302795997684025 120997077402227096998263019)
    ·
      refine ⟨181495616103340645497394529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120997077402227096998263019 181495616103340645497394529)
      ·
        refine ⟨136121712077505484123045897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181495616103340645497394529 136121712077505484123045897)
        ·
          refine ⟨102091284058129113092284423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136121712077505484123045897 102091284058129113092284423)
          ·
            refine ⟨153136926087193669638426635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102091284058129113092284423 153136926087193669638426635)
            ·
              refine ⟨229705389130790504457639953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153136926087193669638426635 229705389130790504457639953)
              ·
                refine ⟨172279041848092878343229965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229705389130790504457639953 172279041848092878343229965)
                ·
                  refine ⟨64604640693034829378711237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172279041848092878343229965 64604640693034829378711237)
                  ·
                    refine ⟨12113370129944030508508357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64604640693034829378711237 12113370129944030508508357)
                    ·
                      refine ⟨2271256899364505720345317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12113370129944030508508357 2271256899364505720345317)
                      ·
                        rfl

theorem cell23_4423257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_4423257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423257 prefixEnd_4423257 := by exact prefixLift 4423257
  have htrace : WordTrace (prefixWord ++ tailWord_4423257) baseStart_4423257 baseEnd_4423257 := by
    simpa [prefixWord, tailWord_4423257, baseEnd_4423257] using wordTrace_append hprefix tailTrace_4423257
  have hstable : (prefixWord ++ tailWord_4423257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423257).length < 2 ^ (prefixWord ++ tailWord_4423257).sum := by decide
  have hdescent : baseEnd_4423257 < baseStart_4423257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423274 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4423274 : Nat := 118140960795 + 4423274 * 2 ^ 59
def prefixEnd_4423274 : Nat := 4983230072969 + 3 ^ 40 * 4423274 * 2
def baseEnd_4423274 : Nat := 2271265628535632153832739

theorem tailTrace_4423274 : CollatzResearch.WordTrace tailWord_4423274 prefixEnd_4423274 2271265628535632153832739 := by
  unfold tailWord_4423274
  simp only [CollatzResearch.WordTrace]
  refine ⟨40332514144310301975263219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107553371051494138600701917 40332514144310301975263219)
  ·
    refine ⟨60498771216465452962894829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40332514144310301975263219 60498771216465452962894829)
    ·
      refine ⟨22687039206174544861085561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60498771216465452962894829 22687039206174544861085561)
      ·
        refine ⟨17015279404630908645814171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22687039206174544861085561 17015279404630908645814171)
        ·
          refine ⟨25522919106946362968721257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17015279404630908645814171 25522919106946362968721257)
          ·
            refine ⟨19142189330209772226540943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25522919106946362968721257 19142189330209772226540943)
            ·
              refine ⟨28713283995314658339811415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19142189330209772226540943 28713283995314658339811415)
              ·
                refine ⟨43069925992971987509717123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28713283995314658339811415 43069925992971987509717123)
                ·
                  refine ⟨64604888989457981264575685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43069925992971987509717123 64604888989457981264575685)
                  ·
                    refine ⟨12113416685523371487107941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64604888989457981264575685 12113416685523371487107941)
                    ·
                      refine ⟨2271265628535632153832739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12113416685523371487107941 2271265628535632153832739)
                      ·
                        rfl

theorem cell23_4423274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4423274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423274 prefixEnd_4423274 := by exact prefixLift 4423274
  have htrace : WordTrace (prefixWord ++ tailWord_4423274) baseStart_4423274 baseEnd_4423274 := by
    simpa [prefixWord, tailWord_4423274, baseEnd_4423274] using wordTrace_append hprefix tailTrace_4423274
  have hstable : (prefixWord ++ tailWord_4423274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423274).length < 2 ^ (prefixWord ++ tailWord_4423274).sum := by decide
  have hdescent : baseEnd_4423274 < baseStart_4423274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423301 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 5]
def baseStart_4423301 : Nat := 118140960795 + 4423301 * 2 ^ 59
def prefixEnd_4423301 : Nat := 4983230072969 + 3 ^ 40 * 4423301 * 2
def baseEnd_4423301 : Nat := 252364388057033727577235

theorem tailTrace_4423301 : CollatzResearch.WordTrace tailWord_4423301 prefixEnd_4423301 252364388057033727577235 := by
  unfold tailWord_4423301
  simp only [CollatzResearch.WordTrace]
  refine ⟨161331041348143391512285757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107554027565428927674857171 161331041348143391512285757)
  ·
    refine ⟨60499140505553771817107159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161331041348143391512285757 60499140505553771817107159)
    ·
      refine ⟨90748710758330657725660739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60499140505553771817107159 90748710758330657725660739)
      ·
        refine ⟨136123066137495986588491109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90748710758330657725660739 136123066137495986588491109)
        ·
          refine ⟨25523074900780497485342083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136123066137495986588491109 25523074900780497485342083)
          ·
            refine ⟨38284612351170746228013125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25523074900780497485342083 38284612351170746228013125)
            ·
              refine ⟨7178364815844514917752461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38284612351170746228013125 7178364815844514917752461)
              ·
                refine ⟨2691886805941693094157173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7178364815844514917752461 2691886805941693094157173)
                ·
                  refine ⟨252364388057033727577235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2691886805941693094157173 252364388057033727577235)
                  ·
                    rfl

theorem cell23_4423301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_4423301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423301 prefixEnd_4423301 := by exact prefixLift 4423301
  have htrace : WordTrace (prefixWord ++ tailWord_4423301) baseStart_4423301 baseEnd_4423301 := by
    simpa [prefixWord, tailWord_4423301, baseEnd_4423301] using wordTrace_append hprefix tailTrace_4423301
  have hstable : (prefixWord ++ tailWord_4423301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423301).length < 2 ^ (prefixWord ++ tailWord_4423301).sum := by decide
  have hdescent : baseEnd_4423301 < baseStart_4423301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423337 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_4423337 : Nat := 118140960795 + 4423337 * 2 ^ 59
def prefixEnd_4423337 : Nat := 4983230072969 + 3 ^ 40 * 4423337 * 2
def baseEnd_4423337 : Nat := 2271297977816865407344949

theorem tailTrace_4423337 : CollatzResearch.WordTrace tailWord_4423337 prefixEnd_4423337 2271297977816865407344949 := by
  unfold tailWord_4423337
  simp only [CollatzResearch.WordTrace]
  refine ⟨161332354376012969660596265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107554902917341979773730843 161332354376012969660596265)
  ·
    refine ⟨120999265782009727245447199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161332354376012969660596265 120999265782009727245447199)
    ·
      refine ⟨181498898673014590868170799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120999265782009727245447199 181498898673014590868170799)
      ·
        refine ⟨272248348009521886302256199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181498898673014590868170799 272248348009521886302256199)
        ·
          refine ⟨408372522014282829453384299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272248348009521886302256199 408372522014282829453384299)
          ·
            refine ⟨612558783021424244180076449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408372522014282829453384299 612558783021424244180076449)
            ·
              refine ⟨459419087266068183135057337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612558783021424244180076449 459419087266068183135057337)
              ·
                refine ⟨344564315449551137351293003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459419087266068183135057337 344564315449551137351293003)
                ·
                  refine ⟨516846473174326706026939505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344564315449551137351293003 516846473174326706026939505)
                  ·
                    refine ⟨387634854880745029520204629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 516846473174326706026939505 387634854880745029520204629)
                    ·
                      refine ⟨2271297977816865407344949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 387634854880745029520204629 2271297977816865407344949)
                      ·
                        rfl

theorem cell23_4423337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_4423337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423337 prefixEnd_4423337 := by exact prefixLift 4423337
  have htrace : WordTrace (prefixWord ++ tailWord_4423337) baseStart_4423337 baseEnd_4423337 := by
    simpa [prefixWord, tailWord_4423337, baseEnd_4423337] using wordTrace_append hprefix tailTrace_4423337
  have hstable : (prefixWord ++ tailWord_4423337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423337).length < 2 ^ (prefixWord ++ tailWord_4423337).sum := by decide
  have hdescent : baseEnd_4423337 < baseStart_4423337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423374 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_4423374 : Nat := 118140960795 + 4423374 * 2 ^ 59
def prefixEnd_4423374 : Nat := 4983230072969 + 3 ^ 40 * 4423374 * 2
def baseEnd_4423374 : Nat := 252368552955675751398031

theorem tailTrace_4423374 : CollatzResearch.WordTrace tailWord_4423374 prefixEnd_4423374 252368552955675751398031 := by
  unfold tailWord_4423374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166712984609865622461647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107555802584585949986462117 20166712984609865622461647)
  ·
    refine ⟨30250069476914798433692471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20166712984609865622461647 30250069476914798433692471)
    ·
      refine ⟨45375104215372197650538707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30250069476914798433692471 45375104215372197650538707)
      ·
        refine ⟨68062656323058296475808061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45375104215372197650538707 68062656323058296475808061)
        ·
          refine ⟨25523496121146861178428023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68062656323058296475808061 25523496121146861178428023)
          ·
            refine ⟨38285244181720291767642035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25523496121146861178428023 38285244181720291767642035)
            ·
              refine ⟨57427866272580437651463053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38285244181720291767642035 57427866272580437651463053)
              ·
                refine ⟨21535449852217664119298645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57427866272580437651463053 21535449852217664119298645)
                ·
                  refine ⟨252368552955675751398031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21535449852217664119298645 252368552955675751398031)
                  ·
                    rfl

theorem cell23_4423374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_4423374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423374 prefixEnd_4423374 := by exact prefixLift 4423374
  have htrace : WordTrace (prefixWord ++ tailWord_4423374) baseStart_4423374 baseEnd_4423374 := by
    simpa [prefixWord, tailWord_4423374, baseEnd_4423374] using wordTrace_append hprefix tailTrace_4423374
  have hstable : (prefixWord ++ tailWord_4423374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423374).length < 2 ^ (prefixWord ++ tailWord_4423374).sum := by decide
  have hdescent : baseEnd_4423374 < baseStart_4423374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423378 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_4423378 : Nat := 118140960795 + 4423378 * 2 ^ 59
def prefixEnd_4423378 : Nat := 4983230072969 + 3 ^ 40 * 4423378 * 2
def baseEnd_4423378 : Nat := 757106343507899915644087

theorem tailTrace_4423378 : CollatzResearch.WordTrace tailWord_4423378 prefixEnd_4423378 757106343507899915644087 := by
  unfold tailWord_4423378
  simp only [CollatzResearch.WordTrace]
  refine ⟨40333462442216108415709697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107555899845909622441892525 40333462442216108415709697)
  ·
    refine ⟨30250096831662081311782273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40333462442216108415709697 30250096831662081311782273)
    ·
      refine ⟨22687572623746560983836705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30250096831662081311782273 22687572623746560983836705)
      ·
        refine ⟨17015679467809920737877529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22687572623746560983836705 17015679467809920737877529)
        ·
          refine ⟨12761759600857440553408147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17015679467809920737877529 12761759600857440553408147)
          ·
            refine ⟨19142639401286160830112221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12761759600857440553408147 19142639401286160830112221)
            ·
              refine ⟨7178489775482310311292083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19142639401286160830112221 7178489775482310311292083)
              ·
                refine ⟨10767734663223465466938125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7178489775482310311292083 10767734663223465466938125)
                ·
                  refine ⟨4037900498708799550101797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10767734663223465466938125 4037900498708799550101797)
                  ·
                    refine ⟨757106343507899915644087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037900498708799550101797 757106343507899915644087)
                    ·
                      rfl

theorem cell23_4423378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_4423378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423378 prefixEnd_4423378 := by exact prefixLift 4423378
  have htrace : WordTrace (prefixWord ++ tailWord_4423378) baseStart_4423378 baseEnd_4423378 := by
    simpa [prefixWord, tailWord_4423378, baseEnd_4423378] using wordTrace_append hprefix tailTrace_4423378
  have hstable : (prefixWord ++ tailWord_4423378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423378).length < 2 ^ (prefixWord ++ tailWord_4423378).sum := by decide
  have hdescent : baseEnd_4423378 < baseStart_4423378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
