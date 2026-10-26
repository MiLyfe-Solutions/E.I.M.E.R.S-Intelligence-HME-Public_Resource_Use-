import V185TrunkScan20Chunk041

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_254855 : List Nat := [1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_254855 : Nat := 118140960795 + 254855 * 2 ^ 59
def prefixEnd_254855 : Nat := 4983230072969 + 3 ^ 40 * 254855 * 2
def baseEnd_254855 : Nat := 38774255467172033286059

theorem tailTrace_254855 : CollatzResearch.WordTrace tailWord_254855 prefixEnd_254855 38774255467172033286059 := by
  unfold tailWord_254855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295325491711335613846019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196883661140890409230679 9295325491711335613846019)
  ·
    refine ⟨13942988237567003420769029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9295325491711335613846019 13942988237567003420769029)
    ·
      refine ⟨2614310294543813141394193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13942988237567003420769029 2614310294543813141394193)
      ·
        refine ⟨1960732720907859856045645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2614310294543813141394193 1960732720907859856045645)
        ·
          refine ⟨735274770340447446017117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1960732720907859856045645 735274770340447446017117)
          ·
            refine ⟨275728038877667792256419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735274770340447446017117 275728038877667792256419)
            ·
              refine ⟨413592058316501688384629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275728038877667792256419 413592058316501688384629)
              ·
                refine ⟨38774255467172033286059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 413592058316501688384629 38774255467172033286059)
                ·
                  rfl

theorem cell20_254855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_254855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254855 prefixEnd_254855 := by exact prefixLift 254855
  have htrace : WordTrace (prefixWord ++ tailWord_254855) baseStart_254855 baseEnd_254855 := by
    simpa [prefixWord, tailWord_254855, baseEnd_254855] using wordTrace_append hprefix tailTrace_254855
  have hstable : (prefixWord ++ tailWord_254855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254855).length < 2 ^ (prefixWord ++ tailWord_254855).sum := by decide
  have hdescent : baseEnd_254855 < baseStart_254855 := by decide
  rcases family_descends (prefixWord ++ tailWord_254855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254869 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_254869 : Nat := 118140960795 + 254869 * 2 ^ 59
def prefixEnd_254869 : Nat := 4983230072969 + 3 ^ 40 * 254869 * 2
def baseEnd_254869 : Nat := 116329156382994273391453

theorem tailTrace_254869 : CollatzResearch.WordTrace tailWord_254869 prefixEnd_254869 116329156382994273391453 := by
  unfold tailWord_254869
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295836113660616004855661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6197224075773744003237107 9295836113660616004855661)
  ·
    refine ⟨3485938542622731001820873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9295836113660616004855661 3485938542622731001820873)
    ·
      refine ⟨2614453906967048251365655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3485938542622731001820873 2614453906967048251365655)
      ·
        refine ⟨3921680860450572377048483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614453906967048251365655 3921680860450572377048483)
        ·
          refine ⟨5882521290675858565572725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921680860450572377048483 5882521290675858565572725)
          ·
            refine ⟨551486371000861740522443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5882521290675858565572725 551486371000861740522443)
            ·
              refine ⟨827229556501292610783665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551486371000861740522443 827229556501292610783665)
              ·
                refine ⟨620422167375969458087749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827229556501292610783665 620422167375969458087749)
                ·
                  refine ⟨116329156382994273391453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620422167375969458087749 116329156382994273391453)
                  ·
                    rfl

theorem cell20_254869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_254869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254869 prefixEnd_254869 := by exact prefixLift 254869
  have htrace : WordTrace (prefixWord ++ tailWord_254869) baseStart_254869 baseEnd_254869 := by
    simpa [prefixWord, tailWord_254869, baseEnd_254869] using wordTrace_append hprefix tailTrace_254869
  have hstable : (prefixWord ++ tailWord_254869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254869).length < 2 ^ (prefixWord ++ tailWord_254869).sum := by decide
  have hdescent : baseEnd_254869 < baseStart_254869 := by decide
  rcases family_descends (prefixWord ++ tailWord_254869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254941 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 2]
def baseStart_254941 : Nat := 118140960795 + 254941 * 2 ^ 59
def prefixEnd_254941 : Nat := 4983230072969 + 3 ^ 40 * 254941 * 2
def baseEnd_254941 : Nat := 116362019144882022991159

theorem tailTrace_254941 : CollatzResearch.WordTrace tailWord_254941 prefixEnd_254941 116362019144882022991159 := by
  unfold tailWord_254941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298462169399772301476677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6198974779599848200984451 9298462169399772301476677)
  ·
    refine ⟨1743461656762457306526877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9298462169399772301476677 1743461656762457306526877)
    ·
      refine ⟨653798121285921489947579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1743461656762457306526877 653798121285921489947579)
      ·
        refine ⟨980697181928882234921369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653798121285921489947579 980697181928882234921369)
        ·
          refine ⟨735522886446661676191027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980697181928882234921369 735522886446661676191027)
          ·
            refine ⟨1103284329669992514286541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735522886446661676191027 1103284329669992514286541)
            ·
              refine ⟨413731623626247192857453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1103284329669992514286541 413731623626247192857453)
              ·
                refine ⟨155149358859842697321545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413731623626247192857453 155149358859842697321545)
                ·
                  refine ⟨116362019144882022991159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155149358859842697321545 116362019144882022991159)
                  ·
                    rfl

theorem cell20_254941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_254941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254941 prefixEnd_254941 := by exact prefixLift 254941
  have htrace : WordTrace (prefixWord ++ tailWord_254941) baseStart_254941 baseEnd_254941 := by
    simpa [prefixWord, tailWord_254941, baseEnd_254941] using wordTrace_append hprefix tailTrace_254941
  have hstable : (prefixWord ++ tailWord_254941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254941).length < 2 ^ (prefixWord ++ tailWord_254941).sum := by decide
  have hdescent : baseEnd_254941 < baseStart_254941 := by decide
  rcases family_descends (prefixWord ++ tailWord_254941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254958 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_254958 : Nat := 118140960795 + 254958 * 2 ^ 59
def prefixEnd_254958 : Nat := 4983230072969 + 3 ^ 40 * 254958 * 2
def baseEnd_254958 : Nat := 116369778408105519424423

theorem tailTrace_254958 : CollatzResearch.WordTrace tailWord_254958 prefixEnd_254958 116369778408105519424423 := by
  unfold tailWord_254958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162385276292273025605691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6199388140225456136563685 1162385276292273025605691)
  ·
    refine ⟨1743577914438409538408537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162385276292273025605691 1743577914438409538408537)
    ·
      refine ⟨1307683435828807153806403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743577914438409538408537 1307683435828807153806403)
      ·
        refine ⟨1961525153743210730709605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307683435828807153806403 1961525153743210730709605)
        ·
          refine ⟨367785966326852012008051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1961525153743210730709605 367785966326852012008051)
          ·
            refine ⟨551678949490278018012077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367785966326852012008051 551678949490278018012077)
            ·
              refine ⟨206879606058854256754529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551678949490278018012077 206879606058854256754529)
              ·
                refine ⟨155159704544140692565897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206879606058854256754529 155159704544140692565897)
                ·
                  refine ⟨116369778408105519424423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155159704544140692565897 116369778408105519424423)
                  ·
                    rfl

theorem cell20_254958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_254958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254958 prefixEnd_254958 := by exact prefixLift 254958
  have htrace : WordTrace (prefixWord ++ tailWord_254958) baseStart_254958 baseEnd_254958 := by
    simpa [prefixWord, tailWord_254958, baseEnd_254958] using wordTrace_append hprefix tailTrace_254958
  have hstable : (prefixWord ++ tailWord_254958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254958).length < 2 ^ (prefixWord ++ tailWord_254958).sum := by decide
  have hdescent : baseEnd_254958 < baseStart_254958 := by decide
  rcases family_descends (prefixWord ++ tailWord_254958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254959 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_254959 : Nat := 118140960795 + 254959 * 2 ^ 59
def prefixEnd_254959 : Nat := 4983230072969 + 3 ^ 40 * 254959 * 2
def baseEnd_254959 : Nat := 116370234835353960391085

theorem tailTrace_254959 : CollatzResearch.WordTrace tailWord_254959 prefixEnd_254959 116370234835353960391085 := by
  unfold tailWord_254959
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299118683334561375631931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6199412455556374250421287 9299118683334561375631931)
  ·
    refine ⟨13948678025001842063447897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9299118683334561375631931 13948678025001842063447897)
    ·
      refine ⟨10461508518751381547585923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13948678025001842063447897 10461508518751381547585923)
      ·
        refine ⟨15692262778127072321378885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10461508518751381547585923 15692262778127072321378885)
        ·
          refine ⟨2942299270898826060258541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15692262778127072321378885 2942299270898826060258541)
          ·
            refine ⟨1103362226587059772596953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2942299270898826060258541 1103362226587059772596953)
            ·
              refine ⟨827521669940294829447715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103362226587059772596953 827521669940294829447715)
              ·
                refine ⟨1241282504910442244171573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827521669940294829447715 1241282504910442244171573)
                ·
                  refine ⟨116370234835353960391085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1241282504910442244171573 116370234835353960391085)
                  ·
                    rfl

theorem cell20_254959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_254959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254959 prefixEnd_254959 := by exact prefixLift 254959
  have htrace : WordTrace (prefixWord ++ tailWord_254959) baseStart_254959 baseEnd_254959 := by
    simpa [prefixWord, tailWord_254959, baseEnd_254959] using wordTrace_append hprefix tailTrace_254959
  have hstable : (prefixWord ++ tailWord_254959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254959).length < 2 ^ (prefixWord ++ tailWord_254959).sum := by decide
  have hdescent : baseEnd_254959 < baseStart_254959 := by decide
  rcases family_descends (prefixWord ++ tailWord_254959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254964 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_254964 : Nat := 118140960795 + 254964 * 2 ^ 59
def prefixEnd_254964 : Nat := 4983230072969 + 3 ^ 40 * 254964 * 2
def baseEnd_254964 : Nat := 116372516971596165224399

theorem tailTrace_254964 : CollatzResearch.WordTrace tailWord_254964 prefixEnd_254964 116372516971596165224399 := by
  unfold tailWord_254964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649650524158223614781973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6199534032210964819709297 4649650524158223614781973)
  ·
    refine ⟨217952368319916731942905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4649650524158223614781973 217952368319916731942905)
    ·
      refine ⟨163464276239937548957179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217952368319916731942905 163464276239937548957179)
      ·
        refine ⟨245196414359906323435769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163464276239937548957179 245196414359906323435769)
        ·
          refine ⟨183897310769929742576827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245196414359906323435769 183897310769929742576827)
          ·
            refine ⟨275845966154894613865241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183897310769929742576827 275845966154894613865241)
            ·
              refine ⟨206884474616170960398931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275845966154894613865241 206884474616170960398931)
              ·
                refine ⟨310326711924256440598397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206884474616170960398931 310326711924256440598397)
                ·
                  refine ⟨116372516971596165224399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310326711924256440598397 116372516971596165224399)
                  ·
                    rfl

theorem cell20_254964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_254964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254964 prefixEnd_254964 := by exact prefixLift 254964
  have htrace : WordTrace (prefixWord ++ tailWord_254964) baseStart_254964 baseEnd_254964 := by
    simpa [prefixWord, tailWord_254964, baseEnd_254964] using wordTrace_append hprefix tailTrace_254964
  have hstable : (prefixWord ++ tailWord_254964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254964).length < 2 ^ (prefixWord ++ tailWord_254964).sum := by decide
  have hdescent : baseEnd_254964 < baseStart_254964 := by decide
  rcases family_descends (prefixWord ++ tailWord_254964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254990 : List Nat := [4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_254990 : Nat := 118140960795 + 254990 * 2 ^ 59
def prefixEnd_254990 : Nat := 4983230072969 + 3 ^ 40 * 254990 * 2
def baseEnd_254990 : Nat := 38794794693351876785875

theorem tailTrace_254990 : CollatzResearch.WordTrace tailWord_254990 prefixEnd_254990 38794794693351876785875 := by
  unfold tailWord_254990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162531168277781708751303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6200166230814835780006949 1162531168277781708751303)
  ·
    refine ⟨1743796752416672563126955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162531168277781708751303 1743796752416672563126955)
    ·
      refine ⟨2615695128625008844690433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743796752416672563126955 2615695128625008844690433)
      ·
        refine ⟨1961771346468756633517825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2615695128625008844690433 1961771346468756633517825)
        ·
          refine ⟨1471328509851567475138369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961771346468756633517825 1471328509851567475138369)
          ·
            refine ⟨1103496382388675606353777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471328509851567475138369 1103496382388675606353777)
            ·
              refine ⟨827622286791506704765333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103496382388675606353777 827622286791506704765333)
              ·
                refine ⟨38794794693351876785875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 827622286791506704765333 38794794693351876785875)
                ·
                  rfl

theorem cell20_254990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_254990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_254990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_254990 prefixEnd_254990 := by exact prefixLift 254990
  have htrace : WordTrace (prefixWord ++ tailWord_254990) baseStart_254990 baseEnd_254990 := by
    simpa [prefixWord, tailWord_254990, baseEnd_254990] using wordTrace_append hprefix tailTrace_254990
  have hstable : (prefixWord ++ tailWord_254990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254990).length < 2 ^ (prefixWord ++ tailWord_254990).sum := by decide
  have hdescent : baseEnd_254990 < baseStart_254990 := by decide
  rcases family_descends (prefixWord ++ tailWord_254990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255011 : List Nat := [1, 1, 1, 4, 3, 10]
def baseStart_255011 : Nat := 118140960795 + 255011 * 2 ^ 59
def prefixEnd_255011 : Nat := 4983230072969 + 3 ^ 40 * 255011 * 2
def baseEnd_255011 : Nat := 4310887742676773728057

theorem tailTrace_255011 : CollatzResearch.WordTrace tailWord_255011 prefixEnd_255011 4310887742676773728057 := by
  unfold tailWord_255011
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301015279146174256524887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6200676852764116171016591 9301015279146174256524887)
  ·
    refine ⟨13951522918719261384787331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9301015279146174256524887 13951522918719261384787331)
    ·
      refine ⟨20927284378078892077180997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13951522918719261384787331 20927284378078892077180997)
      ·
        refine ⟨3923865820889792264471437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20927284378078892077180997 3923865820889792264471437)
        ·
          refine ⟨1471449682833672099176789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3923865820889792264471437 1471449682833672099176789)
          ·
            refine ⟨4310887742676773728057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1471449682833672099176789 4310887742676773728057)
            ·
              rfl

theorem cell20_255011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 10].length) (baseStart_255011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255011 prefixEnd_255011 := by exact prefixLift 255011
  have htrace : WordTrace (prefixWord ++ tailWord_255011) baseStart_255011 baseEnd_255011 := by
    simpa [prefixWord, tailWord_255011, baseEnd_255011] using wordTrace_append hprefix tailTrace_255011
  have hstable : (prefixWord ++ tailWord_255011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255011).length < 2 ^ (prefixWord ++ tailWord_255011).sum := by decide
  have hdescent : baseEnd_255011 < baseStart_255011 := by decide
  rcases family_descends (prefixWord ++ tailWord_255011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255038 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_255038 : Nat := 118140960795 + 255038 * 2 ^ 59
def prefixEnd_255038 : Nat := 4983230072969 + 3 ^ 40 * 255038 * 2
def baseEnd_255038 : Nat := 116406292587980796757429

theorem tailTrace_255038 : CollatzResearch.WordTrace tailWord_255038 prefixEnd_255038 116406292587980796757429 := by
  unfold tailWord_255038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162750006256044733469721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6201333366698905245171845 1162750006256044733469721)
  ·
    refine ⟨872062504692033550102291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1162750006256044733469721 872062504692033550102291)
    ·
      refine ⟨1308093757038050325153437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872062504692033550102291 1308093757038050325153437)
      ·
        refine ⟨490535158889268871932539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1308093757038050325153437 490535158889268871932539)
        ·
          refine ⟨735802738333903307898809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490535158889268871932539 735802738333903307898809)
          ·
            refine ⟨551852053750427480924107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735802738333903307898809 551852053750427480924107)
            ·
              refine ⟨827778080625641221386161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551852053750427480924107 827778080625641221386161)
              ·
                refine ⟨620833560469230916039621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827778080625641221386161 620833560469230916039621)
                ·
                  refine ⟨116406292587980796757429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620833560469230916039621 116406292587980796757429)
                  ·
                    rfl

theorem cell20_255038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_255038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255038 prefixEnd_255038 := by exact prefixLift 255038
  have htrace : WordTrace (prefixWord ++ tailWord_255038) baseStart_255038 baseEnd_255038 := by
    simpa [prefixWord, tailWord_255038, baseEnd_255038] using wordTrace_append hprefix tailTrace_255038
  have hstable : (prefixWord ++ tailWord_255038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255038).length < 2 ^ (prefixWord ++ tailWord_255038).sum := by decide
  have hdescent : baseEnd_255038 < baseStart_255038 := by decide
  rcases family_descends (prefixWord ++ tailWord_255038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255059 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 2]
def baseStart_255059 : Nat := 118140960795 + 255059 * 2 ^ 59
def prefixEnd_255059 : Nat := 4983230072969 + 3 ^ 40 * 255059 * 2
def baseEnd_255059 : Nat := 116415877560198057057343

theorem tailTrace_255059 : CollatzResearch.WordTrace tailWord_255059 prefixEnd_255059 116415877560198057057343 := by
  unfold tailWord_255059
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302765982972278454272231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6201843988648185636181487 9302765982972278454272231)
  ·
    refine ⟨13954148974458417681408347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302765982972278454272231 13954148974458417681408347)
    ·
      refine ⟨20931223461687626522112521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13954148974458417681408347 20931223461687626522112521)
      ·
        refine ⟨15698417596265719891584391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20931223461687626522112521 15698417596265719891584391)
        ·
          refine ⟨23547626394398579837376587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15698417596265719891584391 23547626394398579837376587)
          ·
            refine ⟨35321439591597869756064881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23547626394398579837376587 35321439591597869756064881)
            ·
              refine ⟨26491079693698402317048661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35321439591597869756064881 26491079693698402317048661)
              ·
                refine ⟨155221170080264076076457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26491079693698402317048661 155221170080264076076457)
                ·
                  refine ⟨116415877560198057057343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155221170080264076076457 116415877560198057057343)
                  ·
                    rfl

theorem cell20_255059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2].length) (baseStart_255059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255059 prefixEnd_255059 := by exact prefixLift 255059
  have htrace : WordTrace (prefixWord ++ tailWord_255059) baseStart_255059 baseEnd_255059 := by
    simpa [prefixWord, tailWord_255059, baseEnd_255059] using wordTrace_append hprefix tailTrace_255059
  have hstable : (prefixWord ++ tailWord_255059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255059).length < 2 ^ (prefixWord ++ tailWord_255059).sum := by decide
  have hdescent : baseEnd_255059 < baseStart_255059 := by decide
  rcases family_descends (prefixWord ++ tailWord_255059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255062 : List Nat := [5, 2, 2, 1, 2, 1, 7]
def baseStart_255062 : Nat := 118140960795 + 255062 * 2 ^ 59
def prefixEnd_255062 : Nat := 4983230072969 + 3 ^ 40 * 255062 * 2
def baseEnd_255062 : Nat := 12935249649104819995259

theorem tailTrace_255062 : CollatzResearch.WordTrace tailWord_255062 prefixEnd_255062 12935249649104819995259 := by
  unfold tailWord_255062
  simp only [CollatzResearch.WordTrace]
  refine ⟨581429712622588122914465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6201916934640939977754293 581429712622588122914465)
  ·
    refine ⟨436072284466941092185849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 581429712622588122914465 436072284466941092185849)
    ·
      refine ⟨327054213350205819139387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436072284466941092185849 327054213350205819139387)
      ·
        refine ⟨490581320025308728709081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327054213350205819139387 490581320025308728709081)
        ·
          refine ⟨367935990018981546531811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490581320025308728709081 367935990018981546531811)
          ·
            refine ⟨551903985028472319797717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367935990018981546531811 551903985028472319797717)
            ·
              refine ⟨12935249649104819995259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 551903985028472319797717 12935249649104819995259)
              ·
                rfl

theorem cell20_255062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_255062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255062 prefixEnd_255062 := by exact prefixLift 255062
  have htrace : WordTrace (prefixWord ++ tailWord_255062) baseStart_255062 baseEnd_255062 := by
    simpa [prefixWord, tailWord_255062, baseEnd_255062] using wordTrace_append hprefix tailTrace_255062
  have hstable : (prefixWord ++ tailWord_255062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255062).length < 2 ^ (prefixWord ++ tailWord_255062).sum := by decide
  have hdescent : baseEnd_255062 < baseStart_255062 := by decide
  rcases family_descends (prefixWord ++ tailWord_255062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255069 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_255069 : Nat := 118140960795 + 255069 * 2 ^ 59
def prefixEnd_255069 : Nat := 4983230072969 + 3 ^ 40 * 255069 * 2
def baseEnd_255069 : Nat := 116420441832682466723969

theorem tailTrace_255069 : CollatzResearch.WordTrace tailWord_255069 prefixEnd_255069 116420441832682466723969 := by
  unfold tailWord_255069
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303130712936050162136261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6202087141957366774757507 9303130712936050162136261)
  ·
    refine ⟨1744337008675509405400549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9303130712936050162136261 1744337008675509405400549)
    ·
      refine ⟨327063189126658013512603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1744337008675509405400549 327063189126658013512603)
      ·
        refine ⟨490594783689987020268905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327063189126658013512603 490594783689987020268905)
        ·
          refine ⟨367946087767490265201679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490594783689987020268905 367946087767490265201679)
          ·
            refine ⟨551919131651235397802519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367946087767490265201679 551919131651235397802519)
            ·
              refine ⟨827878697476853096703779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551919131651235397802519 827878697476853096703779)
              ·
                refine ⟨1241818046215279645055669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827878697476853096703779 1241818046215279645055669)
                ·
                  refine ⟨116420441832682466723969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1241818046215279645055669 116420441832682466723969)
                  ·
                    rfl

theorem cell20_255069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_255069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255069 prefixEnd_255069 := by exact prefixLift 255069
  have htrace : WordTrace (prefixWord ++ tailWord_255069) baseStart_255069 baseEnd_255069 := by
    simpa [prefixWord, tailWord_255069, baseEnd_255069] using wordTrace_append hprefix tailTrace_255069
  have hstable : (prefixWord ++ tailWord_255069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255069).length < 2 ^ (prefixWord ++ tailWord_255069).sum := by decide
  have hdescent : baseEnd_255069 < baseStart_255069 := by decide
  rcases family_descends (prefixWord ++ tailWord_255069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255087 : List Nat := [1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_255087 : Nat := 118140960795 + 255087 * 2 ^ 59
def prefixEnd_255087 : Nat := 4983230072969 + 3 ^ 40 * 255087 * 2
def baseEnd_255087 : Nat := 38809552507718134707965

theorem tailTrace_255087 : CollatzResearch.WordTrace tailWord_255087 prefixEnd_255087 38809552507718134707965 := by
  unfold tailWord_255087
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303787226870839236291515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6202524817913892824194343 9303787226870839236291515)
  ·
    refine ⟨13955680840306258854437273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303787226870839236291515 13955680840306258854437273)
    ·
      refine ⟨10466760630229694140827955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13955680840306258854437273 10466760630229694140827955)
      ·
        refine ⟨15700140945344541211241933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10466760630229694140827955 15700140945344541211241933)
        ·
          refine ⟨5887552854504202954215725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15700140945344541211241933 5887552854504202954215725)
          ·
            refine ⟨2207832320439076107830897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5887552854504202954215725 2207832320439076107830897)
            ·
              refine ⟨1655874240329307080873173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207832320439076107830897 1655874240329307080873173)
              ·
                refine ⟨38809552507718134707965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1655874240329307080873173 38809552507718134707965)
                ·
                  rfl

theorem cell20_255087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_255087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255087 prefixEnd_255087 := by exact prefixLift 255087
  have htrace : WordTrace (prefixWord ++ tailWord_255087) baseStart_255087 baseEnd_255087 := by
    simpa [prefixWord, tailWord_255087, baseEnd_255087] using wordTrace_append hprefix tailTrace_255087
  have hstable : (prefixWord ++ tailWord_255087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255087).length < 2 ^ (prefixWord ++ tailWord_255087).sum := by decide
  have hdescent : baseEnd_255087 < baseStart_255087 := by decide
  rcases family_descends (prefixWord ++ tailWord_255087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255104 : List Nat := [2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_255104 : Nat := 118140960795 + 255104 * 2 ^ 59
def prefixEnd_255104 : Nat := 4983230072969 + 3 ^ 40 * 255104 * 2
def baseEnd_255104 : Nat := 38812138928792633519053

theorem tailTrace_255104 : CollatzResearch.WordTrace tailWord_255104 prefixEnd_255104 38812138928792633519053 := by
  unfold tailWord_255104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652203633904625569830183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6202938178539500759773577 4652203633904625569830183)
  ·
    refine ⟨6978305450856938354745275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4652203633904625569830183 6978305450856938354745275)
    ·
      refine ⟨10467458176285407532117913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978305450856938354745275 10467458176285407532117913)
      ·
        refine ⟨7850593632214055649088435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10467458176285407532117913 7850593632214055649088435)
        ·
          refine ⟨11775890448321083473632653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7850593632214055649088435 11775890448321083473632653)
          ·
            refine ⟨4415958918120406302612245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11775890448321083473632653 4415958918120406302612245)
            ·
              refine ⟨206998074286894045434949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4415958918120406302612245 206998074286894045434949)
              ·
                refine ⟨38812138928792633519053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206998074286894045434949 38812138928792633519053)
                ·
                  rfl

theorem cell20_255104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_255104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255104 prefixEnd_255104 := by exact prefixLift 255104
  have htrace : WordTrace (prefixWord ++ tailWord_255104) baseStart_255104 baseEnd_255104 := by
    simpa [prefixWord, tailWord_255104, baseEnd_255104] using wordTrace_append hprefix tailTrace_255104
  have hstable : (prefixWord ++ tailWord_255104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255104).length < 2 ^ (prefixWord ++ tailWord_255104).sum := by decide
  have hdescent : baseEnd_255104 < baseStart_255104 := by decide
  rcases family_descends (prefixWord ++ tailWord_255104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255173 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 2]
def baseStart_255173 : Nat := 118140960795 + 255173 * 2 ^ 59
def prefixEnd_255173 : Nat := 4983230072969 + 3 ^ 40 * 255173 * 2
def baseEnd_255173 : Nat := 116467910266520327256877

theorem tailTrace_255173 : CollatzResearch.WordTrace tailWord_255173 prefixEnd_255173 116467910266520327256877 := by
  unfold tailWord_255173
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306923904559275923922173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6204615936372850615948115 9306923904559275923922173)
  ·
    refine ⟨3490096464209728471470815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9306923904559275923922173 3490096464209728471470815)
    ·
      refine ⟨5235144696314592707206223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490096464209728471470815 5235144696314592707206223)
      ·
        refine ⟨7852717044471889060809335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235144696314592707206223 7852717044471889060809335)
        ·
          refine ⟨11779075566707833591214003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852717044471889060809335 11779075566707833591214003)
          ·
            refine ⟨17668613350061750386821005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779075566707833591214003 17668613350061750386821005)
            ·
              refine ⟨6625730006273156395057877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17668613350061750386821005 6625730006273156395057877)
              ·
                refine ⟨155290547022027103009169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6625730006273156395057877 155290547022027103009169)
                ·
                  refine ⟨116467910266520327256877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155290547022027103009169 116467910266520327256877)
                  ·
                    rfl

theorem cell20_255173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_255173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255173 prefixEnd_255173 := by exact prefixLift 255173
  have htrace : WordTrace (prefixWord ++ tailWord_255173) baseStart_255173 baseEnd_255173 := by
    simpa [prefixWord, tailWord_255173, baseEnd_255173] using wordTrace_append hprefix tailTrace_255173
  have hstable : (prefixWord ++ tailWord_255173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255173).length < 2 ^ (prefixWord ++ tailWord_255173).sum := by decide
  have hdescent : baseEnd_255173 < baseStart_255173 := by decide
  rcases family_descends (prefixWord ++ tailWord_255173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255194 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_255194 : Nat := 118140960795 + 255194 * 2 ^ 59
def prefixEnd_255194 : Nat := 4983230072969 + 3 ^ 40 * 255194 * 2
def baseEnd_255194 : Nat := 116477495238737587556791

theorem tailTrace_255194 : CollatzResearch.WordTrace tailWord_255194 prefixEnd_255194 116477495238737587556791 := by
  unfold tailWord_255194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326922459370799127609159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6205126558322131006957757 2326922459370799127609159)
  ·
    refine ⟨3490383689056198691413739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326922459370799127609159 3490383689056198691413739)
    ·
      refine ⟨5235575533584298037120609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490383689056198691413739 5235575533584298037120609)
      ·
        refine ⟨3926681650188223527840457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5235575533584298037120609 3926681650188223527840457)
        ·
          refine ⟨2945011237641167645880343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3926681650188223527840457 2945011237641167645880343)
          ·
            refine ⟨4417516856461751468820515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945011237641167645880343 4417516856461751468820515)
            ·
              refine ⟨6626275284692627203230773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417516856461751468820515 6626275284692627203230773)
              ·
                refine ⟨621213307939933800302885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6626275284692627203230773 621213307939933800302885)
                ·
                  refine ⟨116477495238737587556791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621213307939933800302885 116477495238737587556791)
                  ·
                    rfl

theorem cell20_255194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_255194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255194 prefixEnd_255194 := by exact prefixLift 255194
  have htrace : WordTrace (prefixWord ++ tailWord_255194) baseStart_255194 baseEnd_255194 := by
    simpa [prefixWord, tailWord_255194, baseEnd_255194] using wordTrace_append hprefix tailTrace_255194
  have hstable : (prefixWord ++ tailWord_255194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255194).length < 2 ^ (prefixWord ++ tailWord_255194).sum := by decide
  have hdescent : baseEnd_255194 < baseStart_255194 := by decide
  rcases family_descends (prefixWord ++ tailWord_255194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255249 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 2]
def baseStart_255249 : Nat := 118140960795 + 255249 * 2 ^ 59
def prefixEnd_255249 : Nat := 4983230072969 + 3 ^ 40 * 255249 * 2
def baseEnd_255249 : Nat := 116502598737401840723233

theorem tailTrace_255249 : CollatzResearch.WordTrace tailWord_255249 prefixEnd_255249 116502598737401840723233 := by
  unfold tailWord_255249
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309695852283940903688801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6206463901522627269125867 9309695852283940903688801)
  ·
    refine ⟨6982271889212955677766601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9309695852283940903688801 6982271889212955677766601)
    ·
      refine ⟨5236703916909716758324951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6982271889212955677766601 5236703916909716758324951)
      ·
        refine ⟨7855055875364575137487427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236703916909716758324951 7855055875364575137487427)
        ·
          refine ⟨11782583813046862706231141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7855055875364575137487427 11782583813046862706231141)
          ·
            refine ⟨2209234464946286757418339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11782583813046862706231141 2209234464946286757418339)
            ·
              refine ⟨3313851697419430136127509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209234464946286757418339 3313851697419430136127509)
              ·
                refine ⟨155336798316535787630977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3313851697419430136127509 155336798316535787630977)
                ·
                  refine ⟨116502598737401840723233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155336798316535787630977 116502598737401840723233)
                  ·
                    rfl

theorem cell20_255249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_255249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255249 prefixEnd_255249 := by exact prefixLift 255249
  have htrace : WordTrace (prefixWord ++ tailWord_255249) baseStart_255249 baseEnd_255249 := by
    simpa [prefixWord, tailWord_255249, baseEnd_255249] using wordTrace_append hprefix tailTrace_255249
  have hstable : (prefixWord ++ tailWord_255249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255249).length < 2 ^ (prefixWord ++ tailWord_255249).sum := by decide
  have hdescent : baseEnd_255249 < baseStart_255249 := by decide
  rcases family_descends (prefixWord ++ tailWord_255249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255300 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_255300 : Nat := 118140960795 + 255300 * 2 ^ 59
def prefixEnd_255300 : Nat := 4983230072969 + 3 ^ 40 * 255300 * 2
def baseEnd_255300 : Nat := 116525876527072330023025

theorem tailTrace_255300 : CollatzResearch.WordTrace tailWord_255300 prefixEnd_255300 116525876527072330023025 := by
  unfold tailWord_255300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655777987549588306897677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6207703983399451075863569 4655777987549588306897677)
  ·
    refine ⟨1745916745331095615086629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4655777987549588306897677 1745916745331095615086629)
    ·
      refine ⟨327359389749580427828743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1745916745331095615086629 327359389749580427828743)
      ·
        refine ⟨491039084624370641743115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327359389749580427828743 491039084624370641743115)
        ·
          refine ⟨736558626936555962614673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491039084624370641743115 736558626936555962614673)
          ·
            refine ⟨552418970202416971961005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736558626936555962614673 552418970202416971961005)
            ·
              refine ⟨207157113825906364485377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552418970202416971961005 207157113825906364485377)
              ·
                refine ⟨155367835369429773364033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207157113825906364485377 155367835369429773364033)
                ·
                  refine ⟨116525876527072330023025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155367835369429773364033 116525876527072330023025)
                  ·
                    rfl

theorem cell20_255300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_255300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255300 prefixEnd_255300 := by exact prefixLift 255300
  have htrace : WordTrace (prefixWord ++ tailWord_255300) baseStart_255300 baseEnd_255300 := by
    simpa [prefixWord, tailWord_255300, baseEnd_255300] using wordTrace_append hprefix tailTrace_255300
  have hstable : (prefixWord ++ tailWord_255300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255300).length < 2 ^ (prefixWord ++ tailWord_255300).sum := by decide
  have hdescent : baseEnd_255300 < baseStart_255300 := by decide
  rcases family_descends (prefixWord ++ tailWord_255300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255315 : List Nat := [1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_255315 : Nat := 118140960795 + 255315 * 2 ^ 59
def prefixEnd_255315 : Nat := 4983230072969 + 3 ^ 40 * 255315 * 2
def baseEnd_255315 : Nat := 38844240978599648174321

theorem tailTrace_255315 : CollatzResearch.WordTrace tailWord_255315 prefixEnd_255315 38844240978599648174321 := by
  unfold tailWord_255315
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312103070044834175591399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6208068713363222783727599 9312103070044834175591399)
  ·
    refine ⟨13968154605067251263387099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9312103070044834175591399 13968154605067251263387099)
    ·
      refine ⟨20952231907600876895080649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968154605067251263387099 20952231907600876895080649)
      ·
        refine ⟨15714173930700657671310487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20952231907600876895080649 15714173930700657671310487)
        ·
          refine ⟨23571260896050986506965731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714173930700657671310487 23571260896050986506965731)
          ·
            refine ⟨35356891344076479760448597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571260896050986506965731 35356891344076479760448597)
            ·
              refine ⟨414338570438396247192757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 35356891344076479760448597 414338570438396247192757)
              ·
                refine ⟨38844240978599648174321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414338570438396247192757 38844240978599648174321)
                ·
                  rfl

theorem cell20_255315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_255315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255315 prefixEnd_255315 := by exact prefixLift 255315
  have htrace : WordTrace (prefixWord ++ tailWord_255315) baseStart_255315 baseEnd_255315 := by
    simpa [prefixWord, tailWord_255315, baseEnd_255315] using wordTrace_append hprefix tailTrace_255315
  have hstable : (prefixWord ++ tailWord_255315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255315).length < 2 ^ (prefixWord ++ tailWord_255315).sum := by decide
  have hdescent : baseEnd_255315 < baseStart_255315 := by decide
  rcases family_descends (prefixWord ++ tailWord_255315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255360 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_255360 : Nat := 118140960795 + 255360 * 2 ^ 59
def prefixEnd_255360 : Nat := 4983230072969 + 3 ^ 40 * 255360 * 2
def baseEnd_255360 : Nat := 116553262161978788022779

theorem tailTrace_255360 : CollatzResearch.WordTrace tailWord_255360 prefixEnd_255360 116553262161978788022779 := by
  unfold tailWord_255360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656872177440903430489767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6209162903254537907319689 4656872177440903430489767)
  ·
    refine ⟨6985308266161355145734651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656872177440903430489767 6985308266161355145734651)
    ·
      refine ⟨10477962399242032718601977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6985308266161355145734651 10477962399242032718601977)
      ·
        refine ⟨7858471799431524538951483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10477962399242032718601977 7858471799431524538951483)
        ·
          refine ⟨11787707699147286808427225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858471799431524538951483 11787707699147286808427225)
          ·
            refine ⟨8840780774360465106320419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787707699147286808427225 8840780774360465106320419)
            ·
              refine ⟨13261171161540697659480629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840780774360465106320419 13261171161540697659480629)
              ·
                refine ⟨1243234796394440405576309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13261171161540697659480629 1243234796394440405576309)
                ·
                  refine ⟨116553262161978788022779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1243234796394440405576309 116553262161978788022779)
                  ·
                    rfl

theorem cell20_255360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_255360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255360 prefixEnd_255360 := by exact prefixLift 255360
  have htrace : WordTrace (prefixWord ++ tailWord_255360) baseStart_255360 baseEnd_255360 := by
    simpa [prefixWord, tailWord_255360, baseEnd_255360] using wordTrace_append hprefix tailTrace_255360
  have hstable : (prefixWord ++ tailWord_255360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255360).length < 2 ^ (prefixWord ++ tailWord_255360).sum := by decide
  have hdescent : baseEnd_255360 < baseStart_255360 := by decide
  rcases family_descends (prefixWord ++ tailWord_255360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255432 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_255432 : Nat := 118140960795 + 255432 * 2 ^ 59
def prefixEnd_255432 : Nat := 4983230072969 + 3 ^ 40 * 255432 * 2
def baseEnd_255432 : Nat := 116586124923866537622485

theorem tailTrace_255432 : CollatzResearch.WordTrace tailWord_255432 prefixEnd_255432 116586124923866537622485 := by
  unfold tailWord_255432
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658185205310481578800275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6210913607080642105067033 4658185205310481578800275)
  ·
    refine ⟨6987277807965722368200413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4658185205310481578800275 6987277807965722368200413)
    ·
      refine ⟨2620229177987145888075155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6987277807965722368200413 2620229177987145888075155)
      ·
        refine ⟨3930343766980718832112733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620229177987145888075155 3930343766980718832112733)
        ·
          refine ⟨1473878912617769562042275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3930343766980718832112733 1473878912617769562042275)
          ·
            refine ⟨2210818368926654343063413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473878912617769562042275 2210818368926654343063413)
            ·
              refine ⟨207264222086873844662195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2210818368926654343063413 207264222086873844662195)
              ·
                refine ⟨310896333130310766993293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207264222086873844662195 310896333130310766993293)
                ·
                  refine ⟨116586124923866537622485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310896333130310766993293 116586124923866537622485)
                  ·
                    rfl

theorem cell20_255432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_255432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255432 prefixEnd_255432 := by exact prefixLift 255432
  have htrace : WordTrace (prefixWord ++ tailWord_255432) baseStart_255432 baseEnd_255432 := by
    simpa [prefixWord, tailWord_255432, baseEnd_255432] using wordTrace_append hprefix tailTrace_255432
  have hstable : (prefixWord ++ tailWord_255432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255432).length < 2 ^ (prefixWord ++ tailWord_255432).sum := by decide
  have hdescent : baseEnd_255432 < baseStart_255432 := by decide
  rcases family_descends (prefixWord ++ tailWord_255432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255453 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_255453 : Nat := 118140960795 + 255453 * 2 ^ 59
def prefixEnd_255453 : Nat := 4983230072969 + 3 ^ 40 * 255453 * 2
def baseEnd_255453 : Nat := 116595709896083797922399

theorem tailTrace_255453 : CollatzResearch.WordTrace tailWord_255453 prefixEnd_255453 116595709896083797922399 := by
  unfold tailWord_255453
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317136343544883744115013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6211424229029922496076675 9317136343544883744115013)
  ·
    refine ⟨1746963064414665702021565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9317136343544883744115013 1746963064414665702021565)
    ·
      refine ⟨655111149155499638258087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1746963064414665702021565 655111149155499638258087)
      ·
        refine ⟨982666723733249457387131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655111149155499638258087 982666723733249457387131)
        ·
          refine ⟨1474000085599874186080697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982666723733249457387131 1474000085599874186080697)
          ·
            refine ⟨1105500064199905639560523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474000085599874186080697 1105500064199905639560523)
            ·
              refine ⟨1658250096299858459340785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105500064199905639560523 1658250096299858459340785)
              ·
                refine ⟨1243687572224893844505589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658250096299858459340785 1243687572224893844505589)
                ·
                  refine ⟨116595709896083797922399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1243687572224893844505589 116595709896083797922399)
                  ·
                    rfl

theorem cell20_255453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_255453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255453 prefixEnd_255453 := by exact prefixLift 255453
  have htrace : WordTrace (prefixWord ++ tailWord_255453) baseStart_255453 baseEnd_255453 := by
    simpa [prefixWord, tailWord_255453, baseEnd_255453] using wordTrace_append hprefix tailTrace_255453
  have hstable : (prefixWord ++ tailWord_255453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255453).length < 2 ^ (prefixWord ++ tailWord_255453).sum := by decide
  have hdescent : baseEnd_255453 < baseStart_255453 := by decide
  rcases family_descends (prefixWord ++ tailWord_255453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255518 : List Nat := [4, 3, 3, 1, 1, 8]
def baseStart_255518 : Nat := 118140960795 + 255518 * 2 ^ 59
def prefixEnd_255518 : Nat := 4983230072969 + 3 ^ 40 * 255518 * 2
def baseEnd_255518 : Nat := 4319458432119720768721

theorem tailTrace_255518 : CollatzResearch.WordTrace tailWord_255518 prefixEnd_255518 4319458432119720768721 := by
  unfold tailWord_255518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164938386038674980653901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6213004725539599896820805 1164938386038674980653901)
  ·
    refine ⟨436851894764503117745213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1164938386038674980653901 436851894764503117745213)
    ·
      refine ⟨163819460536688669154455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436851894764503117745213 163819460536688669154455)
      ·
        refine ⟨245729190805033003731683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163819460536688669154455 245729190805033003731683)
        ·
          refine ⟨368593786207549505597525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245729190805033003731683 368593786207549505597525)
          ·
            refine ⟨4319458432119720768721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 368593786207549505597525 4319458432119720768721)
            ·
              rfl

theorem cell20_255518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 8].length) (baseStart_255518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255518 prefixEnd_255518 := by exact prefixLift 255518
  have htrace : WordTrace (prefixWord ++ tailWord_255518) baseStart_255518 baseEnd_255518 := by
    simpa [prefixWord, tailWord_255518, baseEnd_255518] using wordTrace_append hprefix tailTrace_255518
  have hstable : (prefixWord ++ tailWord_255518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255518).length < 2 ^ (prefixWord ++ tailWord_255518).sum := by decide
  have hdescent : baseEnd_255518 < baseStart_255518 := by decide
  rcases family_descends (prefixWord ++ tailWord_255518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255528 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_255528 : Nat := 118140960795 + 255528 * 2 ^ 59
def prefixEnd_255528 : Nat := 4983230072969 + 3 ^ 40 * 255528 * 2
def baseEnd_255528 : Nat := 116629941939716870422093

theorem tailTrace_255528 : CollatzResearch.WordTrace tailWord_255528 prefixEnd_255528 116629941939716870422093 := by
  unfold tailWord_255528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659935909136585776547619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6213247878848781035396825 4659935909136585776547619)
  ·
    refine ⟨6989903863704878664821429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4659935909136585776547619 6989903863704878664821429)
    ·
      refine ⟨655303487222332374827009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6989903863704878664821429 655303487222332374827009)
      ·
        refine ⟨491477615416749281120257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655303487222332374827009 491477615416749281120257)
        ·
          refine ⟨368608211562561960840193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491477615416749281120257 368608211562561960840193)
          ·
            refine ⟨276456158671921470630145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368608211562561960840193 276456158671921470630145)
            ·
              refine ⟨207342119003941102972609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276456158671921470630145 207342119003941102972609)
              ·
                refine ⟨155506589252955827229457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207342119003941102972609 155506589252955827229457)
                ·
                  refine ⟨116629941939716870422093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155506589252955827229457 116629941939716870422093)
                  ·
                    rfl

theorem cell20_255528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_255528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255528 prefixEnd_255528 := by exact prefixLift 255528
  have htrace : WordTrace (prefixWord ++ tailWord_255528) baseStart_255528 baseEnd_255528 := by
    simpa [prefixWord, tailWord_255528, baseEnd_255528] using wordTrace_append hprefix tailTrace_255528
  have hstable : (prefixWord ++ tailWord_255528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255528).length < 2 ^ (prefixWord ++ tailWord_255528).sum := by decide
  have hdescent : baseEnd_255528 < baseStart_255528 := by decide
  rcases family_descends (prefixWord ++ tailWord_255528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255543 : List Nat := [1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_255543 : Nat := 118140960795 + 255543 * 2 ^ 59
def prefixEnd_255543 : Nat := 4983230072969 + 3 ^ 40 * 255543 * 2
def baseEnd_255543 : Nat := 38878929449481161640677

theorem tailTrace_255543 : CollatzResearch.WordTrace tailWord_255543 prefixEnd_255543 38878929449481161640677 := by
  unfold tailWord_255543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320418913218829114891283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6213612608812552743260855 9320418913218829114891283)
  ·
    refine ⟨13980628369828243672336925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9320418913218829114891283 13980628369828243672336925)
    ·
      refine ⟨5242735638685591377126347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13980628369828243672336925 5242735638685591377126347)
      ·
        refine ⟨7864103458028387065689521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242735638685591377126347 7864103458028387065689521)
        ·
          refine ⟨5898077593521290299267141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7864103458028387065689521 5898077593521290299267141)
          ·
            refine ⟨1105889548785241931112589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5898077593521290299267141 1105889548785241931112589)
            ·
              refine ⟨414708580794465724167221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105889548785241931112589 414708580794465724167221)
              ·
                refine ⟨38878929449481161640677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414708580794465724167221 38878929449481161640677)
                ·
                  rfl

theorem cell20_255543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_255543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255543 prefixEnd_255543 := by exact prefixLift 255543
  have htrace : WordTrace (prefixWord ++ tailWord_255543) baseStart_255543 baseEnd_255543 := by
    simpa [prefixWord, tailWord_255543, baseEnd_255543] using wordTrace_append hprefix tailTrace_255543
  have hstable : (prefixWord ++ tailWord_255543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255543).length < 2 ^ (prefixWord ++ tailWord_255543).sum := by decide
  have hdescent : baseEnd_255543 < baseStart_255543 := by decide
  rcases family_descends (prefixWord ++ tailWord_255543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255570 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_255570 : Nat := 118140960795 + 255570 * 2 ^ 59
def prefixEnd_255570 : Nat := 4983230072969 + 3 ^ 40 * 255570 * 2
def baseEnd_255570 : Nat := 116649111884151391021921

theorem tailTrace_255570 : CollatzResearch.WordTrace tailWord_255570 prefixEnd_255570 116649111884151391021921 := by
  unfold tailWord_255570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330350921030253181531041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6214269122747341817416109 2330350921030253181531041)
  ·
    refine ⟨1747763190772689886148281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330350921030253181531041 1747763190772689886148281)
    ·
      refine ⟨1310822393079517414611211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1747763190772689886148281 1310822393079517414611211)
      ·
        refine ⟨1966233589619276121916817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310822393079517414611211 1966233589619276121916817)
        ·
          refine ⟨1474675192214457091437613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966233589619276121916817 1474675192214457091437613)
          ·
            refine ⟨553003197080421409289105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1474675192214457091437613 553003197080421409289105)
            ·
              refine ⟨414752397810316056966829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553003197080421409289105 414752397810316056966829)
              ·
                refine ⟨155532149178868521362561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414752397810316056966829 155532149178868521362561)
                ·
                  refine ⟨116649111884151391021921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155532149178868521362561 116649111884151391021921)
                  ·
                    rfl

theorem cell20_255570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_255570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255570 prefixEnd_255570 := by exact prefixLift 255570
  have htrace : WordTrace (prefixWord ++ tailWord_255570) baseStart_255570 baseEnd_255570 := by
    simpa [prefixWord, tailWord_255570, baseEnd_255570] using wordTrace_append hprefix tailTrace_255570
  have hstable : (prefixWord ++ tailWord_255570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255570).length < 2 ^ (prefixWord ++ tailWord_255570).sum := by decide
  have hdescent : baseEnd_255570 < baseStart_255570 := by decide
  rcases family_descends (prefixWord ++ tailWord_255570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255591 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 2]
def baseStart_255591 : Nat := 118140960795 + 255591 * 2 ^ 59
def prefixEnd_255591 : Nat := 4983230072969 + 3 ^ 40 * 255591 * 2
def baseEnd_255591 : Nat := 116658696856368651321835

theorem tailTrace_255591 : CollatzResearch.WordTrace tailWord_255591 prefixEnd_255591 116658696856368651321835 := by
  unfold tailWord_255591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9322169617044933312638627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6214779744696622208425751 9322169617044933312638627)
  ·
    refine ⟨13983254425567399968957941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9322169617044933312638627 13983254425567399968957941)
    ·
      refine ⟨1310930102396943747089807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13983254425567399968957941 1310930102396943747089807)
      ·
        refine ⟨1966395153595415620634711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310930102396943747089807 1966395153595415620634711)
        ·
          refine ⟨2949592730393123430952067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966395153595415620634711 2949592730393123430952067)
          ·
            refine ⟨4424389095589685146428101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949592730393123430952067 4424389095589685146428101)
            ·
              refine ⟨829572955423065964955269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4424389095589685146428101 829572955423065964955269)
              ·
                refine ⟨155544929141824868429113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829572955423065964955269 155544929141824868429113)
                ·
                  refine ⟨116658696856368651321835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155544929141824868429113 116658696856368651321835)
                  ·
                    rfl

theorem cell20_255591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 2].length) (baseStart_255591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255591 prefixEnd_255591 := by exact prefixLift 255591
  have htrace : WordTrace (prefixWord ++ tailWord_255591) baseStart_255591 baseEnd_255591 := by
    simpa [prefixWord, tailWord_255591, baseEnd_255591] using wordTrace_append hprefix tailTrace_255591
  have hstable : (prefixWord ++ tailWord_255591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255591).length < 2 ^ (prefixWord ++ tailWord_255591).sum := by decide
  have hdescent : baseEnd_255591 < baseStart_255591 := by decide
  rcases family_descends (prefixWord ++ tailWord_255591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255646 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_255646 : Nat := 118140960795 + 255646 * 2 ^ 59
def prefixEnd_255646 : Nat := 4983230072969 + 3 ^ 40 * 255646 * 2
def baseEnd_255646 : Nat := 116683800355032904488277

theorem tailTrace_255646 : CollatzResearch.WordTrace tailWord_255646 prefixEnd_255646 116683800355032904488277 := by
  unfold tailWord_255646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165521953980709713236349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6216117087897118470593861 1165521953980709713236349)
  ·
    refine ⟨437070732742766142463631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1165521953980709713236349 437070732742766142463631)
    ·
      refine ⟨655606099114149213695447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437070732742766142463631 655606099114149213695447)
      ·
        refine ⟨983409148671223820543171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655606099114149213695447 983409148671223820543171)
        ·
          refine ⟨1475113723006835730814757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983409148671223820543171 1475113723006835730814757)
          ·
            refine ⟨276583823063781699527767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1475113723006835730814757 276583823063781699527767)
            ·
              refine ⟨414875734595672549291651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276583823063781699527767 414875734595672549291651)
              ·
                refine ⟨622313601893508823937477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414875734595672549291651 622313601893508823937477)
                ·
                  refine ⟨116683800355032904488277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622313601893508823937477 116683800355032904488277)
                  ·
                    rfl

theorem cell20_255646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_255646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255646 prefixEnd_255646 := by exact prefixLift 255646
  have htrace : WordTrace (prefixWord ++ tailWord_255646) baseStart_255646 baseEnd_255646 := by
    simpa [prefixWord, tailWord_255646, baseEnd_255646] using wordTrace_append hprefix tailTrace_255646
  have hstable : (prefixWord ++ tailWord_255646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255646).length < 2 ^ (prefixWord ++ tailWord_255646).sum := by decide
  have hdescent : baseEnd_255646 < baseStart_255646 := by decide
  rcases family_descends (prefixWord ++ tailWord_255646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255656 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_255656 : Nat := 118140960795 + 255656 * 2 ^ 59
def prefixEnd_255656 : Nat := 4983230072969 + 3 ^ 40 * 255656 * 2
def baseEnd_255656 : Nat := 116688364627517314154903

theorem tailTrace_255656 : CollatzResearch.WordTrace tailWord_255656 prefixEnd_255656 116688364627517314154903 := by
  unfold tailWord_255656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662270180904724706877411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6216360241206299609169881 4662270180904724706877411)
  ·
    refine ⟨6993405271357087060316117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662270180904724706877411 6993405271357087060316117)
    ·
      refine ⟨163907936047431727976159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6993405271357087060316117 163907936047431727976159)
      ·
        refine ⟨245861904071147591964239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163907936047431727976159 245861904071147591964239)
        ·
          refine ⟨368792856106721387946359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245861904071147591964239 368792856106721387946359)
          ·
            refine ⟨553189284160082081919539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368792856106721387946359 553189284160082081919539)
            ·
              refine ⟨829783926240123122879309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553189284160082081919539 829783926240123122879309)
              ·
                refine ⟨311168972340046171079741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829783926240123122879309 311168972340046171079741)
                ·
                  refine ⟨116688364627517314154903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311168972340046171079741 116688364627517314154903)
                  ·
                    rfl

theorem cell20_255656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_255656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255656 prefixEnd_255656 := by exact prefixLift 255656
  have htrace : WordTrace (prefixWord ++ tailWord_255656) baseStart_255656 baseEnd_255656 := by
    simpa [prefixWord, tailWord_255656, baseEnd_255656] using wordTrace_append hprefix tailTrace_255656
  have hstable : (prefixWord ++ tailWord_255656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255656).length < 2 ^ (prefixWord ++ tailWord_255656).sum := by decide
  have hdescent : baseEnd_255656 < baseStart_255656 := by decide
  rcases family_descends (prefixWord ++ tailWord_255656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255698 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_255698 : Nat := 118140960795 + 255698 * 2 ^ 59
def prefixEnd_255698 : Nat := 4983230072969 + 3 ^ 40 * 255698 * 2
def baseEnd_255698 : Nat := 116707534571951834754731

theorem tailTrace_255698 : CollatzResearch.WordTrace tailWord_255698 prefixEnd_255698 116707534571951834754731 := by
  unfold tailWord_255698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331518056914322646695937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6217381485104860391189165 2331518056914322646695937)
  ·
    refine ⟨1748638542685741985021953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2331518056914322646695937 1748638542685741985021953)
    ·
      refine ⟨1311478907014306488766465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748638542685741985021953 1311478907014306488766465)
      ·
        refine ⟨983609180260729866574849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1311478907014306488766465 983609180260729866574849)
        ·
          refine ⟨737706885195547399931137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983609180260729866574849 737706885195547399931137)
          ·
            refine ⟨553280163896660549948353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737706885195547399931137 553280163896660549948353)
            ·
              refine ⟨414960122922495412461265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553280163896660549948353 414960122922495412461265)
              ·
                refine ⟨311220092191871559345949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414960122922495412461265 311220092191871559345949)
                ·
                  refine ⟨116707534571951834754731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311220092191871559345949 116707534571951834754731)
                  ·
                    rfl

theorem cell20_255698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_255698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255698 prefixEnd_255698 := by exact prefixLift 255698
  have htrace : WordTrace (prefixWord ++ tailWord_255698) baseStart_255698 baseEnd_255698 := by
    simpa [prefixWord, tailWord_255698, baseEnd_255698] using wordTrace_append hprefix tailTrace_255698
  have hstable : (prefixWord ++ tailWord_255698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255698).length < 2 ^ (prefixWord ++ tailWord_255698).sum := by decide
  have hdescent : baseEnd_255698 < baseStart_255698 := by decide
  rcases family_descends (prefixWord ++ tailWord_255698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255705 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 2]
def baseStart_255705 : Nat := 118140960795 + 255705 * 2 ^ 59
def prefixEnd_255705 : Nat := 4983230072969 + 3 ^ 40 * 255705 * 2
def baseEnd_255705 : Nat := 116710729562690921521369

theorem tailTrace_255705 : CollatzResearch.WordTrace tailWord_255705 prefixEnd_255705 116710729562690921521369 := by
  unfold tailWord_255705
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326327538631930782288569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6217551692421287188192379 9326327538631930782288569)
  ·
    refine ⟨6994745653973948086716427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9326327538631930782288569 6994745653973948086716427)
    ·
      refine ⟨10492118480960922130074641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994745653973948086716427 10492118480960922130074641)
      ·
        refine ⟨7869088860720691597555981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492118480960922130074641 7869088860720691597555981)
        ·
          refine ⟨2950908322770259349083493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7869088860720691597555981 2950908322770259349083493)
          ·
            refine ⟨553295310519423627953155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2950908322770259349083493 553295310519423627953155)
            ·
              refine ⟨829942965779135441929733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553295310519423627953155 829942965779135441929733)
              ·
                refine ⟨155614306083587895361825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829942965779135441929733 155614306083587895361825)
                ·
                  refine ⟨116710729562690921521369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155614306083587895361825 116710729562690921521369)
                  ·
                    rfl

theorem cell20_255705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_255705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255705 prefixEnd_255705 := by exact prefixLift 255705
  have htrace : WordTrace (prefixWord ++ tailWord_255705) baseStart_255705 baseEnd_255705 := by
    simpa [prefixWord, tailWord_255705, baseEnd_255705] using wordTrace_append hprefix tailTrace_255705
  have hstable : (prefixWord ++ tailWord_255705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255705).length < 2 ^ (prefixWord ++ tailWord_255705).sum := by decide
  have hdescent : baseEnd_255705 < baseStart_255705 := by decide
  rcases family_descends (prefixWord ++ tailWord_255705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255708 : List Nat := [2, 2, 5, 1, 3, 1, 1, 5]
def baseStart_255708 : Nat := 118140960795 + 255708 * 2 ^ 59
def prefixEnd_255708 : Nat := 4983230072969 + 3 ^ 40 * 255708 * 2
def baseEnd_255708 : Nat := 38904032948145414807119

theorem tailTrace_255708 : CollatzResearch.WordTrace tailWord_255708 prefixEnd_255708 38904032948145414807119 := by
  unfold tailWord_255708
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663218478810531147323889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6217624638414041529765185 4663218478810531147323889)
  ·
    refine ⟨3497413859107898360492917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4663218478810531147323889 3497413859107898360492917)
    ·
      refine ⟨327882549291365471296211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3497413859107898360492917 327882549291365471296211)
      ·
        refine ⟨491823823937048206944317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327882549291365471296211 491823823937048206944317)
        ·
          refine ⟨184433933976393077604119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491823823937048206944317 184433933976393077604119)
          ·
            refine ⟨276650900964589616406179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184433933976393077604119 276650900964589616406179)
            ·
              refine ⟨414976351446884424609269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276650900964589616406179 414976351446884424609269)
              ·
                refine ⟨38904032948145414807119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414976351446884424609269 38904032948145414807119)
                ·
                  rfl

theorem cell20_255708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_255708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255708 prefixEnd_255708 := by exact prefixLift 255708
  have htrace : WordTrace (prefixWord ++ tailWord_255708) baseStart_255708 baseEnd_255708 := by
    simpa [prefixWord, tailWord_255708, baseEnd_255708] using wordTrace_append hprefix tailTrace_255708
  have hstable : (prefixWord ++ tailWord_255708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255708).length < 2 ^ (prefixWord ++ tailWord_255708).sum := by decide
  have hdescent : baseEnd_255708 < baseStart_255708 := by decide
  rcases family_descends (prefixWord ++ tailWord_255708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255726 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_255726 : Nat := 118140960795 + 255726 * 2 ^ 59
def prefixEnd_255726 : Nat := 4983230072969 + 3 ^ 40 * 255726 * 2
def baseEnd_255726 : Nat := 116720314534908181821283

theorem tailTrace_255726 : CollatzResearch.WordTrace tailWord_255726 prefixEnd_255726 116720314534908181821283 := by
  unfold tailWord_255726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165886683944481421100379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6218062314370567579202021 1165886683944481421100379)
  ·
    refine ⟨1748830025916722131650569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1165886683944481421100379 1748830025916722131650569)
    ·
      refine ⟨1311622519437541598737927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748830025916722131650569 1311622519437541598737927)
      ·
        refine ⟨1967433779156312398106891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311622519437541598737927 1967433779156312398106891)
        ·
          refine ⟨2951150668734468597160337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967433779156312398106891 2951150668734468597160337)
          ·
            refine ⟨2213363001550851447870253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951150668734468597160337 2213363001550851447870253)
            ·
              refine ⟨830011125581569292951345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213363001550851447870253 830011125581569292951345)
              ·
                refine ⟨622508344186176969713509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830011125581569292951345 622508344186176969713509)
                ·
                  refine ⟨116720314534908181821283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622508344186176969713509 116720314534908181821283)
                  ·
                    rfl

theorem cell20_255726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_255726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255726 prefixEnd_255726 := by exact prefixLift 255726
  have htrace : WordTrace (prefixWord ++ tailWord_255726) baseStart_255726 baseEnd_255726 := by
    simpa [prefixWord, tailWord_255726, baseEnd_255726] using wordTrace_append hprefix tailTrace_255726
  have hstable : (prefixWord ++ tailWord_255726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255726).length < 2 ^ (prefixWord ++ tailWord_255726).sum := by decide
  have hdescent : baseEnd_255726 < baseStart_255726 := by decide
  rcases family_descends (prefixWord ++ tailWord_255726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255740 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_255740 : Nat := 118140960795 + 255740 * 2 ^ 59
def prefixEnd_255740 : Nat := 4983230072969 + 3 ^ 40 * 255740 * 2
def baseEnd_255740 : Nat := 116726704516386355354559

theorem tailTrace_255740 : CollatzResearch.WordTrace tailWord_255740 prefixEnd_255740 116726704516386355354559 := by
  unfold tailWord_255740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663802046752565879906337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6218402729003421173208449 4663802046752565879906337)
  ·
    refine ⟨3497851535064424409929753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4663802046752565879906337 3497851535064424409929753)
    ·
      refine ⟨2623388651298318307447315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3497851535064424409929753 2623388651298318307447315)
      ·
        refine ⟨3935082976947477461170973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623388651298318307447315 3935082976947477461170973)
        ·
          refine ⟨1475656116355304047939115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3935082976947477461170973 1475656116355304047939115)
          ·
            refine ⟨2213484174532956071908673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475656116355304047939115 2213484174532956071908673)
            ·
              refine ⟨1660113130899717053931505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213484174532956071908673 1660113130899717053931505)
              ·
                refine ⟨1245084848174787790448629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660113130899717053931505 1245084848174787790448629)
                ·
                  refine ⟨116726704516386355354559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245084848174787790448629 116726704516386355354559)
                  ·
                    rfl

theorem cell20_255740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_255740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255740 prefixEnd_255740 := by exact prefixLift 255740
  have htrace : WordTrace (prefixWord ++ tailWord_255740) baseStart_255740 baseEnd_255740 := by
    simpa [prefixWord, tailWord_255740, baseEnd_255740] using wordTrace_append hprefix tailTrace_255740
  have hstable : (prefixWord ++ tailWord_255740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255740).length < 2 ^ (prefixWord ++ tailWord_255740).sum := by decide
  have hdescent : baseEnd_255740 < baseStart_255740 := by decide
  rcases family_descends (prefixWord ++ tailWord_255740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255788 : List Nat := [2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_255788 : Nat := 118140960795 + 255788 * 2 ^ 59
def prefixEnd_255788 : Nat := 4983230072969 + 3 ^ 40 * 255788 * 2
def baseEnd_255788 : Nat := 38916204341437173918121

theorem tailTrace_255788 : CollatzResearch.WordTrace tailWord_255788 prefixEnd_255788 38916204341437173918121 := by
  unfold tailWord_255788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664677398665617978780009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6219569864887490638373345 4664677398665617978780009)
  ·
    refine ⟨3498508048999213484085007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4664677398665617978780009 3498508048999213484085007)
    ·
      refine ⟨5247762073498820226127511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498508048999213484085007 5247762073498820226127511)
      ·
        refine ⟨7871643110248230339191267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247762073498820226127511 7871643110248230339191267)
        ·
          refine ⟨11807464665372345508786901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871643110248230339191267 11807464665372345508786901)
          ·
            refine ⟨276737453094664347862193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11807464665372345508786901 276737453094664347862193)
            ·
              refine ⟨207553089820998260896645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276737453094664347862193 207553089820998260896645)
              ·
                refine ⟨38916204341437173918121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207553089820998260896645 38916204341437173918121)
                ·
                  rfl

theorem cell20_255788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_255788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255788 prefixEnd_255788 := by exact prefixLift 255788
  have htrace : WordTrace (prefixWord ++ tailWord_255788) baseStart_255788 baseEnd_255788 := by
    simpa [prefixWord, tailWord_255788, baseEnd_255788] using wordTrace_append hprefix tailTrace_255788
  have hstable : (prefixWord ++ tailWord_255788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255788).length < 2 ^ (prefixWord ++ tailWord_255788).sum := by decide
  have hdescent : baseEnd_255788 < baseStart_255788 := by decide
  rcases family_descends (prefixWord ++ tailWord_255788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255816 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_255816 : Nat := 118140960795 + 255816 * 2 ^ 59
def prefixEnd_255816 : Nat := 4983230072969 + 3 ^ 40 * 255816 * 2
def baseEnd_255816 : Nat := 116761392987267868820915

theorem tailTrace_255816 : CollatzResearch.WordTrace tailWord_255816 prefixEnd_255816 116761392987267868820915 := by
  unfold tailWord_255816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665188020614898369789651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6220250694153197826386201 4665188020614898369789651)
  ·
    refine ⟨6997782030922347554684477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665188020614898369789651 6997782030922347554684477)
    ·
      refine ⟨2624168261595880333006679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6997782030922347554684477 2624168261595880333006679)
      ·
        refine ⟨3936252392393820499510019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624168261595880333006679 3936252392393820499510019)
        ·
          refine ⟨5904378588590730749265029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936252392393820499510019 5904378588590730749265029)
          ·
            refine ⟨1107070985360762015487193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5904378588590730749265029 1107070985360762015487193)
            ·
              refine ⟨830303239020571511615395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107070985360762015487193 830303239020571511615395)
              ·
                refine ⟨1245454858530857267423093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830303239020571511615395 1245454858530857267423093)
                ·
                  refine ⟨116761392987267868820915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245454858530857267423093 116761392987267868820915)
                  ·
                    rfl

theorem cell20_255816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_255816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255816 prefixEnd_255816 := by exact prefixLift 255816
  have htrace : WordTrace (prefixWord ++ tailWord_255816) baseStart_255816 baseEnd_255816 := by
    simpa [prefixWord, tailWord_255816, baseEnd_255816] using wordTrace_append hprefix tailTrace_255816
  have hstable : (prefixWord ++ tailWord_255816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255816).length < 2 ^ (prefixWord ++ tailWord_255816).sum := by decide
  have hdescent : baseEnd_255816 < baseStart_255816 := by decide
  rcases family_descends (prefixWord ++ tailWord_255816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255870 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_255870 : Nat := 118140960795 + 255870 * 2 ^ 59
def prefixEnd_255870 : Nat := 4983230072969 + 3 ^ 40 * 255870 * 2
def baseEnd_255870 : Nat := 116786040058683681020695

theorem tailTrace_255870 : CollatzResearch.WordTrace tailWord_255870 prefixEnd_255870 116786040058683681020695 := by
  unfold tailWord_255870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166543197879270495255633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6221563722022775974696709 1166543197879270495255633)
  ·
    refine ⟨874907398409452871441725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1166543197879270495255633 874907398409452871441725)
    ·
      refine ⟨328090274403544826790647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 874907398409452871441725 328090274403544826790647)
      ·
        refine ⟨492135411605317240185971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328090274403544826790647 492135411605317240185971)
        ·
          refine ⟨738203117407975860278957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492135411605317240185971 738203117407975860278957)
          ·
            refine ⟨276826169027990947604609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 738203117407975860278957 276826169027990947604609)
            ·
              refine ⟨207619626770993210703457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276826169027990947604609 207619626770993210703457)
              ·
                refine ⟨155714720078244908027593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207619626770993210703457 155714720078244908027593)
                ·
                  refine ⟨116786040058683681020695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155714720078244908027593 116786040058683681020695)
                  ·
                    rfl

theorem cell20_255870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_255870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255870 prefixEnd_255870 := by exact prefixLift 255870
  have htrace : WordTrace (prefixWord ++ tailWord_255870) baseStart_255870 baseEnd_255870 := by
    simpa [prefixWord, tailWord_255870, baseEnd_255870] using wordTrace_append hprefix tailTrace_255870
  have hstable : (prefixWord ++ tailWord_255870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255870).length < 2 ^ (prefixWord ++ tailWord_255870).sum := by decide
  have hdescent : baseEnd_255870 < baseStart_255870 := by decide
  rcases family_descends (prefixWord ++ tailWord_255870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255930 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_255930 : Nat := 118140960795 + 255930 * 2 ^ 59
def prefixEnd_255930 : Nat := 4983230072969 + 3 ^ 40 * 255930 * 2
def baseEnd_255930 : Nat := 116813425693590139020449

theorem tailTrace_255930 : CollatzResearch.WordTrace tailWord_255930 prefixEnd_255930 116813425693590139020449 := by
  unfold tailWord_255930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333633490704198552307311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6223022641877862806152829 2333633490704198552307311)
  ·
    refine ⟨3500450236056297828460967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333633490704198552307311 3500450236056297828460967)
    ·
      refine ⟨5250675354084446742691451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500450236056297828460967 5250675354084446742691451)
      ·
        refine ⟨7876013031126670114037177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250675354084446742691451 7876013031126670114037177)
        ·
          refine ⟨5907009773345002585527883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7876013031126670114037177 5907009773345002585527883)
          ·
            refine ⟨8860514660017503878291825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907009773345002585527883 8860514660017503878291825)
            ·
              refine ⟨6645385995013127908718869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8860514660017503878291825 6645385995013127908718869)
              ·
                refine ⟨311502468516240370721197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6645385995013127908718869 311502468516240370721197)
                ·
                  refine ⟨116813425693590139020449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311502468516240370721197 116813425693590139020449)
                  ·
                    rfl

theorem cell20_255930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_255930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255930 prefixEnd_255930 := by exact prefixLift 255930
  have htrace : WordTrace (prefixWord ++ tailWord_255930) baseStart_255930 baseEnd_255930 := by
    simpa [prefixWord, tailWord_255930, baseEnd_255930] using wordTrace_append hprefix tailTrace_255930
  have hstable : (prefixWord ++ tailWord_255930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255930).length < 2 ^ (prefixWord ++ tailWord_255930).sum := by decide
  have hdescent : baseEnd_255930 < baseStart_255930 := by decide
  rcases family_descends (prefixWord ++ tailWord_255930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255933 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 2]
def baseStart_255933 : Nat := 118140960795 + 255933 * 2 ^ 59
def prefixEnd_255933 : Nat := 4983230072969 + 3 ^ 40 * 255933 * 2
def baseEnd_255933 : Nat := 116814794975335461920437

theorem tailTrace_255933 : CollatzResearch.WordTrace tailWord_255933 prefixEnd_255933 116814794975335461920437 := by
  unfold tailWord_255933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334643381805925721588453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6223095587870617147725635 9334643381805925721588453)
  ·
    refine ⟨1750245634088611072797835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9334643381805925721588453 1750245634088611072797835)
    ·
      refine ⟨2625368451132916609196753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750245634088611072797835 2625368451132916609196753)
      ·
        refine ⟨1969026338349687456897565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625368451132916609196753 1969026338349687456897565)
        ·
          refine ⟨738384876881132796336587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1969026338349687456897565 738384876881132796336587)
          ·
            refine ⟨1107577315321699194504881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738384876881132796336587 1107577315321699194504881)
            ·
              refine ⟨830682986491274395878661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107577315321699194504881 830682986491274395878661)
              ·
                refine ⟨155753059967113949227249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830682986491274395878661 155753059967113949227249)
                ·
                  refine ⟨116814794975335461920437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155753059967113949227249 116814794975335461920437)
                  ·
                    rfl

theorem cell20_255933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_255933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255933 prefixEnd_255933 := by exact prefixLift 255933
  have htrace : WordTrace (prefixWord ++ tailWord_255933) baseStart_255933 baseEnd_255933 := by
    simpa [prefixWord, tailWord_255933, baseEnd_255933] using wordTrace_append hprefix tailTrace_255933
  have hstable : (prefixWord ++ tailWord_255933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255933).length < 2 ^ (prefixWord ++ tailWord_255933).sum := by decide
  have hdescent : baseEnd_255933 < baseStart_255933 := by decide
  rcases family_descends (prefixWord ++ tailWord_255933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255947 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 3]
def baseStart_255947 : Nat := 118140960795 + 255947 * 2 ^ 59
def prefixEnd_255947 : Nat := 4983230072969 + 3 ^ 40 * 255947 * 2
def baseEnd_255947 : Nat := 116821184956813635453713

theorem tailTrace_255947 : CollatzResearch.WordTrace tailWord_255947 prefixEnd_255947 116821184956813635453713 := by
  unfold tailWord_255947
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335154003755206112598095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6223436002503470741732063 9335154003755206112598095)
  ·
    refine ⟨14002731005632809168897143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335154003755206112598095 14002731005632809168897143)
    ·
      refine ⟨21004096508449213753345715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14002731005632809168897143 21004096508449213753345715)
      ·
        refine ⟨31506144762673820630018573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21004096508449213753345715 31506144762673820630018573)
        ·
          refine ⟨11814804286002682736256965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31506144762673820630018573 11814804286002682736256965)
          ·
            refine ⟨2215275803625503013048181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11814804286002682736256965 2215275803625503013048181)
            ·
              refine ⟨207682106589890907473267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2215275803625503013048181 207682106589890907473267)
              ·
                refine ⟨311523159884836361209901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207682106589890907473267 311523159884836361209901)
                ·
                  refine ⟨116821184956813635453713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311523159884836361209901 116821184956813635453713)
                  ·
                    rfl

theorem cell20_255947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_255947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255947 prefixEnd_255947 := by exact prefixLift 255947
  have htrace : WordTrace (prefixWord ++ tailWord_255947) baseStart_255947 baseEnd_255947 := by
    simpa [prefixWord, tailWord_255947, baseEnd_255947] using wordTrace_append hprefix tailTrace_255947
  have hstable : (prefixWord ++ tailWord_255947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255947).length < 2 ^ (prefixWord ++ tailWord_255947).sum := by decide
  have hdescent : baseEnd_255947 < baseStart_255947 := by decide
  rcases family_descends (prefixWord ++ tailWord_255947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255961 : List Nat := [1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_255961 : Nat := 118140960795 + 255961 * 2 ^ 59
def prefixEnd_255961 : Nat := 4983230072969 + 3 ^ 40 * 255961 * 2
def baseEnd_255961 : Nat := 38942524979430602995663

theorem tailTrace_255961 : CollatzResearch.WordTrace tailWord_255961 prefixEnd_255961 38942524979430602995663 := by
  unfold tailWord_255961
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335664625704486503607737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6223776417136324335738491 9335664625704486503607737)
  ·
    refine ⟨7001748469278364877705803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9335664625704486503607737 7001748469278364877705803)
    ·
      refine ⟨10502622703917547316558705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7001748469278364877705803 10502622703917547316558705)
      ·
        refine ⟨7876967027938160487419029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10502622703917547316558705 7876967027938160487419029)
        ·
          refine ⟨369232829434601272847767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7876967027938160487419029 369232829434601272847767)
          ·
            refine ⟨553849244151901909271651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369232829434601272847767 553849244151901909271651)
            ·
              refine ⟨830773866227852863907477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553849244151901909271651 830773866227852863907477)
              ·
                refine ⟨38942524979430602995663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 830773866227852863907477 38942524979430602995663)
                ·
                  rfl

theorem cell20_255961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_255961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255961 prefixEnd_255961 := by exact prefixLift 255961
  have htrace : WordTrace (prefixWord ++ tailWord_255961) baseStart_255961 baseEnd_255961 := by
    simpa [prefixWord, tailWord_255961, baseEnd_255961] using wordTrace_append hprefix tailTrace_255961
  have hstable : (prefixWord ++ tailWord_255961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255961).length < 2 ^ (prefixWord ++ tailWord_255961).sum := by decide
  have hdescent : baseEnd_255961 < baseStart_255961 := by decide
  rcases family_descends (prefixWord ++ tailWord_255961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255971 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 2]
def baseStart_255971 : Nat := 118140960795 + 255971 * 2 ^ 59
def prefixEnd_255971 : Nat := 4983230072969 + 3 ^ 40 * 255971 * 2
def baseEnd_255971 : Nat := 116832139210776218653615

theorem tailTrace_255971 : CollatzResearch.WordTrace tailWord_255971 prefixEnd_255971 116832139210776218653615 := by
  unfold tailWord_255971
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336029355668258211471767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6224019570445505474314511 9336029355668258211471767)
  ·
    refine ⟨14004044033502387317207651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336029355668258211471767 14004044033502387317207651)
    ·
      refine ⟨21006066050253580975811477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14004044033502387317207651 21006066050253580975811477)
      ·
        refine ⟨984659346105636608241163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21006066050253580975811477 984659346105636608241163)
        ·
          refine ⟨1476989019158454912361745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984659346105636608241163 1476989019158454912361745)
          ·
            refine ⟨1107741764368841184271309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476989019158454912361745 1107741764368841184271309)
            ·
              refine ⟨415403161638315444101741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1107741764368841184271309 415403161638315444101741)
              ·
                refine ⟨155776185614368291538153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415403161638315444101741 155776185614368291538153)
                ·
                  refine ⟨116832139210776218653615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155776185614368291538153 116832139210776218653615)
                  ·
                    rfl

theorem cell20_255971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2].length) (baseStart_255971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255971 prefixEnd_255971 := by exact prefixLift 255971
  have htrace : WordTrace (prefixWord ++ tailWord_255971) baseStart_255971 baseEnd_255971 := by
    simpa [prefixWord, tailWord_255971, baseEnd_255971] using wordTrace_append hprefix tailTrace_255971
  have hstable : (prefixWord ++ tailWord_255971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255971).length < 2 ^ (prefixWord ++ tailWord_255971).sum := by decide
  have hdescent : baseEnd_255971 < baseStart_255971 := by decide
  rcases family_descends (prefixWord ++ tailWord_255971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255992 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_255992 : Nat := 118140960795 + 255992 * 2 ^ 59
def prefixEnd_255992 : Nat := 4983230072969 + 3 ^ 40 * 255992 * 2
def baseEnd_255992 : Nat := 116841724182993478953529

theorem tailTrace_255992 : CollatzResearch.WordTrace tailWord_255992 prefixEnd_255992 116841724182993478953529 := by
  unfold tailWord_255992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668397644296089398993115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6224530192394785865324153 4668397644296089398993115)
  ·
    refine ⟨7002596466444134098489673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4668397644296089398993115 7002596466444134098489673)
    ·
      refine ⟨5251947349833100573867255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7002596466444134098489673 5251947349833100573867255)
      ·
        refine ⟨7877921024749650860800883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251947349833100573867255 7877921024749650860800883)
        ·
          refine ⟨11816881537124476291201325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877921024749650860800883 11816881537124476291201325)
          ·
            refine ⟨4431330576421678609200497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11816881537124476291201325 4431330576421678609200497)
            ·
              refine ⟨3323497932316258956900373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431330576421678609200497 3323497932316258956900373)
              ·
                refine ⟨155788965577324638604705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3323497932316258956900373 155788965577324638604705)
                ·
                  refine ⟨116841724182993478953529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155788965577324638604705 116841724182993478953529)
                  ·
                    rfl

theorem cell20_255992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_255992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_255992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_255992 prefixEnd_255992 := by exact prefixLift 255992
  have htrace : WordTrace (prefixWord ++ tailWord_255992) baseStart_255992 baseEnd_255992 := by
    simpa [prefixWord, tailWord_255992, baseEnd_255992] using wordTrace_append hprefix tailTrace_255992
  have hstable : (prefixWord ++ tailWord_255992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255992).length < 2 ^ (prefixWord ++ tailWord_255992).sum := by decide
  have hdescent : baseEnd_255992 < baseStart_255992 := by decide
  rcases family_descends (prefixWord ++ tailWord_255992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256027 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_256027 : Nat := 118140960795 + 256027 * 2 ^ 59
def prefixEnd_256027 : Nat := 4983230072969 + 3 ^ 40 * 256027 * 2
def baseEnd_256027 : Nat := 116857699136688912786719

theorem tailTrace_256027 : CollatzResearch.WordTrace tailWord_256027 prefixEnd_256027 116857699136688912786719 := by
  unfold tailWord_256027
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338071843465379775510335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6225381228976919850340223 9338071843465379775510335)
  ·
    refine ⟨14007107765198069663265503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9338071843465379775510335 14007107765198069663265503)
    ·
      refine ⟨21010661647797104494898255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007107765198069663265503 21010661647797104494898255)
      ·
        refine ⟨31515992471695656742347383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21010661647797104494898255 31515992471695656742347383)
        ·
          refine ⟨47273988707543485113521075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31515992471695656742347383 47273988707543485113521075)
          ·
            refine ⟨70910983061315227670281613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47273988707543485113521075 70910983061315227670281613)
            ·
              refine ⟨26591618647993210376355605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70910983061315227670281613 26591618647993210376355605)
              ·
                refine ⟨1246482124124681736391669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26591618647993210376355605 1246482124124681736391669)
                ·
                  refine ⟨116857699136688912786719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246482124124681736391669 116857699136688912786719)
                  ·
                    rfl

theorem cell20_256027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_256027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256027 prefixEnd_256027 := by exact prefixLift 256027
  have htrace : WordTrace (prefixWord ++ tailWord_256027) baseStart_256027 baseEnd_256027 := by
    simpa [prefixWord, tailWord_256027, baseEnd_256027] using wordTrace_append hprefix tailTrace_256027
  have hstable : (prefixWord ++ tailWord_256027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256027).length < 2 ^ (prefixWord ++ tailWord_256027).sum := by decide
  have hdescent : baseEnd_256027 < baseStart_256027 := by decide
  rcases family_descends (prefixWord ++ tailWord_256027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256085 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 2]
def baseStart_256085 : Nat := 118140960795 + 256085 * 2 ^ 59
def prefixEnd_256085 : Nat := 4983230072969 + 3 ^ 40 * 256085 * 2
def baseEnd_256085 : Nat := 116884171917098488853149

theorem tailTrace_256085 : CollatzResearch.WordTrace tailWord_256085 prefixEnd_256085 116884171917098488853149 := by
  unfold tailWord_256085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340187277255255681121709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6226791518170170454081139 9340187277255255681121709)
  ·
    refine ⟨3502570228970720880420641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9340187277255255681121709 3502570228970720880420641)
    ·
      refine ⟨2626927671728040660315481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3502570228970720880420641 2626927671728040660315481)
      ·
        refine ⟨1970195753796030495236611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2626927671728040660315481 1970195753796030495236611)
        ·
          refine ⟨2955293630694045742854917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970195753796030495236611 2955293630694045742854917)
          ·
            refine ⟨554117555755133576785297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2955293630694045742854917 554117555755133576785297)
            ·
              refine ⟨415588166816350182588973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554117555755133576785297 415588166816350182588973)
              ·
                refine ⟨155845562556131318470865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415588166816350182588973 155845562556131318470865)
                ·
                  refine ⟨116884171917098488853149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155845562556131318470865 116884171917098488853149)
                  ·
                    rfl

theorem cell20_256085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_256085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256085 prefixEnd_256085 := by exact prefixLift 256085
  have htrace : WordTrace (prefixWord ++ tailWord_256085) baseStart_256085 baseEnd_256085 := by
    simpa [prefixWord, tailWord_256085, baseEnd_256085] using wordTrace_append hprefix tailTrace_256085
  have hstable : (prefixWord ++ tailWord_256085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256085).length < 2 ^ (prefixWord ++ tailWord_256085).sum := by decide
  have hdescent : baseEnd_256085 < baseStart_256085 := by decide
  rcases family_descends (prefixWord ++ tailWord_256085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256096 : List Nat := [2, 1, 1, 3, 2, 4, 7]
def baseStart_256096 : Nat := 118140960795 + 256096 * 2 ^ 59
def prefixEnd_256096 : Nat := 4983230072969 + 3 ^ 40 * 256096 * 2
def baseEnd_256096 : Nat := 12987688068536815498493

theorem tailTrace_256096 : CollatzResearch.WordTrace tailWord_256096 prefixEnd_256096 12987688068536815498493 := by
  unfold tailWord_256096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670294240107702279886071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6227058986810269706514761 4670294240107702279886071)
  ·
    refine ⟨7005441360161553419829107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4670294240107702279886071 7005441360161553419829107)
    ·
      refine ⟨10508162040242330129743661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005441360161553419829107 10508162040242330129743661)
      ·
        refine ⟨3940560765090873798653873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10508162040242330129743661 3940560765090873798653873)
        ·
          refine ⟨2955420573818155348990405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3940560765090873798653873 2955420573818155348990405)
          ·
            refine ⟨554141357590904127935701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2955420573818155348990405 554141357590904127935701)
            ·
              refine ⟨12987688068536815498493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 554141357590904127935701 12987688068536815498493)
              ·
                rfl

theorem cell20_256096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_256096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256096 prefixEnd_256096 := by exact prefixLift 256096
  have htrace : WordTrace (prefixWord ++ tailWord_256096) baseStart_256096 baseEnd_256096 := by
    simpa [prefixWord, tailWord_256096, baseEnd_256096] using wordTrace_append hprefix tailTrace_256096
  have hstable : (prefixWord ++ tailWord_256096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256096).length < 2 ^ (prefixWord ++ tailWord_256096).sum := by decide
  have hdescent : baseEnd_256096 < baseStart_256096 := by decide
  rcases family_descends (prefixWord ++ tailWord_256096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256151 : List Nat := [1, 1, 3, 3, 4, 2, 6]
def baseStart_256151 : Nat := 118140960795 + 256151 * 2 ^ 59
def prefixEnd_256151 : Nat := 4983230072969 + 3 ^ 40 * 256151 * 2
def baseEnd_256151 : Nat := 12990477346166176961431

theorem tailTrace_256151 : CollatzResearch.WordTrace tailWord_256151 prefixEnd_256151 12990477346166176961431 := by
  unfold tailWord_256151
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342594495016148953024307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6228396330010765968682871 9342594495016148953024307)
  ·
    refine ⟨14013891742524223429536461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9342594495016148953024307 14013891742524223429536461)
    ·
      refine ⟨5255209403446583786076173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14013891742524223429536461 5255209403446583786076173)
      ·
        refine ⟨1970703526292468919778565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5255209403446583786076173 1970703526292468919778565)
        ·
          refine ⟨369506911179837922458481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1970703526292468919778565 369506911179837922458481)
          ·
            refine ⟨277130183384878441843861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369506911179837922458481 277130183384878441843861)
            ·
              refine ⟨12990477346166176961431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277130183384878441843861 12990477346166176961431)
              ·
                rfl

theorem cell20_256151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_256151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256151 prefixEnd_256151 := by exact prefixLift 256151
  have htrace : WordTrace (prefixWord ++ tailWord_256151) baseStart_256151 baseEnd_256151 := by
    simpa [prefixWord, tailWord_256151, baseEnd_256151] using wordTrace_append hprefix tailTrace_256151
  have hstable : (prefixWord ++ tailWord_256151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256151).length < 2 ^ (prefixWord ++ tailWord_256151).sum := by decide
  have hdescent : baseEnd_256151 < baseStart_256151 := by decide
  rcases family_descends (prefixWord ++ tailWord_256151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256210 : List Nat := [3, 2, 2, 2, 1, 10]
def baseStart_256210 : Nat := 118140960795 + 256210 * 2 ^ 59
def prefixEnd_256210 : Nat := 4983230072969 + 3 ^ 40 * 256210 * 2
def baseEnd_256210 : Nat := 4331156493450133692073

theorem tailTrace_256210 : CollatzResearch.WordTrace tailWord_256210 prefixEnd_256210 4331156493450133692073 := by
  unfold tailWord_256210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336186600450600507355521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6229830934534934686281389 2336186600450600507355521)
  ·
    refine ⟨1752139950337950380516641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2336186600450600507355521 1752139950337950380516641)
    ·
      refine ⟨1314104962753462785387481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1752139950337950380516641 1314104962753462785387481)
      ·
        refine ⟨985578722065097089040611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314104962753462785387481 985578722065097089040611)
        ·
          refine ⟨1478368083097645633560917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985578722065097089040611 1478368083097645633560917)
          ·
            refine ⟨4331156493450133692073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1478368083097645633560917 4331156493450133692073)
            ·
              rfl

theorem cell20_256210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 10].length) (baseStart_256210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256210 prefixEnd_256210 := by exact prefixLift 256210
  have htrace : WordTrace (prefixWord ++ tailWord_256210) baseStart_256210 baseEnd_256210 := by
    simpa [prefixWord, tailWord_256210, baseEnd_256210] using wordTrace_append hprefix tailTrace_256210
  have hstable : (prefixWord ++ tailWord_256210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256210).length < 2 ^ (prefixWord ++ tailWord_256210).sum := by decide
  have hdescent : baseEnd_256210 < baseStart_256210 := by decide
  rcases family_descends (prefixWord ++ tailWord_256210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256216 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_256216 : Nat := 118140960795 + 256216 * 2 ^ 59
def prefixEnd_256216 : Nat := 4983230072969 + 3 ^ 40 * 256216 * 2
def baseEnd_256216 : Nat := 116943963886644255485947

theorem tailTrace_256216 : CollatzResearch.WordTrace tailWord_256216 prefixEnd_256216 116943963886644255485947 := by
  unfold tailWord_256216
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672482619890332527070251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6229976826520443369427001 4672482619890332527070251)
  ·
    refine ⟨7008723929835498790605377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672482619890332527070251 7008723929835498790605377)
    ·
      refine ⟨5256542947376624092954033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7008723929835498790605377 5256542947376624092954033)
      ·
        refine ⟨3942407210532468069715525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256542947376624092954033 3942407210532468069715525)
        ·
          refine ⟨739201351974837763071661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3942407210532468069715525 739201351974837763071661)
          ·
            refine ⟨277200506990564161151873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 739201351974837763071661 277200506990564161151873)
            ·
              refine ⟨207900380242923120863905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277200506990564161151873 207900380242923120863905)
              ·
                refine ⟨155925285182192340647929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207900380242923120863905 155925285182192340647929)
                ·
                  refine ⟨116943963886644255485947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155925285182192340647929 116943963886644255485947)
                  ·
                    rfl

theorem cell20_256216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_256216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256216 prefixEnd_256216 := by exact prefixLift 256216
  have htrace : WordTrace (prefixWord ++ tailWord_256216) baseStart_256216 baseEnd_256216 := by
    simpa [prefixWord, tailWord_256216, baseEnd_256216] using wordTrace_append hprefix tailTrace_256216
  have hstable : (prefixWord ++ tailWord_256216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256216).length < 2 ^ (prefixWord ++ tailWord_256216).sum := by decide
  have hdescent : baseEnd_256216 < baseStart_256216 := by decide
  rcases family_descends (prefixWord ++ tailWord_256216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256217 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_256217 : Nat := 118140960795 + 256217 * 2 ^ 59
def prefixEnd_256217 : Nat := 4983230072969 + 3 ^ 40 * 256217 * 2
def baseEnd_256217 : Nat := 116944420313892696452609

theorem tailTrace_256217 : CollatzResearch.WordTrace tailWord_256217 prefixEnd_256217 116944420313892696452609 := by
  unfold tailWord_256217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345001712777042224926905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6230001141851361483284603 9345001712777042224926905)
  ·
    refine ⟨7008751284582781668695179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9345001712777042224926905 7008751284582781668695179)
    ·
      refine ⟨10513126926874172503042769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008751284582781668695179 10513126926874172503042769)
      ·
        refine ⟨7884845195155629377282077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10513126926874172503042769 7884845195155629377282077)
        ·
          refine ⟨2956816948183361016480779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7884845195155629377282077 2956816948183361016480779)
          ·
            refine ⟨4435225422275041524721169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956816948183361016480779 4435225422275041524721169)
            ·
              refine ⟨3326419066706281143540877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435225422275041524721169 3326419066706281143540877)
              ·
                refine ⟨1247407150014855428827829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3326419066706281143540877 1247407150014855428827829)
                ·
                  refine ⟨116944420313892696452609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1247407150014855428827829 116944420313892696452609)
                  ·
                    rfl

theorem cell20_256217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_256217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256217 prefixEnd_256217 := by exact prefixLift 256217
  have htrace : WordTrace (prefixWord ++ tailWord_256217) baseStart_256217 baseEnd_256217 := by
    simpa [prefixWord, tailWord_256217, baseEnd_256217] using wordTrace_append hprefix tailTrace_256217
  have hstable : (prefixWord ++ tailWord_256217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256217).length < 2 ^ (prefixWord ++ tailWord_256217).sum := by decide
  have hdescent : baseEnd_256217 < baseStart_256217 := by decide
  rcases family_descends (prefixWord ++ tailWord_256217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256234 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_256234 : Nat := 118140960795 + 256234 * 2 ^ 59
def prefixEnd_256234 : Nat := 4983230072969 + 3 ^ 40 * 256234 * 2
def baseEnd_256234 : Nat := 116952179577116192885873

theorem tailTrace_256234 : CollatzResearch.WordTrace tailWord_256234 prefixEnd_256234 116952179577116192885873 := by
  unfold tailWord_256234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336405438428863532073939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6230414502476969418863837 2336405438428863532073939)
  ·
    refine ⟨3504608157643295298110909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336405438428863532073939 3504608157643295298110909)
    ·
      refine ⟨1314228059116235736791591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3504608157643295298110909 1314228059116235736791591)
      ·
        refine ⟨1971342088674353605187387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314228059116235736791591 1971342088674353605187387)
        ·
          refine ⟨2957013133011530407781081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971342088674353605187387 2957013133011530407781081)
          ·
            refine ⟨2217759849758647805835811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957013133011530407781081 2217759849758647805835811)
            ·
              refine ⟨3326639774637971708753717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217759849758647805835811 3326639774637971708753717)
              ·
                refine ⟨311872478872309847695661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3326639774637971708753717 311872478872309847695661)
                ·
                  refine ⟨116952179577116192885873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311872478872309847695661 116952179577116192885873)
                  ·
                    rfl

theorem cell20_256234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_256234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256234 prefixEnd_256234 := by exact prefixLift 256234
  have htrace : WordTrace (prefixWord ++ tailWord_256234) baseStart_256234 baseEnd_256234 := by
    simpa [prefixWord, tailWord_256234, baseEnd_256234] using wordTrace_append hprefix tailTrace_256234
  have hstable : (prefixWord ++ tailWord_256234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256234).length < 2 ^ (prefixWord ++ tailWord_256234).sum := by decide
  have hdescent : baseEnd_256234 < baseStart_256234 := by decide
  rcases family_descends (prefixWord ++ tailWord_256234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256255 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_256255 : Nat := 118140960795 + 256255 * 2 ^ 59
def prefixEnd_256255 : Nat := 4983230072969 + 3 ^ 40 * 256255 * 2
def baseEnd_256255 : Nat := 116961764549333453185787

theorem tailTrace_256255 : CollatzResearch.WordTrace tailWord_256255 prefixEnd_256255 116961764549333453185787 := by
  unfold tailWord_256255
  simp only [CollatzResearch.WordTrace]
  refine ⟨9346387686639374714810219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6230925124426249809873479 9346387686639374714810219)
  ·
    refine ⟨14019581529959062072215329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9346387686639374714810219 14019581529959062072215329)
    ·
      refine ⟨10514686147469296554161497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14019581529959062072215329 10514686147469296554161497)
      ·
        refine ⟨7886014610601972415621123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10514686147469296554161497 7886014610601972415621123)
        ·
          refine ⟨11829021915902958623431685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886014610601972415621123 11829021915902958623431685)
          ·
            refine ⟨2217941609231804741893441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11829021915902958623431685 2217941609231804741893441)
            ·
              refine ⟨1663456206923853556420081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217941609231804741893441 1663456206923853556420081)
              ·
                refine ⟨1247592155192890167315061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663456206923853556420081 1247592155192890167315061)
                ·
                  refine ⟨116961764549333453185787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1247592155192890167315061 116961764549333453185787)
                  ·
                    rfl

theorem cell20_256255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_256255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256255 prefixEnd_256255 := by exact prefixLift 256255
  have htrace : WordTrace (prefixWord ++ tailWord_256255) baseStart_256255 baseEnd_256255 := by
    simpa [prefixWord, tailWord_256255, baseEnd_256255] using wordTrace_append hprefix tailTrace_256255
  have hstable : (prefixWord ++ tailWord_256255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256255).length < 2 ^ (prefixWord ++ tailWord_256255).sum := by decide
  have hdescent : baseEnd_256255 < baseStart_256255 := by decide
  rcases family_descends (prefixWord ++ tailWord_256255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256279 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_256279 : Nat := 118140960795 + 256279 * 2 ^ 59
def prefixEnd_256279 : Nat := 4983230072969 + 3 ^ 40 * 256279 * 2
def baseEnd_256279 : Nat := 116972718803296036385689

theorem tailTrace_256279 : CollatzResearch.WordTrace tailWord_256279 prefixEnd_256279 116972718803296036385689 := by
  unfold tailWord_256279
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347263038552426813683891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6231508692368284542455927 9347263038552426813683891)
  ·
    refine ⟨14020894557828640220525837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347263038552426813683891 14020894557828640220525837)
    ·
      refine ⟨5257835459185740082697189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14020894557828640220525837 5257835459185740082697189)
      ·
        refine ⟨985844148597326265505723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5257835459185740082697189 985844148597326265505723)
        ·
          refine ⟨1478766222895989398258585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985844148597326265505723 1478766222895989398258585)
          ·
            refine ⟨1109074667171992048693939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478766222895989398258585 1109074667171992048693939)
            ·
              refine ⟨1663612000757988073040909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109074667171992048693939 1663612000757988073040909)
              ·
                refine ⟨623854500284245527390341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663612000757988073040909 623854500284245527390341)
                ·
                  refine ⟨116972718803296036385689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 623854500284245527390341 116972718803296036385689)
                  ·
                    rfl

theorem cell20_256279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_256279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256279 prefixEnd_256279 := by exact prefixLift 256279
  have htrace : WordTrace (prefixWord ++ tailWord_256279) baseStart_256279 baseEnd_256279 := by
    simpa [prefixWord, tailWord_256279, baseEnd_256279] using wordTrace_append hprefix tailTrace_256279
  have hstable : (prefixWord ++ tailWord_256279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256279).length < 2 ^ (prefixWord ++ tailWord_256279).sum := by decide
  have hdescent : baseEnd_256279 < baseStart_256279 := by decide
  rcases family_descends (prefixWord ++ tailWord_256279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256295 : List Nat := [1, 1, 8, 1, 2, 1, 2, 4]
def baseStart_256295 : Nat := 118140960795 + 256295 * 2 ^ 59
def prefixEnd_256295 : Nat := 4983230072969 + 3 ^ 40 * 256295 * 2
def baseEnd_256295 : Nat := 38993340546423697284097

theorem tailTrace_256295 : CollatzResearch.WordTrace tailWord_256295 prefixEnd_256295 38993340546423697284097 := by
  unfold tailWord_256295
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347846606494461546266339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6231897737662974364177559 9347846606494461546266339)
  ·
    refine ⟨14021769909741692319399509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347846606494461546266339 14021769909741692319399509)
    ·
      refine ⟨164317616129785456867963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 14021769909741692319399509 164317616129785456867963)
      ·
        refine ⟨246476424194678185301945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164317616129785456867963 246476424194678185301945)
        ·
          refine ⟨184857318146008638976459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246476424194678185301945 184857318146008638976459)
          ·
            refine ⟨277285977219012958464689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184857318146008638976459 277285977219012958464689)
            ·
              refine ⟨207964482914259718848517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277285977219012958464689 207964482914259718848517)
              ·
                refine ⟨38993340546423697284097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207964482914259718848517 38993340546423697284097)
                ·
                  rfl

theorem cell20_256295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_256295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256295 prefixEnd_256295 := by exact prefixLift 256295
  have htrace : WordTrace (prefixWord ++ tailWord_256295) baseStart_256295 baseEnd_256295 := by
    simpa [prefixWord, tailWord_256295, baseEnd_256295] using wordTrace_append hprefix tailTrace_256295
  have hstable : (prefixWord ++ tailWord_256295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256295).length < 2 ^ (prefixWord ++ tailWord_256295).sum := by decide
  have hdescent : baseEnd_256295 < baseStart_256295 := by decide
  rcases family_descends (prefixWord ++ tailWord_256295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256313 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 2]
def baseStart_256313 : Nat := 118140960795 + 256313 * 2 ^ 59
def prefixEnd_256313 : Nat := 4983230072969 + 3 ^ 40 * 256313 * 2
def baseEnd_256313 : Nat := 116988237329743029252217

theorem tailTrace_256313 : CollatzResearch.WordTrace tailWord_256313 prefixEnd_256313 116988237329743029252217 := by
  unfold tailWord_256313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348503120429250620421593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6232335413619500413614395 9348503120429250620421593)
  ·
    refine ⟨7011377340321937965316195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9348503120429250620421593 7011377340321937965316195)
    ·
      refine ⟨10517066010482906947974293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011377340321937965316195 10517066010482906947974293)
      ·
        refine ⟨492987469241386263186295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10517066010482906947974293 492987469241386263186295)
        ·
          refine ⟨739481203862079394779443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492987469241386263186295 739481203862079394779443)
          ·
            refine ⟨1109221805793119092169165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739481203862079394779443 1109221805793119092169165)
            ·
              refine ⟨415958177172419659563437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109221805793119092169165 415958177172419659563437)
              ·
                refine ⟨155984316439657372336289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415958177172419659563437 155984316439657372336289)
                ·
                  refine ⟨116988237329743029252217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155984316439657372336289 116988237329743029252217)
                  ·
                    rfl

theorem cell20_256313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_256313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256313 prefixEnd_256313 := by exact prefixLift 256313
  have htrace : WordTrace (prefixWord ++ tailWord_256313) baseStart_256313 baseEnd_256313 := by
    simpa [prefixWord, tailWord_256313, baseEnd_256313] using wordTrace_append hprefix tailTrace_256313
  have hstable : (prefixWord ++ tailWord_256313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256313).length < 2 ^ (prefixWord ++ tailWord_256313).sum := by decide
  have hdescent : baseEnd_256313 < baseStart_256313 := by decide
  rcases family_descends (prefixWord ++ tailWord_256313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256341 : List Nat := [1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_256341 : Nat := 118140960795 + 256341 * 2 ^ 59
def prefixEnd_256341 : Nat := 4983230072969 + 3 ^ 40 * 256341 * 2
def baseEnd_256341 : Nat := 39000339097566458772923

theorem tailTrace_256341 : CollatzResearch.WordTrace tailWord_256341 prefixEnd_256341 39000339097566458772923 := by
  unfold tailWord_256341
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349524364327811402440877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6233016242885207601627251 9349524364327811402440877)
  ·
    refine ⟨3506071636622929275915329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9349524364327811402440877 3506071636622929275915329)
    ·
      refine ⟨2629553727467196956936497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3506071636622929275915329 2629553727467196956936497)
      ·
        refine ⟨1972165295600397717702373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2629553727467196956936497 1972165295600397717702373)
        ·
          refine ⟨369780992925074572069195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1972165295600397717702373 369780992925074572069195)
          ·
            refine ⟨554671489387611858103793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369780992925074572069195 554671489387611858103793)
            ·
              refine ⟨416003617040708893577845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554671489387611858103793 416003617040708893577845)
              ·
                refine ⟨39000339097566458772923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416003617040708893577845 39000339097566458772923)
                ·
                  rfl

theorem cell20_256341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_256341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256341 prefixEnd_256341 := by exact prefixLift 256341
  have htrace : WordTrace (prefixWord ++ tailWord_256341) baseStart_256341 baseEnd_256341 := by
    simpa [prefixWord, tailWord_256341, baseEnd_256341] using wordTrace_append hprefix tailTrace_256341
  have hstable : (prefixWord ++ tailWord_256341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256341).length < 2 ^ (prefixWord ++ tailWord_256341).sum := by decide
  have hdescent : baseEnd_256341 < baseStart_256341 := by decide
  rcases family_descends (prefixWord ++ tailWord_256341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256441 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_256441 : Nat := 118140960795 + 256441 * 2 ^ 59
def prefixEnd_256441 : Nat := 4983230072969 + 3 ^ 40 * 256441 * 2
def baseEnd_256441 : Nat := 117046660017543472985027

theorem tailTrace_256441 : CollatzResearch.WordTrace tailWord_256441 prefixEnd_256441 117046660017543472985027 := by
  unfold tailWord_256441
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353171663965528481081177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6235447775977018987387451 9353171663965528481081177)
  ·
    refine ⟨7014878747974146360810883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9353171663965528481081177 7014878747974146360810883)
    ·
      refine ⟨10522318121961219541216325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7014878747974146360810883 10522318121961219541216325)
      ·
        refine ⟨1972934647867728663978061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10522318121961219541216325 1972934647867728663978061)
        ·
          refine ⟨739850492950398248991773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1972934647867728663978061 739850492950398248991773)
          ·
            refine ⟨277443934856399343371915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 739850492950398248991773 277443934856399343371915)
            ·
              refine ⟨416165902284599015057873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277443934856399343371915 416165902284599015057873)
              ·
                refine ⟨312124426713449261293405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416165902284599015057873 312124426713449261293405)
                ·
                  refine ⟨117046660017543472985027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312124426713449261293405 117046660017543472985027)
                  ·
                    rfl

theorem cell20_256441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_256441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256441 prefixEnd_256441 := by exact prefixLift 256441
  have htrace : WordTrace (prefixWord ++ tailWord_256441) baseStart_256441 baseEnd_256441 := by
    simpa [prefixWord, tailWord_256441, baseEnd_256441] using wordTrace_append hprefix tailTrace_256441
  have hstable : (prefixWord ++ tailWord_256441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256441).length < 2 ^ (prefixWord ++ tailWord_256441).sum := by decide
  have hdescent : baseEnd_256441 < baseStart_256441 := by decide
  rcases family_descends (prefixWord ++ tailWord_256441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256459 : List Nat := [1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_256459 : Nat := 118140960795 + 256459 * 2 ^ 59
def prefixEnd_256459 : Nat := 4983230072969 + 3 ^ 40 * 256459 * 2
def baseEnd_256459 : Nat := 39018291902671803461651

theorem tailTrace_256459 : CollatzResearch.WordTrace tailWord_256459 prefixEnd_256459 39018291902671803461651 := by
  unfold tailWord_256459
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353828177900317555236431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6235885451933545036824287 9353828177900317555236431)
  ·
    refine ⟨14030742266850476332854647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353828177900317555236431 14030742266850476332854647)
    ·
      refine ⟨21046113400275714499281971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14030742266850476332854647 21046113400275714499281971)
      ·
        refine ⟨31569170100413571748922957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046113400275714499281971 31569170100413571748922957)
        ·
          refine ⟨11838438787655089405846109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31569170100413571748922957 11838438787655089405846109)
          ·
            refine ⟨4439414545370658527192291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11838438787655089405846109 4439414545370658527192291)
            ·
              refine ⟨6659121818055987790788437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439414545370658527192291 6659121818055987790788437)
              ·
                refine ⟨39018291902671803461651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6659121818055987790788437 39018291902671803461651)
                ·
                  rfl

theorem cell20_256459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_256459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256459 prefixEnd_256459 := by exact prefixLift 256459
  have htrace : WordTrace (prefixWord ++ tailWord_256459) baseStart_256459 baseEnd_256459 := by
    simpa [prefixWord, tailWord_256459, baseEnd_256459] using wordTrace_append hprefix tailTrace_256459
  have hstable : (prefixWord ++ tailWord_256459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256459).length < 2 ^ (prefixWord ++ tailWord_256459).sum := by decide
  have hdescent : baseEnd_256459 < baseStart_256459 := by decide
  rcases family_descends (prefixWord ++ tailWord_256459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256469 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_256469 : Nat := 118140960795 + 256469 * 2 ^ 59
def prefixEnd_256469 : Nat := 4983230072969 + 3 ^ 40 * 256469 * 2
def baseEnd_256469 : Nat := 117059439980499820051579

theorem tailTrace_256469 : CollatzResearch.WordTrace tailWord_256469 prefixEnd_256469 117059439980499820051579 := by
  unfold tailWord_256469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354192907864089263100461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6236128605242726175400307 9354192907864089263100461)
  ·
    refine ⟨3507822340449033473662673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9354192907864089263100461 3507822340449033473662673)
    ·
      refine ⟨2630866755336775105247005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507822340449033473662673 2630866755336775105247005)
      ·
        refine ⟨986575033251290664467627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2630866755336775105247005 986575033251290664467627)
        ·
          refine ⟨1479862549876935996701441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986575033251290664467627 1479862549876935996701441)
          ·
            refine ⟨1109896912407701997526081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479862549876935996701441 1109896912407701997526081)
            ·
              refine ⟨832422684305776498144561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109896912407701997526081 832422684305776498144561)
              ·
                refine ⟨624317013229332373608421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832422684305776498144561 624317013229332373608421)
                ·
                  refine ⟨117059439980499820051579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624317013229332373608421 117059439980499820051579)
                  ·
                    rfl

theorem cell20_256469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_256469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256469 prefixEnd_256469 := by exact prefixLift 256469
  have htrace : WordTrace (prefixWord ++ tailWord_256469) baseStart_256469 baseEnd_256469 := by
    simpa [prefixWord, tailWord_256469, baseEnd_256469] using wordTrace_append hprefix tailTrace_256469
  have hstable : (prefixWord ++ tailWord_256469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256469).length < 2 ^ (prefixWord ++ tailWord_256469).sum := by decide
  have hdescent : baseEnd_256469 < baseStart_256469 := by decide
  rcases family_descends (prefixWord ++ tailWord_256469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256493 : List Nat := [1, 5, 1, 3, 1, 3, 6]
def baseStart_256493 : Nat := 118140960795 + 256493 * 2 ^ 59
def prefixEnd_256493 : Nat := 4983230072969 + 3 ^ 40 * 256493 * 2
def baseEnd_256493 : Nat := 13007821581606933694609

theorem tailTrace_256493 : CollatzResearch.WordTrace tailWord_256493 prefixEnd_256493 13007821581606933694609 := by
  unfold tailWord_256493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355068259777141361974133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6236712173184760907982755 9355068259777141361974133)
  ·
    refine ⟨877037649354107002685075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9355068259777141361974133 877037649354107002685075)
    ·
      refine ⟨1315556474031160504027613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877037649354107002685075 1315556474031160504027613)
      ·
        refine ⟨493333677761685189010355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1315556474031160504027613 493333677761685189010355)
        ·
          refine ⟨740000516642527783515533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493333677761685189010355 740000516642527783515533)
          ·
            refine ⟨277500193740947918818325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740000516642527783515533 277500193740947918818325)
            ·
              refine ⟨13007821581606933694609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277500193740947918818325 13007821581606933694609)
              ·
                rfl

theorem cell20_256493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_256493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256493 prefixEnd_256493 := by exact prefixLift 256493
  have htrace : WordTrace (prefixWord ++ tailWord_256493) baseStart_256493 baseEnd_256493 := by
    simpa [prefixWord, tailWord_256493, baseEnd_256493] using wordTrace_append hprefix tailTrace_256493
  have hstable : (prefixWord ++ tailWord_256493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256493).length < 2 ^ (prefixWord ++ tailWord_256493).sum := by decide
  have hdescent : baseEnd_256493 < baseStart_256493 := by decide
  rcases family_descends (prefixWord ++ tailWord_256493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256552 : List Nat := [2, 1, 5, 2, 1, 9]
def baseStart_256552 : Nat := 118140960795 + 256552 * 2 ^ 59
def prefixEnd_256552 : Nat := 4983230072969 + 3 ^ 40 * 256552 * 2
def baseEnd_256552 : Nat := 4336937905263719269799

theorem tailTrace_256552 : CollatzResearch.WordTrace tailWord_256552 prefixEnd_256552 4336937905263719269799 := by
  unfold tailWord_256552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678610083281697219185955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6238146777708929625581273 4678610083281697219185955)
  ·
    refine ⟨7017915124922545828778933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4678610083281697219185955 7017915124922545828778933)
    ·
      refine ⟨657929542961488671448025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7017915124922545828778933 657929542961488671448025)
      ·
        refine ⟨493447157221116503586019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657929542961488671448025 493447157221116503586019)
        ·
          refine ⟨740170735831674755379029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493447157221116503586019 740170735831674755379029)
          ·
            refine ⟨4336937905263719269799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 740170735831674755379029 4336937905263719269799)
            ·
              rfl

theorem cell20_256552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 9].length) (baseStart_256552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256552 prefixEnd_256552 := by exact prefixLift 256552
  have htrace : WordTrace (prefixWord ++ tailWord_256552) baseStart_256552 baseEnd_256552 := by
    simpa [prefixWord, tailWord_256552, baseEnd_256552] using wordTrace_append hprefix tailTrace_256552
  have hstable : (prefixWord ++ tailWord_256552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256552).length < 2 ^ (prefixWord ++ tailWord_256552).sum := by decide
  have hdescent : baseEnd_256552 < baseStart_256552 := by decide
  rcases family_descends (prefixWord ++ tailWord_256552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256583 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_256583 : Nat := 118140960795 + 256583 * 2 ^ 59
def prefixEnd_256583 : Nat := 4983230072969 + 3 ^ 40 * 256583 * 2
def baseEnd_256583 : Nat := 117111472686822090251113

theorem tailTrace_256583 : CollatzResearch.WordTrace tailWord_256583 prefixEnd_256583 117111472686822090251113 := by
  unfold tailWord_256583
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358350829451086732750403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6238900552967391155166935 9358350829451086732750403)
  ·
    refine ⟨14037526244176630099125605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9358350829451086732750403 14037526244176630099125605)
    ·
      refine ⟨2632036170783118143586051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14037526244176630099125605 2632036170783118143586051)
      ·
        refine ⟨3948054256174677215379077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632036170783118143586051 3948054256174677215379077)
        ·
          refine ⟨740260173032751977883577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3948054256174677215379077 740260173032751977883577)
          ·
            refine ⟨555195129774563983412683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740260173032751977883577 555195129774563983412683)
            ·
              refine ⟨832792694661845975119025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555195129774563983412683 832792694661845975119025)
              ·
                refine ⟨624594520996384481339269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832792694661845975119025 624594520996384481339269)
                ·
                  refine ⟨117111472686822090251113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624594520996384481339269 117111472686822090251113)
                  ·
                    rfl

theorem cell20_256583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_256583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256583 prefixEnd_256583 := by exact prefixLift 256583
  have htrace : WordTrace (prefixWord ++ tailWord_256583) baseStart_256583 baseEnd_256583 := by
    simpa [prefixWord, tailWord_256583, baseEnd_256583] using wordTrace_append hprefix tailTrace_256583
  have hstable : (prefixWord ++ tailWord_256583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256583).length < 2 ^ (prefixWord ++ tailWord_256583).sum := by decide
  have hdescent : baseEnd_256583 < baseStart_256583 := by decide
  rcases family_descends (prefixWord ++ tailWord_256583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256606 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_256606 : Nat := 118140960795 + 256606 * 2 ^ 59
def prefixEnd_256606 : Nat := 4983230072969 + 3 ^ 40 * 256606 * 2
def baseEnd_256606 : Nat := 117121970513536232484353

theorem tailTrace_256606 : CollatzResearch.WordTrace tailWord_256606 prefixEnd_256606 117121970513536232484353 := by
  unfold tailWord_256606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169898713545970207604709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6239459805578507773891781 1169898713545970207604709)
  ·
    refine ⟨219356008789869413925883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1169898713545970207604709 219356008789869413925883)
    ·
      refine ⟨329034013184804120888825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219356008789869413925883 329034013184804120888825)
      ·
        refine ⟨246775509888603090666619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329034013184804120888825 246775509888603090666619)
        ·
          refine ⟨370163264832904635999929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246775509888603090666619 370163264832904635999929)
          ·
            refine ⟨277622448624678476999947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370163264832904635999929 277622448624678476999947)
            ·
              refine ⟨416433672937017715499921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277622448624678476999947 416433672937017715499921)
              ·
                refine ⟨312325254702763286624941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416433672937017715499921 312325254702763286624941)
                ·
                  refine ⟨117121970513536232484353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312325254702763286624941 117121970513536232484353)
                  ·
                    rfl

theorem cell20_256606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_256606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256606 prefixEnd_256606 := by exact prefixLift 256606
  have htrace : WordTrace (prefixWord ++ tailWord_256606) baseStart_256606 baseEnd_256606 := by
    simpa [prefixWord, tailWord_256606, baseEnd_256606] using wordTrace_append hprefix tailTrace_256606
  have hstable : (prefixWord ++ tailWord_256606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256606).length < 2 ^ (prefixWord ++ tailWord_256606).sum := by decide
  have hdescent : baseEnd_256606 < baseStart_256606 := by decide
  rcases family_descends (prefixWord ++ tailWord_256606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256611 : List Nat := [1, 1, 1, 5, 1, 2, 9]
def baseStart_256611 : Nat := 118140960795 + 256611 * 2 ^ 59
def prefixEnd_256611 : Nat := 4983230072969 + 3 ^ 40 * 256611 * 2
def baseEnd_256611 : Nat := 13013805849975381924185

theorem tailTrace_256611 : CollatzResearch.WordTrace tailWord_256611 prefixEnd_256611 13013805849975381924185 := by
  unfold tailWord_256611
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359372073349647514769687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6239581382233098343179791 9359372073349647514769687)
  ·
    refine ⟨14039058110024471272154531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9359372073349647514769687 14039058110024471272154531)
    ·
      refine ⟨21058587165036706908231797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039058110024471272154531 21058587165036706908231797)
      ·
        refine ⟨1974242546722191272646731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21058587165036706908231797 1974242546722191272646731)
        ·
          refine ⟨2961363820083286908970097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974242546722191272646731 2961363820083286908970097)
          ·
            refine ⟨2221022865062465181727573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961363820083286908970097 2221022865062465181727573)
            ·
              refine ⟨13013805849975381924185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2221022865062465181727573 13013805849975381924185)
              ·
                rfl

theorem cell20_256611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_256611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256611 prefixEnd_256611 := by exact prefixLift 256611
  have htrace : WordTrace (prefixWord ++ tailWord_256611) baseStart_256611 baseEnd_256611 := by
    simpa [prefixWord, tailWord_256611, baseEnd_256611] using wordTrace_append hprefix tailTrace_256611
  have hstable : (prefixWord ++ tailWord_256611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256611).length < 2 ^ (prefixWord ++ tailWord_256611).sum := by decide
  have hdescent : baseEnd_256611 < baseStart_256611 := by decide
  rcases family_descends (prefixWord ++ tailWord_256611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256621 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_256621 : Nat := 118140960795 + 256621 * 2 ^ 59
def prefixEnd_256621 : Nat := 4983230072969 + 3 ^ 40 * 256621 * 2
def baseEnd_256621 : Nat := 117128816922262846984291

theorem tailTrace_256621 : CollatzResearch.WordTrace tailWord_256621 prefixEnd_256621 117128816922262846984291 := by
  unfold tailWord_256621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359736803313419222633717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6239824535542279481755811 9359736803313419222633717)
  ·
    refine ⟨877475325310633052121911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9359736803313419222633717 877475325310633052121911)
    ·
      refine ⟨1316212987965949578182867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877475325310633052121911 1316212987965949578182867)
      ·
        refine ⟨1974319481948924367274301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316212987965949578182867 1974319481948924367274301)
        ·
          refine ⟨740369805730846637727863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1974319481948924367274301 740369805730846637727863)
          ·
            refine ⟨1110554708596269956591795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740369805730846637727863 1110554708596269956591795)
            ·
              refine ⟨1665832062894404934887693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110554708596269956591795 1665832062894404934887693)
              ·
                refine ⟨624687023585401850582885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665832062894404934887693 624687023585401850582885)
                ·
                  refine ⟨117128816922262846984291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624687023585401850582885 117128816922262846984291)
                  ·
                    rfl

theorem cell20_256621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_256621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256621 prefixEnd_256621 := by exact prefixLift 256621
  have htrace : WordTrace (prefixWord ++ tailWord_256621) baseStart_256621 baseEnd_256621 := by
    simpa [prefixWord, tailWord_256621, baseEnd_256621] using wordTrace_append hprefix tailTrace_256621
  have hstable : (prefixWord ++ tailWord_256621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256621).length < 2 ^ (prefixWord ++ tailWord_256621).sum := by decide
  have hdescent : baseEnd_256621 < baseStart_256621 := by decide
  rcases family_descends (prefixWord ++ tailWord_256621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256645 : List Nat := [1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_256645 : Nat := 118140960795 + 256645 * 2 ^ 59
def prefixEnd_256645 : Nat := 4983230072969 + 3 ^ 40 * 256645 * 2
def baseEnd_256645 : Nat := 39046590392075143394731

theorem tailTrace_256645 : CollatzResearch.WordTrace tailWord_256645 prefixEnd_256645 39046590392075143394731 := by
  unfold tailWord_256645
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360612155226471321507389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6240408103484314214338259 9360612155226471321507389)
  ·
    refine ⟨3510229558209926745565271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9360612155226471321507389 3510229558209926745565271)
    ·
      refine ⟨5265344337314890118347907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510229558209926745565271 5265344337314890118347907)
      ·
        refine ⟨7898016505972335177521861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265344337314890118347907 7898016505972335177521861)
        ·
          refine ⟨1480878094869812845785349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7898016505972335177521861 1480878094869812845785349)
          ·
            refine ⟨277664642788089908584753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1480878094869812845785349 277664642788089908584753)
            ·
              refine ⟨208248482091067431438565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277664642788089908584753 208248482091067431438565)
              ·
                refine ⟨39046590392075143394731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208248482091067431438565 39046590392075143394731)
                ·
                  rfl

theorem cell20_256645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_256645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256645 prefixEnd_256645 := by exact prefixLift 256645
  have htrace : WordTrace (prefixWord ++ tailWord_256645) baseStart_256645 baseEnd_256645 := by
    simpa [prefixWord, tailWord_256645, baseEnd_256645] using wordTrace_append hprefix tailTrace_256645
  have hstable : (prefixWord ++ tailWord_256645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256645).length < 2 ^ (prefixWord ++ tailWord_256645).sum := by decide
  have hdescent : baseEnd_256645 < baseStart_256645 := by decide
  rcases family_descends (prefixWord ++ tailWord_256645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256682 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_256682 : Nat := 118140960795 + 256682 * 2 ^ 59
def prefixEnd_256682 : Nat := 4983230072969 + 3 ^ 40 * 256682 * 2
def baseEnd_256682 : Nat := 117156658984417745950709

theorem tailTrace_256682 : CollatzResearch.WordTrace tailWord_256682 prefixEnd_256682 117156658984417745950709 := by
  unfold tailWord_256682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340490414023106660151075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6241307770728284427069533 2340490414023106660151075)
  ·
    refine ⟨3510735621034659990226613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340490414023106660151075 3510735621034659990226613)
    ·
      refine ⟨329131464471999374083745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3510735621034659990226613 329131464471999374083745)
      ·
        refine ⟨246848598353999530562809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329131464471999374083745 246848598353999530562809)
        ·
          refine ⟨185136448765499647922107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246848598353999530562809 185136448765499647922107)
          ·
            refine ⟨277704673148249471883161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185136448765499647922107 277704673148249471883161)
            ·
              refine ⟨208278504861187103912371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277704673148249471883161 208278504861187103912371)
              ·
                refine ⟨312417757291780655868557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208278504861187103912371 312417757291780655868557)
                ·
                  refine ⟨117156658984417745950709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312417757291780655868557 117156658984417745950709)
                  ·
                    rfl

theorem cell20_256682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_256682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256682 prefixEnd_256682 := by exact prefixLift 256682
  have htrace : WordTrace (prefixWord ++ tailWord_256682) baseStart_256682 baseEnd_256682 := by
    simpa [prefixWord, tailWord_256682, baseEnd_256682] using wordTrace_append hprefix tailTrace_256682
  have hstable : (prefixWord ++ tailWord_256682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256682).length < 2 ^ (prefixWord ++ tailWord_256682).sum := by decide
  have hdescent : baseEnd_256682 < baseStart_256682 := by decide
  rcases family_descends (prefixWord ++ tailWord_256682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256686 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_256686 : Nat := 118140960795 + 256686 * 2 ^ 59
def prefixEnd_256686 : Nat := 4983230072969 + 3 ^ 40 * 256686 * 2
def baseEnd_256686 : Nat := 117158484693411509817359

theorem tailTrace_256686 : CollatzResearch.WordTrace tailWord_256686 prefixEnd_256686 117158484693411509817359 := by
  unfold tailWord_256686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170263443509741915468739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6241405032051956882499941 1170263443509741915468739)
  ·
    refine ⟨1755395165264612873203109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1170263443509741915468739 1755395165264612873203109)
    ·
      refine ⟨329136593487114913725583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1755395165264612873203109 329136593487114913725583)
      ·
        refine ⟨493704890230672370588375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329136593487114913725583 493704890230672370588375)
        ·
          refine ⟨740557335346008555882563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493704890230672370588375 740557335346008555882563)
          ·
            refine ⟨1110836003019012833823845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740557335346008555882563 1110836003019012833823845)
            ·
              refine ⟨208281750566064906341971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1110836003019012833823845 208281750566064906341971)
              ·
                refine ⟨312422625849097359512957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208281750566064906341971 312422625849097359512957)
                ·
                  refine ⟨117158484693411509817359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312422625849097359512957 117158484693411509817359)
                  ·
                    rfl

theorem cell20_256686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_256686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256686 prefixEnd_256686 := by exact prefixLift 256686
  have htrace : WordTrace (prefixWord ++ tailWord_256686) baseStart_256686 baseEnd_256686 := by
    simpa [prefixWord, tailWord_256686, baseEnd_256686] using wordTrace_append hprefix tailTrace_256686
  have hstable : (prefixWord ++ tailWord_256686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256686).length < 2 ^ (prefixWord ++ tailWord_256686).sum := by decide
  have hdescent : baseEnd_256686 < baseStart_256686 := by decide
  rcases family_descends (prefixWord ++ tailWord_256686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256687 : List Nat := [1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_256687 : Nat := 118140960795 + 256687 * 2 ^ 59
def prefixEnd_256687 : Nat := 4983230072969 + 3 ^ 40 * 256687 * 2
def baseEnd_256687 : Nat := 39052980373553316928007

theorem tailTrace_256687 : CollatzResearch.WordTrace tailWord_256687 prefixEnd_256687 39052980373553316928007 := by
  unfold tailWord_256687
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362144021074312494536315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6241429347382874996357543 9362144021074312494536315)
  ·
    refine ⟨14043216031611468741804473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362144021074312494536315 14043216031611468741804473)
    ·
      refine ⟨10532412023708601556353355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14043216031611468741804473 10532412023708601556353355)
      ·
        refine ⟨15798618035562902334530033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532412023708601556353355 15798618035562902334530033)
        ·
          refine ⟨11848963526672176750897525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15798618035562902334530033 11848963526672176750897525)
          ·
            refine ⟨1110840330625516570396643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11848963526672176750897525 1110840330625516570396643)
            ·
              refine ⟨1666260495938274855594965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110840330625516570396643 1666260495938274855594965)
              ·
                refine ⟨39052980373553316928007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1666260495938274855594965 39052980373553316928007)
                ·
                  rfl

theorem cell20_256687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_256687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256687 prefixEnd_256687 := by exact prefixLift 256687
  have htrace : WordTrace (prefixWord ++ tailWord_256687) baseStart_256687 baseEnd_256687 := by
    simpa [prefixWord, tailWord_256687, baseEnd_256687] using wordTrace_append hprefix tailTrace_256687
  have hstable : (prefixWord ++ tailWord_256687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256687).length < 2 ^ (prefixWord ++ tailWord_256687).sum := by decide
  have hdescent : baseEnd_256687 < baseStart_256687 := by decide
  rcases family_descends (prefixWord ++ tailWord_256687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256728 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_256728 : Nat := 118140960795 + 256728 * 2 ^ 59
def prefixEnd_256728 : Nat := 4983230072969 + 3 ^ 40 * 256728 * 2
def baseEnd_256728 : Nat := 117177654637846030417187

theorem tailTrace_256728 : CollatzResearch.WordTrace tailWord_256728 prefixEnd_256728 117177654637846030417187 := by
  unfold tailWord_256728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681819706962888248389419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6242426275950517664519225 4681819706962888248389419)
  ·
    refine ⟨7022729560444332372584129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4681819706962888248389419 7022729560444332372584129)
    ·
      refine ⟨5267047170333249279438097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7022729560444332372584129 5267047170333249279438097)
      ·
        refine ⟨3950285377749936959578573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267047170333249279438097 3950285377749936959578573)
        ·
          refine ⟨1481357016656226359841965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3950285377749936959578573 1481357016656226359841965)
          ·
            refine ⟨555508881246084884940737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1481357016656226359841965 555508881246084884940737)
            ·
              refine ⟨416631660934563663705553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555508881246084884940737 416631660934563663705553)
              ·
                refine ⟨312473745700922747779165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416631660934563663705553 312473745700922747779165)
                ·
                  refine ⟨117177654637846030417187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312473745700922747779165 117177654637846030417187)
                  ·
                    rfl

theorem cell20_256728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_256728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256728 prefixEnd_256728 := by exact prefixLift 256728
  have htrace : WordTrace (prefixWord ++ tailWord_256728) baseStart_256728 baseEnd_256728 := by
    simpa [prefixWord, tailWord_256728, baseEnd_256728] using wordTrace_append hprefix tailTrace_256728
  have hstable : (prefixWord ++ tailWord_256728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256728).length < 2 ^ (prefixWord ++ tailWord_256728).sum := by decide
  have hdescent : baseEnd_256728 < baseStart_256728 := by decide
  rcases family_descends (prefixWord ++ tailWord_256728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256801 : List Nat := [1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_256801 : Nat := 118140960795 + 256801 * 2 ^ 59
def prefixEnd_256801 : Nat := 4983230072969 + 3 ^ 40 * 256801 * 2
def baseEnd_256801 : Nat := 39070324608994073661185

theorem tailTrace_256801 : CollatzResearch.WordTrace tailWord_256801 prefixEnd_256801 39070324608994073661185 := by
  unfold tailWord_256801
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366301942661309964186257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6244201295107539976124171 9366301942661309964186257)
  ·
    refine ⟨7024726456995982473139693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9366301942661309964186257 7024726456995982473139693)
    ·
      refine ⟨2634272421373493427427385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7024726456995982473139693 2634272421373493427427385)
      ·
        refine ⟨1975704316030120070570539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2634272421373493427427385 1975704316030120070570539)
        ·
          refine ⟨2963556474045180105855809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975704316030120070570539 2963556474045180105855809)
          ·
            refine ⟨2222667355533885079391857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963556474045180105855809 2222667355533885079391857)
            ·
              refine ⟨1667000516650413809543893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222667355533885079391857 1667000516650413809543893)
              ·
                refine ⟨39070324608994073661185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1667000516650413809543893 39070324608994073661185)
                ·
                  rfl

theorem cell20_256801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_256801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256801 prefixEnd_256801 := by exact prefixLift 256801
  have htrace : WordTrace (prefixWord ++ tailWord_256801) baseStart_256801 baseEnd_256801 := by
    simpa [prefixWord, tailWord_256801, baseEnd_256801] using wordTrace_append hprefix tailTrace_256801
  have hstable : (prefixWord ++ tailWord_256801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256801).length < 2 ^ (prefixWord ++ tailWord_256801).sum := by decide
  have hdescent : baseEnd_256801 < baseStart_256801 := by decide
  rcases family_descends (prefixWord ++ tailWord_256801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256814 : List Nat := [4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_256814 : Nat := 118140960795 + 256814 * 2 ^ 59
def prefixEnd_256814 : Nat := 4983230072969 + 3 ^ 40 * 256814 * 2
def baseEnd_256814 : Nat := 39072302460403984516723

theorem tailTrace_256814 : CollatzResearch.WordTrace tailWord_256814 prefixEnd_256814 39072302460403984516723 := by
  unfold tailWord_256814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170847011451776648051187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6244517394409475456272997 1170847011451776648051187)
  ·
    refine ⟨1756270517177664972076781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1170847011451776648051187 1756270517177664972076781)
    ·
      refine ⟨658601443941624364528793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1756270517177664972076781 658601443941624364528793)
      ·
        refine ⟨493951082956218273396595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658601443941624364528793 493951082956218273396595)
        ·
          refine ⟨740926624434327410094893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493951082956218273396595 740926624434327410094893)
          ·
            refine ⟨277847484162872778785585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740926624434327410094893 277847484162872778785585)
            ·
              refine ⟨208385613122154584089189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277847484162872778785585 208385613122154584089189)
              ·
                refine ⟨39072302460403984516723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208385613122154584089189 39072302460403984516723)
                ·
                  rfl

theorem cell20_256814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_256814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256814 prefixEnd_256814 := by exact prefixLift 256814
  have htrace : WordTrace (prefixWord ++ tailWord_256814) baseStart_256814 baseEnd_256814 := by
    simpa [prefixWord, tailWord_256814, baseEnd_256814] using wordTrace_append hprefix tailTrace_256814
  have hstable : (prefixWord ++ tailWord_256814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256814).length < 2 ^ (prefixWord ++ tailWord_256814).sum := by decide
  have hdescent : baseEnd_256814 < baseStart_256814 := by decide
  rcases family_descends (prefixWord ++ tailWord_256814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256845 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_256845 : Nat := 118140960795 + 256845 * 2 ^ 59
def prefixEnd_256845 : Nat := 4983230072969 + 3 ^ 40 * 256845 * 2
def baseEnd_256845 : Nat := 117231056625913623516709

theorem tailTrace_256845 : CollatzResearch.WordTrace tailWord_256845 prefixEnd_256845 117231056625913623516709 := by
  unfold tailWord_256845
  simp only [CollatzResearch.WordTrace]
  refine ⟨9367906754501905478787989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6245271169667936985858659 9367906754501905478787989)
  ·
    refine ⟨439120629117276819318187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9367906754501905478787989 439120629117276819318187)
    ·
      refine ⟨658680943675915228977281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439120629117276819318187 658680943675915228977281)
      ·
        refine ⟨494010707756936421732961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658680943675915228977281 494010707756936421732961)
        ·
          refine ⟨370508030817702316299721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494010707756936421732961 370508030817702316299721)
          ·
            refine ⟨277881023113276737224791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370508030817702316299721 277881023113276737224791)
            ·
              refine ⟨416821534669915105837187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277881023113276737224791 416821534669915105837187)
              ·
                refine ⟨625232302004872658755781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416821534669915105837187 625232302004872658755781)
                ·
                  refine ⟨117231056625913623516709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625232302004872658755781 117231056625913623516709)
                  ·
                    rfl

theorem cell20_256845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_256845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256845 prefixEnd_256845 := by exact prefixLift 256845
  have htrace : WordTrace (prefixWord ++ tailWord_256845) baseStart_256845 baseEnd_256845 := by
    simpa [prefixWord, tailWord_256845, baseEnd_256845] using wordTrace_append hprefix tailTrace_256845
  have hstable : (prefixWord ++ tailWord_256845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256845).length < 2 ^ (prefixWord ++ tailWord_256845).sum := by decide
  have hdescent : baseEnd_256845 < baseStart_256845 := by decide
  rcases family_descends (prefixWord ++ tailWord_256845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256863 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_256863 : Nat := 118140960795 + 256863 * 2 ^ 59
def prefixEnd_256863 : Nat := 4983230072969 + 3 ^ 40 * 256863 * 2
def baseEnd_256863 : Nat := 117239272316385560916635

theorem tailTrace_256863 : CollatzResearch.WordTrace tailWord_256863 prefixEnd_256863 117239272316385560916635 := by
  unfold tailWord_256863
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368563268436694552943243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6245708845624463035295495 9368563268436694552943243)
  ·
    refine ⟨14052844902655041829414865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9368563268436694552943243 14052844902655041829414865)
    ·
      refine ⟨10539633676991281372061149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14052844902655041829414865 10539633676991281372061149)
      ·
        refine ⟨3952362628871730514522931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10539633676991281372061149 3952362628871730514522931)
        ·
          refine ⟨5928543943307595771784397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952362628871730514522931 5928543943307595771784397)
          ·
            refine ⟨2223203978740348414419149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5928543943307595771784397 2223203978740348414419149)
            ·
              refine ⟨833701492027630655407181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2223203978740348414419149 833701492027630655407181)
              ·
                refine ⟨312638059510361495777693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833701492027630655407181 312638059510361495777693)
                ·
                  refine ⟨117239272316385560916635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312638059510361495777693 117239272316385560916635)
                  ·
                    rfl

theorem cell20_256863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_256863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256863 prefixEnd_256863 := by exact prefixLift 256863
  have htrace : WordTrace (prefixWord ++ tailWord_256863) baseStart_256863 baseEnd_256863 := by
    simpa [prefixWord, tailWord_256863, baseEnd_256863] using wordTrace_append hprefix tailTrace_256863
  have hstable : (prefixWord ++ tailWord_256863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256863).length < 2 ^ (prefixWord ++ tailWord_256863).sum := by decide
  have hdescent : baseEnd_256863 < baseStart_256863 := by decide
  rcases family_descends (prefixWord ++ tailWord_256863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256894 : List Nat := [4, 2, 3, 1, 10]
def baseStart_256894 : Nat := 118140960795 + 256894 * 2 ^ 59
def prefixEnd_256894 : Nat := 4983230072969 + 3 ^ 40 * 256894 * 2
def baseEnd_256894 : Nat := 1447573105692434949175

theorem tailTrace_256894 : CollatzResearch.WordTrace tailWord_256894 prefixEnd_256894 1447573105692434949175 := by
  unfold tailWord_256894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171211741415548355915217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6246462620882924564881157 1171211741415548355915217)
  ·
    refine ⟨878408806061661266936413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1171211741415548355915217 878408806061661266936413)
    ·
      refine ⟨329403302273122975101155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 878408806061661266936413 329403302273122975101155)
      ·
        refine ⟨494104953409684462651733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329403302273122975101155 494104953409684462651733)
        ·
          refine ⟨1447573105692434949175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 494104953409684462651733 1447573105692434949175)
          ·
            rfl

theorem cell20_256894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 10].length) (baseStart_256894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256894 prefixEnd_256894 := by exact prefixLift 256894
  have htrace : WordTrace (prefixWord ++ tailWord_256894) baseStart_256894 baseEnd_256894 := by
    simpa [prefixWord, tailWord_256894, baseEnd_256894] using wordTrace_append hprefix tailTrace_256894
  have hstable : (prefixWord ++ tailWord_256894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256894).length < 2 ^ (prefixWord ++ tailWord_256894).sum := by decide
  have hdescent : baseEnd_256894 < baseStart_256894 := by decide
  rcases family_descends (prefixWord ++ tailWord_256894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256901 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_256901 : Nat := 118140960795 + 256901 * 2 ^ 59
def prefixEnd_256901 : Nat := 4983230072969 + 3 ^ 40 * 256901 * 2
def baseEnd_256901 : Nat := 117256616551826317649813

theorem tailTrace_256901 : CollatzResearch.WordTrace tailWord_256901 prefixEnd_256901 117256616551826317649813 := by
  unfold tailWord_256901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369949242299027042826557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6246632828199351361884371 9369949242299027042826557)
  ·
    refine ⟨3513730965862135141059959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9369949242299027042826557 3513730965862135141059959)
    ·
      refine ⟨5270596448793202711589939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513730965862135141059959 5270596448793202711589939)
      ·
        refine ⟨7905894673189804067384909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270596448793202711589939 7905894673189804067384909)
        ·
          refine ⟨2964710502446176525269341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7905894673189804067384909 2964710502446176525269341)
          ·
            refine ⟨1111766438417316196976003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2964710502446176525269341 1111766438417316196976003)
            ·
              refine ⟨1667649657625974295464005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111766438417316196976003 1667649657625974295464005)
              ·
                refine ⟨312684310804870180399501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1667649657625974295464005 312684310804870180399501)
                ·
                  refine ⟨117256616551826317649813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312684310804870180399501 117256616551826317649813)
                  ·
                    rfl

theorem cell20_256901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_256901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256901 prefixEnd_256901 := by exact prefixLift 256901
  have htrace : WordTrace (prefixWord ++ tailWord_256901) baseStart_256901 baseEnd_256901 := by
    simpa [prefixWord, tailWord_256901, baseEnd_256901] using wordTrace_append hprefix tailTrace_256901
  have hstable : (prefixWord ++ tailWord_256901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256901).length < 2 ^ (prefixWord ++ tailWord_256901).sum := by decide
  have hdescent : baseEnd_256901 < baseStart_256901 := by decide
  rcases family_descends (prefixWord ++ tailWord_256901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256904 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_256904 : Nat := 118140960795 + 256904 * 2 ^ 59
def prefixEnd_256904 : Nat := 4983230072969 + 3 ^ 40 * 256904 * 2
def baseEnd_256904 : Nat := 117257985833571640549801

theorem tailTrace_256904 : CollatzResearch.WordTrace tailWord_256904 prefixEnd_256904 117257985833571640549801 := by
  unfold tailWord_256904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685029330644079277592883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6246705774192105703457177 4685029330644079277592883)
  ·
    refine ⟨7027543995966118916389325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685029330644079277592883 7027543995966118916389325)
    ·
      refine ⟨2635328998487294593645997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7027543995966118916389325 2635328998487294593645997)
      ·
        refine ⟨988248374432735472617249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2635328998487294593645997 988248374432735472617249)
        ·
          refine ⟨741186280824551604462937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988248374432735472617249 741186280824551604462937)
          ·
            refine ⟨555889710618413703347203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741186280824551604462937 555889710618413703347203)
            ·
              refine ⟨833834565927620555020805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555889710618413703347203 833834565927620555020805)
              ·
                refine ⟨156343981111428854066401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833834565927620555020805 156343981111428854066401)
                ·
                  refine ⟨117257985833571640549801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156343981111428854066401 117257985833571640549801)
                  ·
                    rfl

theorem cell20_256904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_256904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256904 prefixEnd_256904 := by exact prefixLift 256904
  have htrace : WordTrace (prefixWord ++ tailWord_256904) baseStart_256904 baseEnd_256904 := by
    simpa [prefixWord, tailWord_256904, baseEnd_256904] using wordTrace_append hprefix tailTrace_256904
  have hstable : (prefixWord ++ tailWord_256904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256904).length < 2 ^ (prefixWord ++ tailWord_256904).sum := by decide
  have hdescent : baseEnd_256904 < baseStart_256904 := by decide
  rcases family_descends (prefixWord ++ tailWord_256904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256932 : List Nat := [2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_256932 : Nat := 118140960795 + 256932 * 2 ^ 59
def prefixEnd_256932 : Nat := 4983230072969 + 3 ^ 40 * 256932 * 2
def baseEnd_256932 : Nat := 39090255265509329205451

theorem tailTrace_256932 : CollatzResearch.WordTrace tailWord_256932 prefixEnd_256932 39090255265509329205451 := by
  unfold tailWord_256932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685539952593359668602525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6247386603457812891470033 4685539952593359668602525)
  ·
    refine ⟨1757077482222509875725947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4685539952593359668602525 1757077482222509875725947)
    ·
      refine ⟨2635616223333764813588921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757077482222509875725947 2635616223333764813588921)
      ·
        refine ⟨1976712167500323610191691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2635616223333764813588921 1976712167500323610191691)
        ·
          refine ⟨2965068251250485415287537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976712167500323610191691 2965068251250485415287537)
          ·
            refine ⟨2223801188437864061465653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965068251250485415287537 2223801188437864061465653)
            ·
              refine ⟨208481361416049755762405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2223801188437864061465653 208481361416049755762405)
              ·
                refine ⟨39090255265509329205451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208481361416049755762405 39090255265509329205451)
                ·
                  rfl

theorem cell20_256932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_256932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256932 prefixEnd_256932 := by exact prefixLift 256932
  have htrace : WordTrace (prefixWord ++ tailWord_256932) baseStart_256932 baseEnd_256932 := by
    simpa [prefixWord, tailWord_256932, baseEnd_256932] using wordTrace_append hprefix tailTrace_256932
  have hstable : (prefixWord ++ tailWord_256932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256932).length < 2 ^ (prefixWord ++ tailWord_256932).sum := by decide
  have hdescent : baseEnd_256932 < baseStart_256932 := by decide
  rcases family_descends (prefixWord ++ tailWord_256932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256953 : List Nat := [1, 2, 1, 4, 2, 3, 7]
def baseStart_256953 : Nat := 118140960795 + 256953 * 2 ^ 59
def prefixEnd_256953 : Nat := 4983230072969 + 3 ^ 40 * 256953 * 2
def baseEnd_256953 : Nat := 13031150085416138657363

theorem tailTrace_256953 : CollatzResearch.WordTrace tailWord_256953 prefixEnd_256953 13031150085416138657363 := by
  unfold tailWord_256953
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371845838110639923719513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6247897225407093282479675 9371845838110639923719513)
  ·
    refine ⟨7028884378582979942789635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9371845838110639923719513 7028884378582979942789635)
    ·
      refine ⟨10543326567874469914184453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028884378582979942789635 10543326567874469914184453)
      ·
        refine ⟨1976873731476463108909585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10543326567874469914184453 1976873731476463108909585)
        ·
          refine ⟨1482655298607347331682189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976873731476463108909585 1482655298607347331682189)
          ·
            refine ⟨555995736977755249380821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1482655298607347331682189 555995736977755249380821)
            ·
              refine ⟨13031150085416138657363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 555995736977755249380821 13031150085416138657363)
              ·
                rfl

theorem cell20_256953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_256953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256953 prefixEnd_256953 := by exact prefixLift 256953
  have htrace : WordTrace (prefixWord ++ tailWord_256953) baseStart_256953 baseEnd_256953 := by
    simpa [prefixWord, tailWord_256953, baseEnd_256953] using wordTrace_append hprefix tailTrace_256953
  have hstable : (prefixWord ++ tailWord_256953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256953).length < 2 ^ (prefixWord ++ tailWord_256953).sum := by decide
  have hdescent : baseEnd_256953 < baseStart_256953 := by decide
  rcases family_descends (prefixWord ++ tailWord_256953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256984 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_256984 : Nat := 118140960795 + 256984 * 2 ^ 59
def prefixEnd_256984 : Nat := 4983230072969 + 3 ^ 40 * 256984 * 2
def baseEnd_256984 : Nat := 117294500013446917882807

theorem tailTrace_256984 : CollatzResearch.WordTrace tailWord_256984 prefixEnd_256984 117294500013446917882807 := by
  unfold tailWord_256984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686488250499166109049003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6248651000665554812065337 4686488250499166109049003)
  ·
    refine ⟨7029732375748749163573505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686488250499166109049003 7029732375748749163573505)
    ·
      refine ⟨5272299281811561872680129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7029732375748749163573505 5272299281811561872680129)
      ·
        refine ⟨3954224461358671404510097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272299281811561872680129 3954224461358671404510097)
        ·
          refine ⟨2965668346019003553382573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3954224461358671404510097 2965668346019003553382573)
          ·
            refine ⟨1112125629757126332518465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2965668346019003553382573 1112125629757126332518465)
            ·
              refine ⟨834094222317844749388849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112125629757126332518465 834094222317844749388849)
              ·
                refine ⟨625570666738383562041637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834094222317844749388849 625570666738383562041637)
                ·
                  refine ⟨117294500013446917882807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625570666738383562041637 117294500013446917882807)
                  ·
                    rfl

theorem cell20_256984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_256984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256984 prefixEnd_256984 := by exact prefixLift 256984
  have htrace : WordTrace (prefixWord ++ tailWord_256984) baseStart_256984 baseEnd_256984 := by
    simpa [prefixWord, tailWord_256984, baseEnd_256984] using wordTrace_append hprefix tailTrace_256984
  have hstable : (prefixWord ++ tailWord_256984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256984).length < 2 ^ (prefixWord ++ tailWord_256984).sum := by decide
  have hdescent : baseEnd_256984 < baseStart_256984 := by decide
  rcases family_descends (prefixWord ++ tailWord_256984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256994 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_256994 : Nat := 118140960795 + 256994 * 2 ^ 59
def prefixEnd_256994 : Nat := 4983230072969 + 3 ^ 40 * 256994 * 2
def baseEnd_256994 : Nat := 117299064285931327549433

theorem tailTrace_256994 : CollatzResearch.WordTrace tailWord_256994 prefixEnd_256994 117299064285931327549433 := by
  unfold tailWord_256994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343335307740525981490509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6248894153974735950641357 2343335307740525981490509)
  ·
    refine ⟨878750740402697243058941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2343335307740525981490509 878750740402697243058941)
    ·
      refine ⟨329531527651011466147103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 878750740402697243058941 329531527651011466147103)
      ·
        refine ⟨494297291476517199220655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329531527651011466147103 494297291476517199220655)
        ·
          refine ⟨741445937214775798830983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494297291476517199220655 741445937214775798830983)
          ·
            refine ⟨1112168905822163698246475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741445937214775798830983 1112168905822163698246475)
            ·
              refine ⟨1668253358733245547369713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112168905822163698246475 1668253358733245547369713)
              ·
                refine ⟨1251190019049934160527285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668253358733245547369713 1251190019049934160527285)
                ·
                  refine ⟨117299064285931327549433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251190019049934160527285 117299064285931327549433)
                  ·
                    rfl

theorem cell20_256994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_256994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_256994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_256994 prefixEnd_256994 := by exact prefixLift 256994
  have htrace : WordTrace (prefixWord ++ tailWord_256994) baseStart_256994 baseEnd_256994 := by
    simpa [prefixWord, tailWord_256994, baseEnd_256994] using wordTrace_append hprefix tailTrace_256994
  have hstable : (prefixWord ++ tailWord_256994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256994).length < 2 ^ (prefixWord ++ tailWord_256994).sum := by decide
  have hdescent : baseEnd_256994 < baseStart_256994 := by decide
  rcases family_descends (prefixWord ++ tailWord_256994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257029 : List Nat := [1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_257029 : Nat := 118140960795 + 257029 * 2 ^ 59
def prefixEnd_257029 : Nat := 4983230072969 + 3 ^ 40 * 257029 * 2
def baseEnd_257029 : Nat := 39105013079875587127541

theorem tailTrace_257029 : CollatzResearch.WordTrace tailWord_257029 prefixEnd_257029 39105013079875587127541 := by
  unfold tailWord_257029
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374617785835304903486141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6249745190556869935657427 9374617785835304903486141)
  ·
    refine ⟨3515481669688239338807303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9374617785835304903486141 3515481669688239338807303)
    ·
      refine ⟨5273222504532359008210955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515481669688239338807303 5273222504532359008210955)
      ·
        refine ⟨7909833756798538512316433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5273222504532359008210955 7909833756798538512316433)
        ·
          refine ⟨5932375317598903884237325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7909833756798538512316433 5932375317598903884237325)
          ·
            refine ⟨2224640744099588956588997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5932375317598903884237325 2224640744099588956588997)
            ·
              refine ⟨417120139518672929360437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2224640744099588956588997 417120139518672929360437)
              ·
                refine ⟨39105013079875587127541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417120139518672929360437 39105013079875587127541)
                ·
                  rfl

theorem cell20_257029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_257029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257029 prefixEnd_257029 := by exact prefixLift 257029
  have htrace : WordTrace (prefixWord ++ tailWord_257029) baseStart_257029 baseEnd_257029 := by
    simpa [prefixWord, tailWord_257029, baseEnd_257029] using wordTrace_append hprefix tailTrace_257029
  have hstable : (prefixWord ++ tailWord_257029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257029).length < 2 ^ (prefixWord ++ tailWord_257029).sum := by decide
  have hdescent : baseEnd_257029 < baseStart_257029 := by decide
  rcases family_descends (prefixWord ++ tailWord_257029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257032 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_257032 : Nat := 118140960795 + 257032 * 2 ^ 59
def prefixEnd_257032 : Nat := 4983230072969 + 3 ^ 40 * 257032 * 2
def baseEnd_257032 : Nat := 117316408521372084282611

theorem tailTrace_257032 : CollatzResearch.WordTrace tailWord_257032 prefixEnd_257032 117316408521372084282611 := by
  unfold tailWord_257032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687363602412218207922675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6249818136549624277230233 4687363602412218207922675)
  ·
    refine ⟨7031045403618327311884013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687363602412218207922675 7031045403618327311884013)
    ·
      refine ⟨2636642026356872741956505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7031045403618327311884013 2636642026356872741956505)
      ·
        refine ⟨1977481519767654556467379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2636642026356872741956505 1977481519767654556467379)
        ·
          refine ⟨2966222279651481834701069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977481519767654556467379 2966222279651481834701069)
          ·
            refine ⟨1112333354869305688012901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2966222279651481834701069 1112333354869305688012901)
            ·
              refine ⟨208562504037994816502419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1112333354869305688012901 208562504037994816502419)
              ·
                refine ⟨312843756056992224753629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208562504037994816502419 312843756056992224753629)
                ·
                  refine ⟨117316408521372084282611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312843756056992224753629 117316408521372084282611)
                  ·
                    rfl

theorem cell20_257032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_257032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257032 prefixEnd_257032 := by exact prefixLift 257032
  have htrace : WordTrace (prefixWord ++ tailWord_257032) baseStart_257032 baseEnd_257032 := by
    simpa [prefixWord, tailWord_257032, baseEnd_257032] using wordTrace_append hprefix tailTrace_257032
  have hstable : (prefixWord ++ tailWord_257032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257032).length < 2 ^ (prefixWord ++ tailWord_257032).sum := by decide
  have hdescent : baseEnd_257032 < baseStart_257032 := by decide
  rcases family_descends (prefixWord ++ tailWord_257032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257043 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_257043 : Nat := 118140960795 + 257043 * 2 ^ 59
def prefixEnd_257043 : Nat := 4983230072969 + 3 ^ 40 * 257043 * 2
def baseEnd_257043 : Nat := 117321429221104934915899

theorem tailTrace_257043 : CollatzResearch.WordTrace tailWord_257043 prefixEnd_257043 117321429221104934915899 := by
  unfold tailWord_257043
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375128407784585294495783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6250085605189723529663855 9375128407784585294495783)
  ·
    refine ⟨14062692611676877941743675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375128407784585294495783 14062692611676877941743675)
    ·
      refine ⟨21094038917515316912615513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062692611676877941743675 21094038917515316912615513)
      ·
        refine ⟨15820529188136487684461635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21094038917515316912615513 15820529188136487684461635)
        ·
          refine ⟨23730793782204731526692453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820529188136487684461635 23730793782204731526692453)
          ·
            refine ⟨4449523834163387161254835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23730793782204731526692453 4449523834163387161254835)
            ·
              refine ⟨6674285751245080741882253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449523834163387161254835 6674285751245080741882253)
              ·
                refine ⟨2502857156716905278205845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6674285751245080741882253 2502857156716905278205845)
                ·
                  refine ⟨117321429221104934915899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2502857156716905278205845 117321429221104934915899)
                  ·
                    rfl

theorem cell20_257043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_257043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257043 prefixEnd_257043 := by exact prefixLift 257043
  have htrace : WordTrace (prefixWord ++ tailWord_257043) baseStart_257043 baseEnd_257043 := by
    simpa [prefixWord, tailWord_257043, baseEnd_257043] using wordTrace_append hprefix tailTrace_257043
  have hstable : (prefixWord ++ tailWord_257043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257043).length < 2 ^ (prefixWord ++ tailWord_257043).sum := by decide
  have hdescent : baseEnd_257043 < baseStart_257043 := by decide
  rcases family_descends (prefixWord ++ tailWord_257043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257070 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_257070 : Nat := 118140960795 + 257070 * 2 ^ 59
def prefixEnd_257070 : Nat := 4983230072969 + 3 ^ 40 * 257070 * 2
def baseEnd_257070 : Nat := 117333752756812841015789

theorem tailTrace_257070 : CollatzResearch.WordTrace tailWord_257070 prefixEnd_257070 117333752756812841015789 := by
  unfold tailWord_257070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172014147335846113216083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6250742119124512603819109 1172014147335846113216083)
  ·
    refine ⟨1758021221003769169824125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1172014147335846113216083 1758021221003769169824125)
    ·
      refine ⟨659257957876413438684047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1758021221003769169824125 659257957876413438684047)
      ·
        refine ⟨988886936814620158026071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659257957876413438684047 988886936814620158026071)
        ·
          refine ⟨1483330405221930237039107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988886936814620158026071 1483330405221930237039107)
          ·
            refine ⟨2224995607832895355558661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483330405221930237039107 2224995607832895355558661)
            ·
              refine ⟨417186676468667879167249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2224995607832895355558661 417186676468667879167249)
              ·
                refine ⟨312890007351500909375437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417186676468667879167249 312890007351500909375437)
                ·
                  refine ⟨117333752756812841015789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312890007351500909375437 117333752756812841015789)
                  ·
                    rfl

theorem cell20_257070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_257070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257070 prefixEnd_257070 := by exact prefixLift 257070
  have htrace : WordTrace (prefixWord ++ tailWord_257070) baseStart_257070 baseEnd_257070 := by
    simpa [prefixWord, tailWord_257070, baseEnd_257070] using wordTrace_append hprefix tailTrace_257070
  have hstable : (prefixWord ++ tailWord_257070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257070).length < 2 ^ (prefixWord ++ tailWord_257070).sum := by decide
  have hdescent : baseEnd_257070 < baseStart_257070 := by decide
  rcases family_descends (prefixWord ++ tailWord_257070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257084 : List Nat := [2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_257084 : Nat := 118140960795 + 257084 * 2 ^ 59
def prefixEnd_257084 : Nat := 4983230072969 + 3 ^ 40 * 257084 * 2
def baseEnd_257084 : Nat := 39113380912763671516355

theorem tailTrace_257084 : CollatzResearch.WordTrace tailWord_257084 prefixEnd_257084 39113380912763671516355 := by
  unfold tailWord_257084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688311900318024648369153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6251082533757366197825537 4688311900318024648369153)
  ·
    refine ⟨3516233925238518486276865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4688311900318024648369153 3516233925238518486276865)
    ·
      refine ⟨2637175443928888864707649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3516233925238518486276865 2637175443928888864707649)
      ·
        refine ⟨1977881582946666648530737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637175443928888864707649 1977881582946666648530737)
        ·
          refine ⟨1483411187209999986398053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977881582946666648530737 1483411187209999986398053)
          ·
            refine ⟨278139597601874997449635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1483411187209999986398053 278139597601874997449635)
            ·
              refine ⟨417209396402812496174453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278139597601874997449635 417209396402812496174453)
              ·
                refine ⟨39113380912763671516355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417209396402812496174453 39113380912763671516355)
                ·
                  rfl

theorem cell20_257084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_257084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257084 prefixEnd_257084 := by exact prefixLift 257084
  have htrace : WordTrace (prefixWord ++ tailWord_257084) baseStart_257084 baseEnd_257084 := by
    simpa [prefixWord, tailWord_257084, baseEnd_257084] using wordTrace_append hprefix tailTrace_257084
  have hstable : (prefixWord ++ tailWord_257084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257084).length < 2 ^ (prefixWord ++ tailWord_257084).sum := by decide
  have hdescent : baseEnd_257084 < baseStart_257084 := by decide
  rcases family_descends (prefixWord ++ tailWord_257084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257094 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_257094 : Nat := 118140960795 + 257094 * 2 ^ 59
def prefixEnd_257094 : Nat := 4983230072969 + 3 ^ 40 * 257094 * 2
def baseEnd_257094 : Nat := 117344707010775424215691

theorem tailTrace_257094 : CollatzResearch.WordTrace tailWord_257094 prefixEnd_257094 117344707010775424215691 := by
  unfold tailWord_257094
  simp only [CollatzResearch.WordTrace]
  refine ⟨293030891581244406393823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6251325687066547336401557 293030891581244406393823)
  ·
    refine ⟨439546337371866609590735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293030891581244406393823 439546337371866609590735)
    ·
      refine ⟨659319506057799914386103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439546337371866609590735 659319506057799914386103)
      ·
        refine ⟨988979259086699871579155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659319506057799914386103 988979259086699871579155)
        ·
          refine ⟨1483468888630049807368733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988979259086699871579155 1483468888630049807368733)
          ·
            refine ⟨556300833236268677763275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483468888630049807368733 556300833236268677763275)
            ·
              refine ⟨834451249854403016644913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556300833236268677763275 834451249854403016644913)
              ·
                refine ⟨625838437390802262483685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834451249854403016644913 625838437390802262483685)
                ·
                  refine ⟨117344707010775424215691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625838437390802262483685 117344707010775424215691)
                  ·
                    rfl

theorem cell20_257094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_257094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257094 prefixEnd_257094 := by exact prefixLift 257094
  have htrace : WordTrace (prefixWord ++ tailWord_257094) baseStart_257094 baseEnd_257094 := by
    simpa [prefixWord, tailWord_257094, baseEnd_257094] using wordTrace_append hprefix tailTrace_257094
  have hstable : (prefixWord ++ tailWord_257094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257094).length < 2 ^ (prefixWord ++ tailWord_257094).sum := by decide
  have hdescent : baseEnd_257094 < baseStart_257094 := by decide
  rcases family_descends (prefixWord ++ tailWord_257094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257101 : List Nat := [1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_257101 : Nat := 118140960795 + 257101 * 2 ^ 59
def prefixEnd_257101 : Nat := 4983230072969 + 3 ^ 40 * 257101 * 2
def baseEnd_257101 : Nat := 39115967333838170327443

theorem tailTrace_257101 : CollatzResearch.WordTrace tailWord_257101 prefixEnd_257101 39115967333838170327443 := by
  unfold tailWord_257101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377243841574461200107157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6251495894382974133404771 9377243841574461200107157)
  ·
    refine ⟨439558305073802868755023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9377243841574461200107157 439558305073802868755023)
    ·
      refine ⟨659337457610704303132535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439558305073802868755023 659337457610704303132535)
      ·
        refine ⟨989006186416056454698803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659337457610704303132535 989006186416056454698803)
        ·
          refine ⟨1483509279624084682048205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989006186416056454698803 1483509279624084682048205)
          ·
            refine ⟨556315979859031755768077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483509279624084682048205 556315979859031755768077)
            ·
              refine ⟨208618492447136908413029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556315979859031755768077 208618492447136908413029)
              ·
                refine ⟨39115967333838170327443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208618492447136908413029 39115967333838170327443)
                ·
                  rfl

theorem cell20_257101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_257101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257101 prefixEnd_257101 := by exact prefixLift 257101
  have htrace : WordTrace (prefixWord ++ tailWord_257101) baseStart_257101 baseEnd_257101 := by
    simpa [prefixWord, tailWord_257101, baseEnd_257101] using wordTrace_append hprefix tailTrace_257101
  have hstable : (prefixWord ++ tailWord_257101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257101).length < 2 ^ (prefixWord ++ tailWord_257101).sum := by decide
  have hdescent : baseEnd_257101 < baseStart_257101 := by decide
  rcases family_descends (prefixWord ++ tailWord_257101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257112 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_257112 : Nat := 118140960795 + 257112 * 2 ^ 59
def prefixEnd_257112 : Nat := 4983230072969 + 3 ^ 40 * 257112 * 2
def baseEnd_257112 : Nat := 117352922701247361615617

theorem tailTrace_257112 : CollatzResearch.WordTrace tailWord_257112 prefixEnd_257112 117352922701247361615617 := by
  unfold tailWord_257112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688822522267305039378795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6251763363023073385838393 4688822522267305039378795)
  ·
    refine ⟨7033233783400957559068193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688822522267305039378795 7033233783400957559068193)
    ·
      refine ⟨5274925337550718169301145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7033233783400957559068193 5274925337550718169301145)
      ·
        refine ⟨3956194003163038626975859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274925337550718169301145 3956194003163038626975859)
        ·
          refine ⟨5934291004744557940463789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956194003163038626975859 5934291004744557940463789)
          ·
            refine ⟨2225359126779209227673921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5934291004744557940463789 2225359126779209227673921)
            ·
              refine ⟨1669019345084406920755441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225359126779209227673921 1669019345084406920755441)
              ·
                refine ⟨1251764508813305190566581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669019345084406920755441 1251764508813305190566581)
                ·
                  refine ⟨117352922701247361615617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251764508813305190566581 117352922701247361615617)
                  ·
                    rfl

theorem cell20_257112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_257112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257112 prefixEnd_257112 := by exact prefixLift 257112
  have htrace : WordTrace (prefixWord ++ tailWord_257112) baseStart_257112 baseEnd_257112 := by
    simpa [prefixWord, tailWord_257112, baseEnd_257112] using wordTrace_append hprefix tailTrace_257112
  have hstable : (prefixWord ++ tailWord_257112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257112).length < 2 ^ (prefixWord ++ tailWord_257112).sum := by decide
  have hdescent : baseEnd_257112 < baseStart_257112 := by decide
  rcases family_descends (prefixWord ++ tailWord_257112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257119 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_257119 : Nat := 118140960795 + 257119 * 2 ^ 59
def prefixEnd_257119 : Nat := 4983230072969 + 3 ^ 40 * 257119 * 2
def baseEnd_257119 : Nat := 117356117691986448382255

theorem tailTrace_257119 : CollatzResearch.WordTrace tailWord_257119 prefixEnd_257119 117356117691986448382255 := by
  unfold tailWord_257119
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377900355509250274262411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6251933570339500182841607 9377900355509250274262411)
  ·
    refine ⟨14066850533263875411393617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377900355509250274262411 14066850533263875411393617)
    ·
      refine ⟨10550137899947906558545213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14066850533263875411393617 10550137899947906558545213)
      ·
        refine ⟨3956301712480464959454455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10550137899947906558545213 3956301712480464959454455)
        ·
          refine ⟨5934452568720697439181683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956301712480464959454455 5934452568720697439181683)
          ·
            refine ⟨8901678853081046158772525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934452568720697439181683 8901678853081046158772525)
            ·
              refine ⟨3338129569905392309539697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8901678853081046158772525 3338129569905392309539697)
              ·
                refine ⟨2503597177429044232154773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338129569905392309539697 2503597177429044232154773)
                ·
                  refine ⟨117356117691986448382255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2503597177429044232154773 117356117691986448382255)
                  ·
                    rfl

theorem cell20_257119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_257119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257119 prefixEnd_257119 := by exact prefixLift 257119
  have htrace : WordTrace (prefixWord ++ tailWord_257119) baseStart_257119 baseEnd_257119 := by
    simpa [prefixWord, tailWord_257119, baseEnd_257119] using wordTrace_append hprefix tailTrace_257119
  have hstable : (prefixWord ++ tailWord_257119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257119).length < 2 ^ (prefixWord ++ tailWord_257119).sum := by decide
  have hdescent : baseEnd_257119 < baseStart_257119 := by decide
  rcases family_descends (prefixWord ++ tailWord_257119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257122 : List Nat := [3, 3, 2, 2, 1, 2, 7]
def baseStart_257122 : Nat := 118140960795 + 257122 * 2 ^ 59
def prefixEnd_257122 : Nat := 4983230072969 + 3 ^ 40 * 257122 * 2
def baseEnd_257122 : Nat := 13039720774859085698027

theorem tailTrace_257122 : CollatzResearch.WordTrace tailWord_257122 prefixEnd_257122 13039720774859085698027 := by
  unfold tailWord_257122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344502443624595446655405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6252006516332254524414413 2344502443624595446655405)
  ·
    refine ⟨879188416359223292495777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2344502443624595446655405 879188416359223292495777)
    ·
      refine ⟨659391312269417469371833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 879188416359223292495777 659391312269417469371833)
      ·
        refine ⟨494543484202063102028875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659391312269417469371833 494543484202063102028875)
        ·
          refine ⟨741815226303094653043313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494543484202063102028875 741815226303094653043313)
          ·
            refine ⟨556361419727320989782485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741815226303094653043313 556361419727320989782485)
            ·
              refine ⟨13039720774859085698027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 556361419727320989782485 13039720774859085698027)
              ·
                rfl

theorem cell20_257122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_257122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257122 prefixEnd_257122 := by exact prefixLift 257122
  have htrace : WordTrace (prefixWord ++ tailWord_257122) baseStart_257122 baseEnd_257122 := by
    simpa [prefixWord, tailWord_257122, baseEnd_257122] using wordTrace_append hprefix tailTrace_257122
  have hstable : (prefixWord ++ tailWord_257122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257122).length < 2 ^ (prefixWord ++ tailWord_257122).sum := by decide
  have hdescent : baseEnd_257122 < baseStart_257122 := by decide
  rcases family_descends (prefixWord ++ tailWord_257122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257129 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_257129 : Nat := 118140960795 + 257129 * 2 ^ 59
def prefixEnd_257129 : Nat := 4983230072969 + 3 ^ 40 * 257129 * 2
def baseEnd_257129 : Nat := 117360681964470858048881

theorem tailTrace_257129 : CollatzResearch.WordTrace tailWord_257129 prefixEnd_257129 117360681964470858048881 := by
  unfold tailWord_257129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378265085473021982126441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6252176723648681321417627 9378265085473021982126441)
  ·
    refine ⟨7033698814104766486594831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9378265085473021982126441 7033698814104766486594831)
    ·
      refine ⟨10550548221157149729892247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033698814104766486594831 10550548221157149729892247)
      ·
        refine ⟨15825822331735724594838371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550548221157149729892247 15825822331735724594838371)
        ·
          refine ⟨23738733497603586892257557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825822331735724594838371 23738733497603586892257557)
          ·
            refine ⟨1112753132700168135574573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23738733497603586892257557 1112753132700168135574573)
            ·
              refine ⟨417282424762563050840465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112753132700168135574573 417282424762563050840465)
              ·
                refine ⟨312961818571922288130349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417282424762563050840465 312961818571922288130349)
                ·
                  refine ⟨117360681964470858048881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312961818571922288130349 117360681964470858048881)
                  ·
                    rfl

theorem cell20_257129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_257129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257129 prefixEnd_257129 := by exact prefixLift 257129
  have htrace : WordTrace (prefixWord ++ tailWord_257129) baseStart_257129 baseEnd_257129 := by
    simpa [prefixWord, tailWord_257129, baseEnd_257129] using wordTrace_append hprefix tailTrace_257129
  have hstable : (prefixWord ++ tailWord_257129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257129).length < 2 ^ (prefixWord ++ tailWord_257129).sum := by decide
  have hdescent : baseEnd_257129 < baseStart_257129 := by decide
  rcases family_descends (prefixWord ++ tailWord_257129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257136 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_257136 : Nat := 118140960795 + 257136 * 2 ^ 59
def prefixEnd_257136 : Nat := 4983230072969 + 3 ^ 40 * 257136 * 2
def baseEnd_257136 : Nat := 117363876955209944815519

theorem tailTrace_257136 : CollatzResearch.WordTrace tailWord_257136 prefixEnd_257136 117363876955209944815519 := by
  unfold tailWord_257136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689260198223831088815631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6252346930965108118420841 4689260198223831088815631)
  ·
    refine ⟨7033890297335746633223447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689260198223831088815631 7033890297335746633223447)
    ·
      refine ⟨10550835446003619949835171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033890297335746633223447 10550835446003619949835171)
      ·
        refine ⟨15826253169005429924752757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550835446003619949835171 15826253169005429924752757)
        ·
          refine ⟨1483711234594259055445571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15826253169005429924752757 1483711234594259055445571)
          ·
            refine ⟨2225566851891388583168357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483711234594259055445571 2225566851891388583168357)
            ·
              refine ⟨417293784729635359344067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2225566851891388583168357 417293784729635359344067)
              ·
                refine ⟨625940677094453039016101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417293784729635359344067 625940677094453039016101)
                ·
                  refine ⟨117363876955209944815519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 625940677094453039016101 117363876955209944815519)
                  ·
                    rfl

theorem cell20_257136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_257136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257136 prefixEnd_257136 := by exact prefixLift 257136
  have htrace : WordTrace (prefixWord ++ tailWord_257136) baseStart_257136 baseEnd_257136 := by
    simpa [prefixWord, tailWord_257136, baseEnd_257136] using wordTrace_append hprefix tailTrace_257136
  have hstable : (prefixWord ++ tailWord_257136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257136).length < 2 ^ (prefixWord ++ tailWord_257136).sum := by decide
  have hdescent : baseEnd_257136 < baseStart_257136 := by decide
  rcases family_descends (prefixWord ++ tailWord_257136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257160 : List Nat := [2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_257160 : Nat := 118140960795 + 257160 * 2 ^ 59
def prefixEnd_257160 : Nat := 4983230072969 + 3 ^ 40 * 257160 * 2
def baseEnd_257160 : Nat := 39124943736390842671807

theorem tailTrace_257160 : CollatzResearch.WordTrace tailWord_257160 prefixEnd_257160 39124943736390842671807 := by
  unfold tailWord_257160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689697874180357138252467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6252930498907142851003289 4689697874180357138252467)
  ·
    refine ⟨7034546811270535707378701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689697874180357138252467 7034546811270535707378701)
    ·
      refine ⟨2637955054226450890267013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7034546811270535707378701 2637955054226450890267013)
      ·
        refine ⟨494616572667459541925065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2637955054226450890267013 494616572667459541925065)
        ·
          refine ⟨370962429500594656443799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494616572667459541925065 370962429500594656443799)
          ·
            refine ⟨556443644250891984665699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370962429500594656443799 556443644250891984665699)
            ·
              refine ⟨834665466376337976998549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556443644250891984665699 834665466376337976998549)
              ·
                refine ⟨39124943736390842671807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834665466376337976998549 39124943736390842671807)
                ·
                  rfl

theorem cell20_257160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_257160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257160 prefixEnd_257160 := by exact prefixLift 257160
  have htrace : WordTrace (prefixWord ++ tailWord_257160) baseStart_257160 baseEnd_257160 := by
    simpa [prefixWord, tailWord_257160, baseEnd_257160] using wordTrace_append hprefix tailTrace_257160
  have hstable : (prefixWord ++ tailWord_257160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257160).length < 2 ^ (prefixWord ++ tailWord_257160).sum := by decide
  have hdescent : baseEnd_257160 < baseStart_257160 := by decide
  rcases family_descends (prefixWord ++ tailWord_257160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257170 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_257170 : Nat := 118140960795 + 257170 * 2 ^ 59
def prefixEnd_257170 : Nat := 4983230072969 + 3 ^ 40 * 257170 * 2
def baseEnd_257170 : Nat := 117379395481656937682047

theorem tailTrace_257170 : CollatzResearch.WordTrace tailWord_257170 prefixEnd_257170 117379395481656937682047 := by
  unfold tailWord_257170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344940119581121496092241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6253173652216323989579309 2344940119581121496092241)
  ·
    refine ⟨1758705089685841122069181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2344940119581121496092241 1758705089685841122069181)
    ·
      refine ⟨659514408632190420775943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1758705089685841122069181 659514408632190420775943)
      ·
        refine ⟨989271612948285631163915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659514408632190420775943 989271612948285631163915)
        ·
          refine ⟨1483907419422428446745873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989271612948285631163915 1483907419422428446745873)
          ·
            refine ⟨1112930564566821335059405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483907419422428446745873 1112930564566821335059405)
            ·
              refine ⟨417348961712558000647277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112930564566821335059405 417348961712558000647277)
              ·
                refine ⟨156505860642209250242729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417348961712558000647277 156505860642209250242729)
                ·
                  refine ⟨117379395481656937682047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156505860642209250242729 117379395481656937682047)
                  ·
                    rfl

theorem cell20_257170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_257170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257170 prefixEnd_257170 := by exact prefixLift 257170
  have htrace : WordTrace (prefixWord ++ tailWord_257170) baseStart_257170 baseEnd_257170 := by
    simpa [prefixWord, tailWord_257170, baseEnd_257170] using wordTrace_append hprefix tailTrace_257170
  have hstable : (prefixWord ++ tailWord_257170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257170).length < 2 ^ (prefixWord ++ tailWord_257170).sum := by decide
  have hdescent : baseEnd_257170 < baseStart_257170 := by decide
  rcases family_descends (prefixWord ++ tailWord_257170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257191 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_257191 : Nat := 118140960795 + 257191 * 2 ^ 59
def prefixEnd_257191 : Nat := 4983230072969 + 3 ^ 40 * 257191 * 2
def baseEnd_257191 : Nat := 117388980453874197981961

theorem tailTrace_257191 : CollatzResearch.WordTrace tailWord_257191 prefixEnd_257191 117388980453874197981961 := by
  unfold tailWord_257191
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380526411248406570883427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6253684274165604380588951 9380526411248406570883427)
  ·
    refine ⟨14070789616872609856325141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9380526411248406570883427 14070789616872609856325141)
    ·
      refine ⟨659568263290903587015241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14070789616872609856325141 659568263290903587015241)
      ·
        refine ⟨494676197468177690261431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659568263290903587015241 494676197468177690261431)
        ·
          refine ⟨742014296202266535392147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494676197468177690261431 742014296202266535392147)
          ·
            refine ⟨1113021444303399803088221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742014296202266535392147 1113021444303399803088221)
            ·
              refine ⟨417383041613774926158083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113021444303399803088221 417383041613774926158083)
              ·
                refine ⟨626074562420662389237125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417383041613774926158083 626074562420662389237125)
                ·
                  refine ⟨117388980453874197981961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 626074562420662389237125 117388980453874197981961)
                  ·
                    rfl

theorem cell20_257191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_257191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257191 prefixEnd_257191 := by exact prefixLift 257191
  have htrace : WordTrace (prefixWord ++ tailWord_257191) baseStart_257191 baseEnd_257191 := by
    simpa [prefixWord, tailWord_257191, baseEnd_257191] using wordTrace_append hprefix tailTrace_257191
  have hstable : (prefixWord ++ tailWord_257191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257191).length < 2 ^ (prefixWord ++ tailWord_257191).sum := by decide
  have hdescent : baseEnd_257191 < baseStart_257191 := by decide
  rcases family_descends (prefixWord ++ tailWord_257191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257201 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 3]
def baseStart_257201 : Nat := 118140960795 + 257201 * 2 ^ 59
def prefixEnd_257201 : Nat := 4983230072969 + 3 ^ 40 * 257201 * 2
def baseEnd_257201 : Nat := 117393544726358607648587

theorem tailTrace_257201 : CollatzResearch.WordTrace tailWord_257201 prefixEnd_257201 117393544726358607648587 := by
  unfold tailWord_257201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380891141212178278747457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6253927427474785519164971 9380891141212178278747457)
  ·
    refine ⟨7035668355909133709060593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9380891141212178278747457 7035668355909133709060593)
    ·
      refine ⟨5276751266931850281795445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7035668355909133709060593 5276751266931850281795445)
      ·
        refine ⟨494695431274860963918323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5276751266931850281795445 494695431274860963918323)
        ·
          refine ⟨742043146912291445877485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494695431274860963918323 742043146912291445877485)
          ·
            refine ⟨278266180092109292204057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742043146912291445877485 278266180092109292204057)
            ·
              refine ⟨208699635069081969153043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278266180092109292204057 208699635069081969153043)
              ·
                refine ⟨313049452603622953729565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208699635069081969153043 313049452603622953729565)
                ·
                  refine ⟨117393544726358607648587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313049452603622953729565 117393544726358607648587)
                  ·
                    rfl

theorem cell20_257201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_257201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257201 prefixEnd_257201 := by exact prefixLift 257201
  have htrace : WordTrace (prefixWord ++ tailWord_257201) baseStart_257201 baseEnd_257201 := by
    simpa [prefixWord, tailWord_257201, baseEnd_257201] using wordTrace_append hprefix tailTrace_257201
  have hstable : (prefixWord ++ tailWord_257201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257201).length < 2 ^ (prefixWord ++ tailWord_257201).sum := by decide
  have hdescent : baseEnd_257201 < baseStart_257201 := by decide
  rcases family_descends (prefixWord ++ tailWord_257201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257236 : List Nat := [2, 4, 1, 4, 1, 8]
def baseStart_257236 : Nat := 118140960795 + 257236 * 2 ^ 59
def prefixEnd_257236 : Nat := 4983230072969 + 3 ^ 40 * 257236 * 2
def baseEnd_257236 : Nat := 4348500728890890425251

theorem tailTrace_257236 : CollatzResearch.WordTrace tailWord_257236 prefixEnd_257236 4348500728890890425251 := by
  unfold tailWord_257236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691083848042689628135781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6254778464056919504181041 4691083848042689628135781)
  ·
    refine ⟨879578221508004305275459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4691083848042689628135781 879578221508004305275459)
    ·
      refine ⟨1319367332262006457913189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879578221508004305275459 1319367332262006457913189)
      ·
        refine ⟨247381374799126210858723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1319367332262006457913189 247381374799126210858723)
        ·
          refine ⟨371072062198689316288085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247381374799126210858723 371072062198689316288085)
          ·
            refine ⟨4348500728890890425251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 371072062198689316288085 4348500728890890425251)
            ·
              rfl

theorem cell20_257236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 8].length) (baseStart_257236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257236 prefixEnd_257236 := by exact prefixLift 257236
  have htrace : WordTrace (prefixWord ++ tailWord_257236) baseStart_257236 baseEnd_257236 := by
    simpa [prefixWord, tailWord_257236, baseEnd_257236] using wordTrace_append hprefix tailTrace_257236
  have hstable : (prefixWord ++ tailWord_257236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257236).length < 2 ^ (prefixWord ++ tailWord_257236).sum := by decide
  have hdescent : baseEnd_257236 < baseStart_257236 := by decide
  rcases family_descends (prefixWord ++ tailWord_257236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257240 : List Nat := [2, 1, 2, 2, 13]
def baseStart_257240 : Nat := 118140960795 + 257240 * 2 ^ 59
def prefixEnd_257240 : Nat := 4983230072969 + 3 ^ 40 * 257240 * 2
def baseEnd_257240 : Nat := 1449522782580837103067

theorem tailTrace_257240 : CollatzResearch.WordTrace tailWord_257240 prefixEnd_257240 1449522782580837103067 := by
  unfold tailWord_257240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691156794035443969708587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6254875725380591959611449 4691156794035443969708587)
  ·
    refine ⟨7036735191053165954562881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4691156794035443969708587 7036735191053165954562881)
    ·
      refine ⟨5277551393289874465922161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7036735191053165954562881 5277551393289874465922161)
      ·
        refine ⟨3958163544967405849441621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5277551393289874465922161 3958163544967405849441621)
        ·
          refine ⟨1449522782580837103067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3958163544967405849441621 1449522782580837103067)
          ·
            rfl

theorem cell20_257240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 13].length) (baseStart_257240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257240 prefixEnd_257240 := by exact prefixLift 257240
  have htrace : WordTrace (prefixWord ++ tailWord_257240) baseStart_257240 baseEnd_257240 := by
    simpa [prefixWord, tailWord_257240, baseEnd_257240] using wordTrace_append hprefix tailTrace_257240
  have hstable : (prefixWord ++ tailWord_257240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257240).length < 2 ^ (prefixWord ++ tailWord_257240).sum := by decide
  have hdescent : baseEnd_257240 < baseStart_257240 := by decide
  rcases family_descends (prefixWord ++ tailWord_257240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257253 : List Nat := [1, 3, 1, 4, 4, 1, 1, 5]
def baseStart_257253 : Nat := 118140960795 + 257253 * 2 ^ 59
def prefixEnd_257253 : Nat := 4983230072969 + 3 ^ 40 * 257253 * 2
def baseEnd_257253 : Nat := 39139092981092512638347

theorem tailTrace_257253 : CollatzResearch.WordTrace tailWord_257253 prefixEnd_257253 39139092981092512638347 := by
  unfold tailWord_257253
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382787737023791159640413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6255191824682527439760275 9382787737023791159640413)
  ·
    refine ⟨3518545401383921684865155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9382787737023791159640413 3518545401383921684865155)
    ·
      refine ⟨5277818102075882527297733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518545401383921684865155 5277818102075882527297733)
      ·
        refine ⟨989590894139227973868325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5277818102075882527297733 989590894139227973868325)
        ·
          refine ⟨185548292651105245100311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 989590894139227973868325 185548292651105245100311)
          ·
            refine ⟨278322438976657867650467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185548292651105245100311 278322438976657867650467)
            ·
              refine ⟨417483658464986801475701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278322438976657867650467 417483658464986801475701)
              ·
                refine ⟨39139092981092512638347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417483658464986801475701 39139092981092512638347)
                ·
                  rfl

theorem cell20_257253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_257253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257253 prefixEnd_257253 := by exact prefixLift 257253
  have htrace : WordTrace (prefixWord ++ tailWord_257253) baseStart_257253 baseEnd_257253 := by
    simpa [prefixWord, tailWord_257253, baseEnd_257253] using wordTrace_append hprefix tailTrace_257253
  have hstable : (prefixWord ++ tailWord_257253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257253).length < 2 ^ (prefixWord ++ tailWord_257253).sum := by decide
  have hdescent : baseEnd_257253 < baseStart_257253 := by decide
  rcases family_descends (prefixWord ++ tailWord_257253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257271 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_257271 : Nat := 118140960795 + 257271 * 2 ^ 59
def prefixEnd_257271 : Nat := 4983230072969 + 3 ^ 40 * 257271 * 2
def baseEnd_257271 : Nat := 117425494633749475314967

theorem tailTrace_257271 : CollatzResearch.WordTrace tailWord_257271 prefixEnd_257271 117425494633749475314967 := by
  unfold tailWord_257271
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383444250958580233795667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6255629500639053489197111 9383444250958580233795667)
  ·
    refine ⟨14075166376437870350693501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383444250958580233795667 14075166376437870350693501)
    ·
      refine ⟨5278187391164201381510063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14075166376437870350693501 5278187391164201381510063)
      ·
        refine ⟨7917281086746302072265095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278187391164201381510063 7917281086746302072265095)
        ·
          refine ⟨11875921630119453108397643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917281086746302072265095 11875921630119453108397643)
          ·
            refine ⟨17813882445179179662596465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875921630119453108397643 17813882445179179662596465)
            ·
              refine ⟨13360411833884384746947349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17813882445179179662596465 13360411833884384746947349)
              ·
                refine ⟨626269304713330535013157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13360411833884384746947349 626269304713330535013157)
                ·
                  refine ⟨117425494633749475314967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 626269304713330535013157 117425494633749475314967)
                  ·
                    rfl

theorem cell20_257271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_257271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257271 prefixEnd_257271 := by exact prefixLift 257271
  have htrace : WordTrace (prefixWord ++ tailWord_257271) baseStart_257271 baseEnd_257271 := by
    simpa [prefixWord, tailWord_257271, baseEnd_257271] using wordTrace_append hprefix tailTrace_257271
  have hstable : (prefixWord ++ tailWord_257271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257271).length < 2 ^ (prefixWord ++ tailWord_257271).sum := by decide
  have hdescent : baseEnd_257271 < baseStart_257271 := by decide
  rcases family_descends (prefixWord ++ tailWord_257271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257284 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_257284 : Nat := 118140960795 + 257284 * 2 ^ 59
def prefixEnd_257284 : Nat := 4983230072969 + 3 ^ 40 * 257284 * 2
def baseEnd_257284 : Nat := 117431428187979207881581

theorem tailTrace_257284 : CollatzResearch.WordTrace tailWord_257284 prefixEnd_257284 117431428187979207881581 := by
  unfold tailWord_257284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691959199955741727009453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6255945599940988969345937 4691959199955741727009453)
  ·
    refine ⟨1759484699983403147628545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4691959199955741727009453 1759484699983403147628545)
    ·
      refine ⟨1319613524987552360721409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1759484699983403147628545 1319613524987552360721409)
      ·
        refine ⟨989710143740664270541057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319613524987552360721409 989710143740664270541057)
        ·
          refine ⟨742282607805498202905793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989710143740664270541057 742282607805498202905793)
          ·
            refine ⟨556711955854123652179345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742282607805498202905793 556711955854123652179345)
            ·
              refine ⟨417533966890592739134509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556711955854123652179345 417533966890592739134509)
              ·
                refine ⟨156575237583972277175441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417533966890592739134509 156575237583972277175441)
                ·
                  refine ⟨117431428187979207881581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156575237583972277175441 117431428187979207881581)
                  ·
                    rfl

theorem cell20_257284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_257284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257284 prefixEnd_257284 := by exact prefixLift 257284
  have htrace : WordTrace (prefixWord ++ tailWord_257284) baseStart_257284 baseEnd_257284 := by
    simpa [prefixWord, tailWord_257284, baseEnd_257284] using wordTrace_append hprefix tailTrace_257284
  have hstable : (prefixWord ++ tailWord_257284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257284).length < 2 ^ (prefixWord ++ tailWord_257284).sum := by decide
  have hdescent : baseEnd_257284 < baseStart_257284 := by decide
  rcases family_descends (prefixWord ++ tailWord_257284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257333 : List Nat := [1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_257333 : Nat := 118140960795 + 257333 * 2 ^ 59
def prefixEnd_257333 : Nat := 4983230072969 + 3 ^ 40 * 257333 * 2
def baseEnd_257333 : Nat := 39151264374384271749349

theorem tailTrace_257333 : CollatzResearch.WordTrace tailWord_257333 prefixEnd_257333 39151264374384271749349 := by
  unfold tailWord_257333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385705576733964822552653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6257137051155976548368435 9385705576733964822552653)
  ·
    refine ⟨3519639591275236808457245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9385705576733964822552653 3519639591275236808457245)
    ·
      refine ⟨1319864846728213803171467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3519639591275236808457245 1319864846728213803171467)
      ·
        refine ⟨1979797270092320704757201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319864846728213803171467 1979797270092320704757201)
        ·
          refine ⟨1484847952569240528567901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979797270092320704757201 1484847952569240528567901)
          ·
            refine ⟨556817982213465198212963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1484847952569240528567901 556817982213465198212963)
            ·
              refine ⟨835226973320197797319445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556817982213465198212963 835226973320197797319445)
              ·
                refine ⟨39151264374384271749349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 835226973320197797319445 39151264374384271749349)
                ·
                  rfl

theorem cell20_257333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_257333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257333 prefixEnd_257333 := by exact prefixLift 257333
  have htrace : WordTrace (prefixWord ++ tailWord_257333) baseStart_257333 baseEnd_257333 := by
    simpa [prefixWord, tailWord_257333, baseEnd_257333] using wordTrace_append hprefix tailTrace_257333
  have hstable : (prefixWord ++ tailWord_257333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257333).length < 2 ^ (prefixWord ++ tailWord_257333).sum := by decide
  have hdescent : baseEnd_257333 < baseStart_257333 := by decide
  rcases family_descends (prefixWord ++ tailWord_257333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257340 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_257340 : Nat := 118140960795 + 257340 * 2 ^ 59
def prefixEnd_257340 : Nat := 4983230072969 + 3 ^ 40 * 257340 * 2
def baseEnd_257340 : Nat := 117456988113891902014685

theorem tailTrace_257340 : CollatzResearch.WordTrace tailWord_257340 prefixEnd_257340 117456988113891902014685 := by
  unfold tailWord_257340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692980443854302509028737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6257307258472403345371649 4692980443854302509028737)
  ·
    refine ⟨3519735332890726881771553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4692980443854302509028737 3519735332890726881771553)
    ·
      refine ⟨2639801499668045161328665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3519735332890726881771553 2639801499668045161328665)
      ·
        refine ⟨1979851124751033870996499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2639801499668045161328665 1979851124751033870996499)
        ·
          refine ⟨2969776687126550806494749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979851124751033870996499 2969776687126550806494749)
          ·
            refine ⟨1113666257672456552435531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2969776687126550806494749 1113666257672456552435531)
            ·
              refine ⟨1670499386508684828653297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113666257672456552435531 1670499386508684828653297)
              ·
                refine ⟨1252874539881513621489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670499386508684828653297 1252874539881513621489973)
                ·
                  refine ⟨117456988113891902014685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1252874539881513621489973 117456988113891902014685)
                  ·
                    rfl

theorem cell20_257340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_257340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257340 prefixEnd_257340 := by exact prefixLift 257340
  have htrace : WordTrace (prefixWord ++ tailWord_257340) baseStart_257340 baseEnd_257340 := by
    simpa [prefixWord, tailWord_257340, baseEnd_257340] using wordTrace_append hprefix tailTrace_257340
  have hstable : (prefixWord ++ tailWord_257340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257340).length < 2 ^ (prefixWord ++ tailWord_257340).sum := by decide
  have hdescent : baseEnd_257340 < baseStart_257340 := by decide
  rcases family_descends (prefixWord ++ tailWord_257340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257343 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 2]
def baseStart_257343 : Nat := 118140960795 + 257343 * 2 ^ 59
def prefixEnd_257343 : Nat := 4983230072969 + 3 ^ 40 * 257343 * 2
def baseEnd_257343 : Nat := 117458357395637224914673

theorem tailTrace_257343 : CollatzResearch.WordTrace tailWord_257343 prefixEnd_257343 117458357395637224914673 := by
  unfold tailWord_257343
  simp only [CollatzResearch.WordTrace]
  refine ⟨9386070306697736530416683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6257380204465157686944455 9386070306697736530416683)
  ·
    refine ⟨14079105460046604795625025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9386070306697736530416683 14079105460046604795625025)
    ·
      refine ⟨10559329095034953596718769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14079105460046604795625025 10559329095034953596718769)
      ·
        refine ⟨7919496821276215197539077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10559329095034953596718769 7919496821276215197539077)
        ·
          refine ⟨1484905653989290349538577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7919496821276215197539077 1484905653989290349538577)
          ·
            refine ⟨1113679240491967762153933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484905653989290349538577 1113679240491967762153933)
            ·
              refine ⟨417629715184487910807725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113679240491967762153933 417629715184487910807725)
              ·
                refine ⟨156611143194182966552897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417629715184487910807725 156611143194182966552897)
                ·
                  refine ⟨117458357395637224914673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156611143194182966552897 117458357395637224914673)
                  ·
                    rfl

theorem cell20_257343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2].length) (baseStart_257343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257343 prefixEnd_257343 := by exact prefixLift 257343
  have htrace : WordTrace (prefixWord ++ tailWord_257343) baseStart_257343 baseEnd_257343 := by
    simpa [prefixWord, tailWord_257343, baseEnd_257343] using wordTrace_append hprefix tailTrace_257343
  have hstable : (prefixWord ++ tailWord_257343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257343).length < 2 ^ (prefixWord ++ tailWord_257343).sum := by decide
  have hdescent : baseEnd_257343 < baseStart_257343 := by decide
  rcases family_descends (prefixWord ++ tailWord_257343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257366 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_257366 : Nat := 118140960795 + 257366 * 2 ^ 59
def prefixEnd_257366 : Nat := 4983230072969 + 3 ^ 40 * 257366 * 2
def baseEnd_257366 : Nat := 117468855222351367147913

theorem tailTrace_257366 : CollatzResearch.WordTrace tailWord_257366 prefixEnd_257366 117468855222351367147913 := by
  unfold tailWord_257366
  simp only [CollatzResearch.WordTrace]
  refine ⟨586681824100900716156497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6257939457076274305669301 586681824100900716156497)
  ·
    refine ⟨440011368075675537117373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 586681824100900716156497 440011368075675537117373)
    ·
      refine ⟨165004263028378326419015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440011368075675537117373 165004263028378326419015)
      ·
        refine ⟨247506394542567489628523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165004263028378326419015 247506394542567489628523)
        ·
          refine ⟨371259591813851234442785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247506394542567489628523 371259591813851234442785)
          ·
            refine ⟨278444693860388425832089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371259591813851234442785 278444693860388425832089)
            ·
              refine ⟨208833520395291319374067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278444693860388425832089 208833520395291319374067)
              ·
                refine ⟨313250280592936979061101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208833520395291319374067 313250280592936979061101)
                ·
                  refine ⟨117468855222351367147913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313250280592936979061101 117468855222351367147913)
                  ·
                    rfl

theorem cell20_257366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_257366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257366 prefixEnd_257366 := by exact prefixLift 257366
  have htrace : WordTrace (prefixWord ++ tailWord_257366) baseStart_257366 baseEnd_257366 := by
    simpa [prefixWord, tailWord_257366, baseEnd_257366] using wordTrace_append hprefix tailTrace_257366
  have hstable : (prefixWord ++ tailWord_257366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257366).length < 2 ^ (prefixWord ++ tailWord_257366).sum := by decide
  have hdescent : baseEnd_257366 < baseStart_257366 := by decide
  rcases family_descends (prefixWord ++ tailWord_257366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257392 : List Nat := [2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_257392 : Nat := 118140960795 + 257392 * 2 ^ 59
def prefixEnd_257392 : Nat := 4983230072969 + 3 ^ 40 * 257392 * 2
def baseEnd_257392 : Nat := 39160240776936944093713

theorem tailTrace_257392 : CollatzResearch.WordTrace tailWord_257392 prefixEnd_257392 39160240776936944093713 := by
  unfold tailWord_257392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693928741760108949475215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6258571655680145265966953 4693928741760108949475215)
  ·
    refine ⟨7040893112640163424212823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693928741760108949475215 7040893112640163424212823)
    ·
      refine ⟨10561339668960245136319235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040893112640163424212823 10561339668960245136319235)
      ·
        refine ⟨15842009503440367704478853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561339668960245136319235 15842009503440367704478853)
        ·
          refine ⟨2970376781895068944589785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15842009503440367704478853 2970376781895068944589785)
          ·
            refine ⟨2227782586421301708442339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970376781895068944589785 2227782586421301708442339)
            ·
              refine ⟨3341673879631952562663509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227782586421301708442339 3341673879631952562663509)
              ·
                refine ⟨39160240776936944093713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3341673879631952562663509 39160240776936944093713)
                ·
                  rfl

theorem cell20_257392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_257392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257392 prefixEnd_257392 := by exact prefixLift 257392
  have htrace : WordTrace (prefixWord ++ tailWord_257392) baseStart_257392 baseEnd_257392 := by
    simpa [prefixWord, tailWord_257392, baseEnd_257392] using wordTrace_append hprefix tailTrace_257392
  have hstable : (prefixWord ++ tailWord_257392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257392).length < 2 ^ (prefixWord ++ tailWord_257392).sum := by decide
  have hdescent : baseEnd_257392 < baseStart_257392 := by decide
  rcases family_descends (prefixWord ++ tailWord_257392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257409 : List Nat := [1, 2, 4, 3, 2, 8]
def baseStart_257409 : Nat := 118140960795 + 257409 * 2 ^ 59
def prefixEnd_257409 : Nat := 4983230072969 + 3 ^ 40 * 257409 * 2
def baseEnd_257409 : Nat := 4351425244223493656089

theorem tailTrace_257409 : CollatzResearch.WordTrace tailWord_257409 prefixEnd_257409 4351425244223493656089 := by
  unfold tailWord_257409
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388477524458629802319281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6258985016305753201546187 9388477524458629802319281)
  ·
    refine ⟨7041358143343972351739461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9388477524458629802319281 7041358143343972351739461)
    ·
      refine ⟨1320254651876994815951149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7041358143343972351739461 1320254651876994815951149)
      ·
        refine ⟨495095494453873055981681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1320254651876994815951149 495095494453873055981681)
        ·
          refine ⟨371321620840404791986261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495095494453873055981681 371321620840404791986261)
          ·
            refine ⟨4351425244223493656089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 371321620840404791986261 4351425244223493656089)
            ·
              rfl

theorem cell20_257409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 8].length) (baseStart_257409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257409 prefixEnd_257409 := by exact prefixLift 257409
  have htrace : WordTrace (prefixWord ++ tailWord_257409) baseStart_257409 baseEnd_257409 := by
    simpa [prefixWord, tailWord_257409, baseEnd_257409] using wordTrace_append hprefix tailTrace_257409
  have hstable : (prefixWord ++ tailWord_257409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257409).length < 2 ^ (prefixWord ++ tailWord_257409).sum := by decide
  have hdescent : baseEnd_257409 < baseStart_257409 := by decide
  rcases family_descends (prefixWord ++ tailWord_257409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257457 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 2]
def baseStart_257457 : Nat := 118140960795 + 257457 * 2 ^ 59
def prefixEnd_257457 : Nat := 4983230072969 + 3 ^ 40 * 257457 * 2
def baseEnd_257457 : Nat := 117510390101959495114207

theorem tailTrace_257457 : CollatzResearch.WordTrace tailWord_257457 prefixEnd_257457 117510390101959495114207 := by
  unfold tailWord_257457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390228228284734000066625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6260152152189822666711083 9390228228284734000066625)
  ·
    refine ⟨7042671171213550500049969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9390228228284734000066625 7042671171213550500049969)
    ·
      refine ⟨5282003378410162875037477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7042671171213550500049969 5282003378410162875037477)
      ·
        refine ⟨990375633451905539069527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5282003378410162875037477 990375633451905539069527)
        ·
          refine ⟨1485563450177858308604291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990375633451905539069527 1485563450177858308604291)
          ·
            refine ⟨2228345175266787462906437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485563450177858308604291 2228345175266787462906437)
            ·
              refine ⟨417814720362522649294957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2228345175266787462906437 417814720362522649294957)
              ·
                refine ⟨156680520135945993485609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417814720362522649294957 156680520135945993485609)
                ·
                  refine ⟨117510390101959495114207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156680520135945993485609 117510390101959495114207)
                  ·
                    rfl

theorem cell20_257457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_257457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257457 prefixEnd_257457 := by exact prefixLift 257457
  have htrace : WordTrace (prefixWord ++ tailWord_257457) baseStart_257457 baseEnd_257457 := by
    simpa [prefixWord, tailWord_257457, baseEnd_257457] using wordTrace_append hprefix tailTrace_257457
  have hstable : (prefixWord ++ tailWord_257457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257457).length < 2 ^ (prefixWord ++ tailWord_257457).sum := by decide
  have hdescent : baseEnd_257457 < baseStart_257457 := by decide
  rcases family_descends (prefixWord ++ tailWord_257457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257516 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_257516 : Nat := 118140960795 + 257516 * 2 ^ 59
def prefixEnd_257516 : Nat := 4983230072969 + 3 ^ 40 * 257516 * 2
def baseEnd_257516 : Nat := 117537319309617512147299

theorem tailTrace_257516 : CollatzResearch.WordTrace tailWord_257516 prefixEnd_257516 117537319309617512147299 := by
  unfold tailWord_257516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696190067535493538232201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6261586756713991384309601 4696190067535493538232201)
  ·
    refine ⟨3522142550651620153674151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4696190067535493538232201 3522142550651620153674151)
    ·
      refine ⟨5283213825977430230511227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522142550651620153674151 5283213825977430230511227)
      ·
        refine ⟨7924820738966145345766841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283213825977430230511227 7924820738966145345766841)
        ·
          refine ⟨5943615554224609009325131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7924820738966145345766841 5943615554224609009325131)
          ·
            refine ⟨8915423331336913513987697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943615554224609009325131 8915423331336913513987697)
            ·
              refine ⟨6686567498502685135490773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8915423331336913513987697 6686567498502685135490773)
              ·
                refine ⟨156716425746156682863065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6686567498502685135490773 156716425746156682863065)
                ·
                  refine ⟨117537319309617512147299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156716425746156682863065 117537319309617512147299)
                  ·
                    rfl

theorem cell20_257516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_257516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257516 prefixEnd_257516 := by exact prefixLift 257516
  have htrace : WordTrace (prefixWord ++ tailWord_257516) baseStart_257516 baseEnd_257516 := by
    simpa [prefixWord, tailWord_257516, baseEnd_257516] using wordTrace_append hprefix tailTrace_257516
  have hstable : (prefixWord ++ tailWord_257516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257516).length < 2 ^ (prefixWord ++ tailWord_257516).sum := by decide
  have hdescent : baseEnd_257516 < baseStart_257516 := by decide
  rcases family_descends (prefixWord ++ tailWord_257516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257530 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_257530 : Nat := 118140960795 + 257530 * 2 ^ 59
def prefixEnd_257530 : Nat := 4983230072969 + 3 ^ 40 * 257530 * 2
def baseEnd_257530 : Nat := 117543709291095685680575

theorem tailTrace_257530 : CollatzResearch.WordTrace tailWord_257530 prefixEnd_257530 117543709291095685680575 := by
  unfold tailWord_257530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348222689255066866868511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6261927171346844978316029 2348222689255066866868511)
  ·
    refine ⟨3522334033882600300302767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348222689255066866868511 3522334033882600300302767)
    ·
      refine ⟨5283501050823900450454151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522334033882600300302767 5283501050823900450454151)
      ·
        refine ⟨7925251576235850675681227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283501050823900450454151 7925251576235850675681227)
        ·
          refine ⟨11887877364353776013521841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925251576235850675681227 11887877364353776013521841)
          ·
            refine ⟨8915908023265332010141381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11887877364353776013521841 8915908023265332010141381)
            ·
              refine ⟨1671732754362249751901509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8915908023265332010141381 1671732754362249751901509)
              ·
                refine ⟨313449891442921828481533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1671732754362249751901509 313449891442921828481533)
                ·
                  refine ⟨117543709291095685680575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313449891442921828481533 117543709291095685680575)
                  ·
                    rfl

theorem cell20_257530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_257530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257530 prefixEnd_257530 := by exact prefixLift 257530
  have htrace : WordTrace (prefixWord ++ tailWord_257530) baseStart_257530 baseEnd_257530 := by
    simpa [prefixWord, tailWord_257530, baseEnd_257530] using wordTrace_append hprefix tailTrace_257530
  have hstable : (prefixWord ++ tailWord_257530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257530).length < 2 ^ (prefixWord ++ tailWord_257530).sum := by decide
  have hdescent : baseEnd_257530 < baseStart_257530 := by decide
  rcases family_descends (prefixWord ++ tailWord_257530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257540 : List Nat := [2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_257540 : Nat := 118140960795 + 257540 * 2 ^ 59
def prefixEnd_257540 : Nat := 4983230072969 + 3 ^ 40 * 257540 * 2
def baseEnd_257540 : Nat := 39182757854526698449067

theorem tailTrace_257540 : CollatzResearch.WordTrace tailWord_257540 prefixEnd_257540 39182757854526698449067 := by
  unfold tailWord_257540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696627743492019587669037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6262170324656026116892049 4696627743492019587669037)
  ·
    refine ⟨1761235403809507345375889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4696627743492019587669037 1761235403809507345375889)
    ·
      refine ⟨1320926552857130509031917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1761235403809507345375889 1320926552857130509031917)
      ·
        refine ⟨495347457321423940886969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1320926552857130509031917 495347457321423940886969)
        ·
          refine ⟨371510592991067955665227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495347457321423940886969 371510592991067955665227)
          ·
            refine ⟨557265889486601933497841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371510592991067955665227 557265889486601933497841)
            ·
              refine ⟨417949417114951450123381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557265889486601933497841 417949417114951450123381)
              ·
                refine ⟨39182757854526698449067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417949417114951450123381 39182757854526698449067)
                ·
                  rfl

theorem cell20_257540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_257540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257540 prefixEnd_257540 := by exact prefixLift 257540
  have htrace : WordTrace (prefixWord ++ tailWord_257540) baseStart_257540 baseEnd_257540 := by
    simpa [prefixWord, tailWord_257540, baseEnd_257540] using wordTrace_append hprefix tailTrace_257540
  have hstable : (prefixWord ++ tailWord_257540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257540).length < 2 ^ (prefixWord ++ tailWord_257540).sum := by decide
  have hdescent : baseEnd_257540 < baseStart_257540 := by decide
  rcases family_descends (prefixWord ++ tailWord_257540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257544 : List Nat := [2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_257544 : Nat := 118140960795 + 257544 * 2 ^ 59
def prefixEnd_257544 : Nat := 4983230072969 + 3 ^ 40 * 257544 * 2
def baseEnd_257544 : Nat := 39183366424191286404617

theorem tailTrace_257544 : CollatzResearch.WordTrace tailWord_257544 prefixEnd_257544 39183366424191286404617 := by
  unfold tailWord_257544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696700689484773929241843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6262267585979698572322457 4696700689484773929241843)
  ·
    refine ⟨7045051034227160893862765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4696700689484773929241843 7045051034227160893862765)
    ·
      refine ⟨2641894137835185335198537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7045051034227160893862765 2641894137835185335198537)
      ·
        refine ⟨1981420603376389001398903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2641894137835185335198537 1981420603376389001398903)
        ·
          refine ⟨2972130905064583502098355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981420603376389001398903 2972130905064583502098355)
          ·
            refine ⟨4458196357596875253147533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972130905064583502098355 4458196357596875253147533)
            ·
              refine ⟨1671823634098828219930325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4458196357596875253147533 1671823634098828219930325)
              ·
                refine ⟨39183366424191286404617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1671823634098828219930325 39183366424191286404617)
                ·
                  rfl

theorem cell20_257544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_257544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257544 prefixEnd_257544 := by exact prefixLift 257544
  have htrace : WordTrace (prefixWord ++ tailWord_257544) baseStart_257544 baseEnd_257544 := by
    simpa [prefixWord, tailWord_257544, baseEnd_257544] using wordTrace_append hprefix tailTrace_257544
  have hstable : (prefixWord ++ tailWord_257544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257544).length < 2 ^ (prefixWord ++ tailWord_257544).sum := by decide
  have hdescent : baseEnd_257544 < baseStart_257544 := by decide
  rcases family_descends (prefixWord ++ tailWord_257544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257547 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_257547 : Nat := 118140960795 + 257547 * 2 ^ 59
def prefixEnd_257547 : Nat := 4983230072969 + 3 ^ 40 * 257547 * 2
def baseEnd_257547 : Nat := 117551468554319182113839

theorem tailTrace_257547 : CollatzResearch.WordTrace tailWord_257547 prefixEnd_257547 117551468554319182113839 := by
  unfold tailWord_257547
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393510797958679370842895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6262340531972452913895263 9393510797958679370842895)
  ·
    refine ⟨14090266196938019056264343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9393510797958679370842895 14090266196938019056264343)
    ·
      refine ⟨21135399295407028584396515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14090266196938019056264343 21135399295407028584396515)
      ·
        refine ⟨31703098943110542876594773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135399295407028584396515 31703098943110542876594773)
        ·
          refine ⟨371520690739576674335095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 31703098943110542876594773 371520690739576674335095)
          ·
            refine ⟨557281036109365011502643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371520690739576674335095 557281036109365011502643)
            ·
              refine ⟨835921554164047517253965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557281036109365011502643 835921554164047517253965)
              ·
                refine ⟨313470582811517818970237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835921554164047517253965 313470582811517818970237)
                ·
                  refine ⟨117551468554319182113839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313470582811517818970237 117551468554319182113839)
                  ·
                    rfl

theorem cell20_257547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_257547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257547 prefixEnd_257547 := by exact prefixLift 257547
  have htrace : WordTrace (prefixWord ++ tailWord_257547) baseStart_257547 baseEnd_257547 := by
    simpa [prefixWord, tailWord_257547, baseEnd_257547] using wordTrace_append hprefix tailTrace_257547
  have hstable : (prefixWord ++ tailWord_257547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257547).length < 2 ^ (prefixWord ++ tailWord_257547).sum := by decide
  have hdescent : baseEnd_257547 < baseStart_257547 := by decide
  rcases family_descends (prefixWord ++ tailWord_257547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257599 : List Nat := [1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_257599 : Nat := 118140960795 + 257599 * 2 ^ 59
def prefixEnd_257599 : Nat := 4983230072969 + 3 ^ 40 * 257599 * 2
def baseEnd_257599 : Nat := 39191734257079370793431

theorem tailTrace_257599 : CollatzResearch.WordTrace tailWord_257599 prefixEnd_257599 39191734257079370793431 := by
  unfold tailWord_257599
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395407393770292251735851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6263604929180194834490567 9395407393770292251735851)
  ·
    refine ⟨14093111090655438377603777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395407393770292251735851 14093111090655438377603777)
    ·
      refine ⟨10569833317991578783202833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14093111090655438377603777 10569833317991578783202833)
      ·
        refine ⟨7927374988493684087402125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10569833317991578783202833 7927374988493684087402125)
        ·
          refine ⟨2972765620685131532775797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7927374988493684087402125 2972765620685131532775797)
          ·
            refine ⟨278696776939231081197731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2972765620685131532775797 278696776939231081197731)
            ·
              refine ⟨418045165408846621796597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278696776939231081197731 418045165408846621796597)
              ·
                refine ⟨39191734257079370793431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418045165408846621796597 39191734257079370793431)
                ·
                  rfl

theorem cell20_257599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_257599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257599 prefixEnd_257599 := by exact prefixLift 257599
  have htrace : WordTrace (prefixWord ++ tailWord_257599) baseStart_257599 baseEnd_257599 := by
    simpa [prefixWord, tailWord_257599, baseEnd_257599] using wordTrace_append hprefix tailTrace_257599
  have hstable : (prefixWord ++ tailWord_257599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257599).length < 2 ^ (prefixWord ++ tailWord_257599).sum := by decide
  have hdescent : baseEnd_257599 < baseStart_257599 := by decide
  rcases family_descends (prefixWord ++ tailWord_257599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257622 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_257622 : Nat := 118140960795 + 257622 * 2 ^ 59
def prefixEnd_257622 : Nat := 4983230072969 + 3 ^ 40 * 257622 * 2
def baseEnd_257622 : Nat := 117585700597952254613533

theorem tailTrace_257622 : CollatzResearch.WordTrace tailWord_257622 prefixEnd_257622 117585700597952254613533 := by
  unfold tailWord_257622
  simp only [CollatzResearch.WordTrace]
  refine ⟨587265392042935448738945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6264164181791311453215413 587265392042935448738945)
  ·
    refine ⟨440449044032201586554209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 587265392042935448738945 440449044032201586554209)
    ·
      refine ⟨330336783024151189915657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440449044032201586554209 330336783024151189915657)
      ·
        refine ⟨247752587268113392436743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330336783024151189915657 247752587268113392436743)
        ·
          refine ⟨371628880902170088655115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247752587268113392436743 371628880902170088655115)
          ·
            refine ⟨557443321353255132982673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371628880902170088655115 557443321353255132982673)
            ·
              refine ⟨418082491014941349737005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557443321353255132982673 418082491014941349737005)
              ·
                refine ⟨156780934130603006151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418082491014941349737005 156780934130603006151377)
                ·
                  refine ⟨117585700597952254613533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156780934130603006151377 117585700597952254613533)
                  ·
                    rfl

theorem cell20_257622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_257622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257622 prefixEnd_257622 := by exact prefixLift 257622
  have htrace : WordTrace (prefixWord ++ tailWord_257622) baseStart_257622 baseEnd_257622 := by
    simpa [prefixWord, tailWord_257622, baseEnd_257622] using wordTrace_append hprefix tailTrace_257622
  have hstable : (prefixWord ++ tailWord_257622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257622).length < 2 ^ (prefixWord ++ tailWord_257622).sum := by decide
  have hdescent : baseEnd_257622 < baseStart_257622 := by decide
  rcases family_descends (prefixWord ++ tailWord_257622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257640 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_257640 : Nat := 118140960795 + 257640 * 2 ^ 59
def prefixEnd_257640 : Nat := 4983230072969 + 3 ^ 40 * 257640 * 2
def baseEnd_257640 : Nat := 117593916288424192013459

theorem tailTrace_257640 : CollatzResearch.WordTrace tailWord_257640 prefixEnd_257640 117593916288424192013459 := by
  unfold tailWord_257640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698451393310878126989187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6264601857747837502652249 4698451393310878126989187)
  ·
    refine ⟨7047677089966317190483781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698451393310878126989187 7047677089966317190483781)
    ·
      refine ⟨1321439454368684473215709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7047677089966317190483781 1321439454368684473215709)
      ·
        refine ⟨495539795388256677455891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1321439454368684473215709 495539795388256677455891)
        ·
          refine ⟨743309693082385016183837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495539795388256677455891 743309693082385016183837)
          ·
            refine ⟨278741134905894381068939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743309693082385016183837 278741134905894381068939)
            ·
              refine ⟨418111702358841571603409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278741134905894381068939 418111702358841571603409)
              ·
                refine ⟨313583776769131178702557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418111702358841571603409 313583776769131178702557)
                ·
                  refine ⟨117593916288424192013459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313583776769131178702557 117593916288424192013459)
                  ·
                    rfl

theorem cell20_257640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_257640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257640 prefixEnd_257640 := by exact prefixLift 257640
  have htrace : WordTrace (prefixWord ++ tailWord_257640) baseStart_257640 baseEnd_257640 := by
    simpa [prefixWord, tailWord_257640, baseEnd_257640] using wordTrace_append hprefix tailTrace_257640
  have hstable : (prefixWord ++ tailWord_257640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257640).length < 2 ^ (prefixWord ++ tailWord_257640).sum := by decide
  have hdescent : baseEnd_257640 < baseStart_257640 := by decide
  rcases family_descends (prefixWord ++ tailWord_257640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257692 : List Nat := [2, 2, 3, 2, 4, 1, 6]
def baseStart_257692 : Nat := 118140960795 + 257692 * 2 ^ 59
def prefixEnd_257692 : Nat := 4983230072969 + 3 ^ 40 * 257692 * 2
def baseEnd_257692 : Nat := 13068627833927013586657

theorem tailTrace_257692 : CollatzResearch.WordTrace tailWord_257692 prefixEnd_257692 13068627833927013586657 := by
  unfold tailWord_257692
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699399691216684567435665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6265866254955579423247553 4699399691216684567435665)
  ·
    refine ⟨3524549768412513425576749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4699399691216684567435665 3524549768412513425576749)
    ·
      refine ⟨1321706163154692534591281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3524549768412513425576749 1321706163154692534591281)
      ·
        refine ⟨991279622366019400943461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1321706163154692534591281 991279622366019400943461)
        ·
          refine ⟨185864929193628637676899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 991279622366019400943461 185864929193628637676899)
          ·
            refine ⟨278797393790442956515349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185864929193628637676899 278797393790442956515349)
            ·
              refine ⟨13068627833927013586657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278797393790442956515349 13068627833927013586657)
              ·
                rfl

theorem cell20_257692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 6].length) (baseStart_257692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257692 prefixEnd_257692 := by exact prefixLift 257692
  have htrace : WordTrace (prefixWord ++ tailWord_257692) baseStart_257692 baseEnd_257692 := by
    simpa [prefixWord, tailWord_257692, baseEnd_257692] using wordTrace_append hprefix tailTrace_257692
  have hstable : (prefixWord ++ tailWord_257692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257692).length < 2 ^ (prefixWord ++ tailWord_257692).sum := by decide
  have hdescent : baseEnd_257692 < baseStart_257692 := by decide
  rcases family_descends (prefixWord ++ tailWord_257692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257696 : List Nat := [2, 1, 1, 4, 3, 1, 8]
def baseStart_257696 : Nat := 118140960795 + 257696 * 2 ^ 59
def prefixEnd_257696 : Nat := 4983230072969 + 3 ^ 40 * 257696 * 2
def baseEnd_257696 : Nat := 13068830690481876238507

theorem tailTrace_257696 : CollatzResearch.WordTrace tailWord_257696 prefixEnd_257696 13068830690481876238507 := by
  unfold tailWord_257696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699472637209438909008471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6265963516279251878677961 4699472637209438909008471)
  ·
    refine ⟨7049208955814158363512707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699472637209438909008471 7049208955814158363512707)
    ·
      refine ⟨10573813433721237545269061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7049208955814158363512707 10573813433721237545269061)
      ·
        refine ⟨1982590018822732039737949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10573813433721237545269061 1982590018822732039737949)
        ·
          refine ⟨743471257058524514901731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1982590018822732039737949 743471257058524514901731)
          ·
            refine ⟨1115206885587786772352597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743471257058524514901731 1115206885587786772352597)
            ·
              refine ⟨13068830690481876238507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1115206885587786772352597 13068830690481876238507)
              ·
                rfl

theorem cell20_257696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_257696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257696 prefixEnd_257696 := by exact prefixLift 257696
  have htrace : WordTrace (prefixWord ++ tailWord_257696) baseStart_257696 baseEnd_257696 := by
    simpa [prefixWord, tailWord_257696, baseEnd_257696] using wordTrace_append hprefix tailTrace_257696
  have hstable : (prefixWord ++ tailWord_257696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257696).length < 2 ^ (prefixWord ++ tailWord_257696).sum := by decide
  have hdescent : baseEnd_257696 < baseStart_257696 := by decide
  rcases family_descends (prefixWord ++ tailWord_257696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257761 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 2]
def baseStart_257761 : Nat := 118140960795 + 257761 * 2 ^ 59
def prefixEnd_257761 : Nat := 4983230072969 + 3 ^ 40 * 257761 * 2
def baseEnd_257761 : Nat := 117649143985485548979631

theorem tailTrace_257761 : CollatzResearch.WordTrace tailWord_257761 prefixEnd_257761 117649143985485548979631 := by
  unfold tailWord_257761
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401316019183393919133137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6267544012788929279422091 9401316019183393919133137)
  ·
    refine ⟨7050987014387545439349853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9401316019183393919133137 7050987014387545439349853)
    ·
      refine ⟨2644120130395329539756195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7050987014387545439349853 2644120130395329539756195)
      ·
        refine ⟨3966180195592994309634293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644120130395329539756195 3966180195592994309634293)
        ·
          refine ⟨371829393336843216528215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3966180195592994309634293 371829393336843216528215)
          ·
            refine ⟨557744090005264824792323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371829393336843216528215 557744090005264824792323)
            ·
              refine ⟨836616135007897237188485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557744090005264824792323 836616135007897237188485)
              ·
                refine ⟨156865525313980731972841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836616135007897237188485 156865525313980731972841)
                ·
                  refine ⟨117649143985485548979631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156865525313980731972841 117649143985485548979631)
                  ·
                    rfl

theorem cell20_257761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_257761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257761 prefixEnd_257761 := by exact prefixLift 257761
  have htrace : WordTrace (prefixWord ++ tailWord_257761) baseStart_257761 baseEnd_257761 := by
    simpa [prefixWord, tailWord_257761, baseEnd_257761] using wordTrace_append hprefix tailTrace_257761
  have hstable : (prefixWord ++ tailWord_257761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257761).length < 2 ^ (prefixWord ++ tailWord_257761).sum := by decide
  have hdescent : baseEnd_257761 < baseStart_257761 := by decide
  rcases family_descends (prefixWord ++ tailWord_257761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257765 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_257765 : Nat := 118140960795 + 257765 * 2 ^ 59
def prefixEnd_257765 : Nat := 4983230072969 + 3 ^ 40 * 257765 * 2
def baseEnd_257765 : Nat := 117650969694479312846281

theorem tailTrace_257765 : CollatzResearch.WordTrace tailWord_257765 prefixEnd_257765 117650969694479312846281 := by
  unfold tailWord_257765
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401461911168902602278749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6267641274112601734852499 9401461911168902602278749)
  ·
    refine ⟨3525548216688338475854531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9401461911168902602278749 3525548216688338475854531)
    ·
      refine ⟨5288322325032507713781797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525548216688338475854531 5288322325032507713781797)
      ·
        refine ⟨991560435943595196334087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5288322325032507713781797 991560435943595196334087)
        ·
          refine ⟨1487340653915392794501131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991560435943595196334087 1487340653915392794501131)
          ·
            refine ⟨2231010980873089191751697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487340653915392794501131 2231010980873089191751697)
            ·
              refine ⟨1673258235654816893813773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231010980873089191751697 1673258235654816893813773)
              ·
                refine ⟨627471838370556335180165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673258235654816893813773 627471838370556335180165)
                ·
                  refine ⟨117650969694479312846281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627471838370556335180165 117650969694479312846281)
                  ·
                    rfl

theorem cell20_257765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_257765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257765 prefixEnd_257765 := by exact prefixLift 257765
  have htrace : WordTrace (prefixWord ++ tailWord_257765) baseStart_257765 baseEnd_257765 := by
    simpa [prefixWord, tailWord_257765, baseEnd_257765] using wordTrace_append hprefix tailTrace_257765
  have hstable : (prefixWord ++ tailWord_257765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257765).length < 2 ^ (prefixWord ++ tailWord_257765).sum := by decide
  have hdescent : baseEnd_257765 < baseStart_257765 := by decide
  rcases family_descends (prefixWord ++ tailWord_257765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257772 : List Nat := [2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_257772 : Nat := 118140960795 + 257772 * 2 ^ 59
def prefixEnd_257772 : Nat := 4983230072969 + 3 ^ 40 * 257772 * 2
def baseEnd_257772 : Nat := 39218054895072799870973

theorem tailTrace_257772 : CollatzResearch.WordTrace tailWord_257772 prefixEnd_257772 39218054895072799870973 := by
  unfold tailWord_257772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700858611071771398891785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6267811481429028531855713 4700858611071771398891785)
  ·
    refine ⟨3525643958303828549168839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4700858611071771398891785 3525643958303828549168839)
    ·
      refine ⟨5288465937455742823753259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525643958303828549168839 5288465937455742823753259)
      ·
        refine ⟨7932698906183614235629889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288465937455742823753259 7932698906183614235629889)
        ·
          refine ⟨5949524179637710676722417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932698906183614235629889 5949524179637710676722417)
          ·
            refine ⟨4462143134728283007541813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5949524179637710676722417 4462143134728283007541813)
            ·
              refine ⟨418325918880776531957045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4462143134728283007541813 418325918880776531957045)
              ·
                refine ⟨39218054895072799870973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418325918880776531957045 39218054895072799870973)
                ·
                  rfl

theorem cell20_257772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_257772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257772 prefixEnd_257772 := by exact prefixLift 257772
  have htrace : WordTrace (prefixWord ++ tailWord_257772) baseStart_257772 baseEnd_257772 := by
    simpa [prefixWord, tailWord_257772, baseEnd_257772] using wordTrace_append hprefix tailTrace_257772
  have hstable : (prefixWord ++ tailWord_257772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257772).length < 2 ^ (prefixWord ++ tailWord_257772).sum := by decide
  have hdescent : baseEnd_257772 < baseStart_257772 := by decide
  rcases family_descends (prefixWord ++ tailWord_257772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257782 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_257782 : Nat := 118140960795 + 257782 * 2 ^ 59
def prefixEnd_257782 : Nat := 4983230072969 + 3 ^ 40 * 257782 * 2
def baseEnd_257782 : Nat := 117658728957702809279545

theorem tailTrace_257782 : CollatzResearch.WordTrace tailWord_257782 prefixEnd_257782 117658728957702809279545 := by
  unfold tailWord_257782
  simp only [CollatzResearch.WordTrace]
  refine ⟨587630122006707156602975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6268054634738209670431733 587630122006707156602975)
  ·
    refine ⟨881445183010060734904463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 587630122006707156602975 881445183010060734904463)
    ·
      refine ⟨1322167774515091102356695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881445183010060734904463 1322167774515091102356695)
      ·
        refine ⟨1983251661772636653535043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322167774515091102356695 1983251661772636653535043)
        ·
          refine ⟨2974877492658954980302565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983251661772636653535043 2974877492658954980302565)
          ·
            refine ⟨557789529873554058806731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2974877492658954980302565 557789529873554058806731)
            ·
              refine ⟨836684294810331088210097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557789529873554058806731 836684294810331088210097)
              ·
                refine ⟨627513221107748316157573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836684294810331088210097 627513221107748316157573)
                ·
                  refine ⟨117658728957702809279545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627513221107748316157573 117658728957702809279545)
                  ·
                    rfl

theorem cell20_257782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_257782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257782 prefixEnd_257782 := by exact prefixLift 257782
  have htrace : WordTrace (prefixWord ++ tailWord_257782) baseStart_257782 baseEnd_257782 := by
    simpa [prefixWord, tailWord_257782, baseEnd_257782] using wordTrace_append hprefix tailTrace_257782
  have hstable : (prefixWord ++ tailWord_257782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257782).length < 2 ^ (prefixWord ++ tailWord_257782).sum := by decide
  have hdescent : baseEnd_257782 < baseStart_257782 := by decide
  rcases family_descends (prefixWord ++ tailWord_257782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257805 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 3]
def baseStart_257805 : Nat := 118140960795 + 257805 * 2 ^ 59
def prefixEnd_257805 : Nat := 4983230072969 + 3 ^ 40 * 257805 * 2
def baseEnd_257805 : Nat := 117669226784416951512785

theorem tailTrace_257805 : CollatzResearch.WordTrace tailWord_257805 prefixEnd_257805 117669226784416951512785 := by
  unfold tailWord_257805
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402920831023989433734869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6268613887349326289156579 9402920831023989433734869)
  ·
    refine ⟨220380956977124752353161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9402920831023989433734869 220380956977124752353161)
    ·
      refine ⟨165285717732843564264871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220380956977124752353161 165285717732843564264871)
      ·
        refine ⟨247928576599265346397307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165285717732843564264871 247928576599265346397307)
        ·
          refine ⟨371892864898898019595961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247928576599265346397307 371892864898898019595961)
          ·
            refine ⟨278919648674173514696971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371892864898898019595961 278919648674173514696971)
            ·
              refine ⟨418379473011260272045457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278919648674173514696971 418379473011260272045457)
              ·
                refine ⟨313784604758445204034093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418379473011260272045457 313784604758445204034093)
                ·
                  refine ⟨117669226784416951512785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313784604758445204034093 117669226784416951512785)
                  ·
                    rfl

theorem cell20_257805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_257805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257805 prefixEnd_257805 := by exact prefixLift 257805
  have htrace : WordTrace (prefixWord ++ tailWord_257805) baseStart_257805 baseEnd_257805 := by
    simpa [prefixWord, tailWord_257805, baseEnd_257805] using wordTrace_append hprefix tailTrace_257805
  have hstable : (prefixWord ++ tailWord_257805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257805).length < 2 ^ (prefixWord ++ tailWord_257805).sum := by decide
  have hdescent : baseEnd_257805 < baseStart_257805 := by decide
  rcases family_descends (prefixWord ++ tailWord_257805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257813 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_257813 : Nat := 118140960795 + 257813 * 2 ^ 59
def prefixEnd_257813 : Nat := 4983230072969 + 3 ^ 40 * 257813 * 2
def baseEnd_257813 : Nat := 117672878202404479246085

theorem tailTrace_257813 : CollatzResearch.WordTrace tailWord_257813 prefixEnd_257813 117672878202404479246085 := by
  unfold tailWord_257813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403212614995006800026093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6268808409996671200017395 9403212614995006800026093)
  ·
    refine ⟨3526204730623127550009785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9403212614995006800026093 3526204730623127550009785)
    ·
      refine ⟨2644653547967345662507339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3526204730623127550009785 2644653547967345662507339)
      ·
        refine ⟨3966980321951018493761009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644653547967345662507339 3966980321951018493761009)
        ·
          refine ⟨2975235241463263870320757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966980321951018493761009 2975235241463263870320757)
          ·
            refine ⟨278928303887180987842571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2975235241463263870320757 278928303887180987842571)
            ·
              refine ⟨418392455830771481763857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278928303887180987842571 418392455830771481763857)
              ·
                refine ⟨313794341873078611322893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418392455830771481763857 313794341873078611322893)
                ·
                  refine ⟨117672878202404479246085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313794341873078611322893 117672878202404479246085)
                  ·
                    rfl

theorem cell20_257813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_257813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257813 prefixEnd_257813 := by exact prefixLift 257813
  have htrace : WordTrace (prefixWord ++ tailWord_257813) baseStart_257813 baseEnd_257813 := by
    simpa [prefixWord, tailWord_257813, baseEnd_257813] using wordTrace_append hprefix tailTrace_257813
  have hstable : (prefixWord ++ tailWord_257813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257813).length < 2 ^ (prefixWord ++ tailWord_257813).sum := by decide
  have hdescent : baseEnd_257813 < baseStart_257813 := by decide
  rcases family_descends (prefixWord ++ tailWord_257813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257820 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_257820 : Nat := 118140960795 + 257820 * 2 ^ 59
def prefixEnd_257820 : Nat := 4983230072969 + 3 ^ 40 * 257820 * 2
def baseEnd_257820 : Nat := 117676073193143566012723

theorem tailTrace_257820 : CollatzResearch.WordTrace tailWord_257820 prefixEnd_257820 117676073193143566012723 := by
  unfold tailWord_257820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701733962984823497765457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6268978617313097997020609 4701733962984823497765457)
  ·
    refine ⟨3526300472238617623324093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4701733962984823497765457 3526300472238617623324093)
    ·
      refine ⟨1322362677089481608746535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3526300472238617623324093 1322362677089481608746535)
      ·
        refine ⟨1983544015634222413119803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322362677089481608746535 1983544015634222413119803)
        ·
          refine ⟨2975316023451333619679705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983544015634222413119803 2975316023451333619679705)
          ·
            refine ⟨2231487017588500214759779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975316023451333619679705 2231487017588500214759779)
            ·
              refine ⟨3347230526382750322139669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231487017588500214759779 3347230526382750322139669)
              ·
                refine ⟨156901430924191421350297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3347230526382750322139669 156901430924191421350297)
                ·
                  refine ⟨117676073193143566012723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156901430924191421350297 117676073193143566012723)
                  ·
                    rfl

theorem cell20_257820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_257820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257820 prefixEnd_257820 := by exact prefixLift 257820
  have htrace : WordTrace (prefixWord ++ tailWord_257820) baseStart_257820 baseEnd_257820 := by
    simpa [prefixWord, tailWord_257820, baseEnd_257820] using wordTrace_append hprefix tailTrace_257820
  have hstable : (prefixWord ++ tailWord_257820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257820).length < 2 ^ (prefixWord ++ tailWord_257820).sum := by decide
  have hdescent : baseEnd_257820 < baseStart_257820 := by decide
  rcases family_descends (prefixWord ++ tailWord_257820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257841 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_257841 : Nat := 118140960795 + 257841 * 2 ^ 59
def prefixEnd_257841 : Nat := 4983230072969 + 3 ^ 40 * 257841 * 2
def baseEnd_257841 : Nat := 117685658165360826312637

theorem tailTrace_257841 : CollatzResearch.WordTrace tailWord_257841 prefixEnd_257841 117685658165360826312637 := by
  unfold tailWord_257841
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404233858893567582045377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6269489239262378388030251 9404233858893567582045377)
  ·
    refine ⟨7053175394170175686534033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9404233858893567582045377 7053175394170175686534033)
    ·
      refine ⟨5289881545627631764900525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7053175394170175686534033 5289881545627631764900525)
      ·
        refine ⟨1983705579610361911837697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5289881545627631764900525 1983705579610361911837697)
        ·
          refine ⟨1487779184707771433878273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983705579610361911837697 1487779184707771433878273)
          ·
            refine ⟨1115834388530828575408705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487779184707771433878273 1115834388530828575408705)
            ·
              refine ⟨836875791398121431556529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115834388530828575408705 836875791398121431556529)
              ·
                refine ⟨627656843548591073667397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836875791398121431556529 627656843548591073667397)
                ·
                  refine ⟨117685658165360826312637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627656843548591073667397 117685658165360826312637)
                  ·
                    rfl

theorem cell20_257841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_257841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257841 prefixEnd_257841 := by exact prefixLift 257841
  have htrace : WordTrace (prefixWord ++ tailWord_257841) baseStart_257841 baseEnd_257841 := by
    simpa [prefixWord, tailWord_257841, baseEnd_257841] using wordTrace_append hprefix tailTrace_257841
  have hstable : (prefixWord ++ tailWord_257841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257841).length < 2 ^ (prefixWord ++ tailWord_257841).sum := by decide
  have hdescent : baseEnd_257841 < baseStart_257841 := by decide
  rcases family_descends (prefixWord ++ tailWord_257841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257844 : List Nat := [2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_257844 : Nat := 118140960795 + 257844 * 2 ^ 59
def prefixEnd_257844 : Nat := 4983230072969 + 3 ^ 40 * 257844 * 2
def baseEnd_257844 : Nat := 39229009149035383070875

theorem tailTrace_257844 : CollatzResearch.WordTrace tailWord_257844 prefixEnd_257844 39229009149035383070875 := by
  unfold tailWord_257844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702171638941349547202293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6269562185255132729603057 4702171638941349547202293)
  ·
    refine ⟨440828591150751520050215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4702171638941349547202293 440828591150751520050215)
    ·
      refine ⟨661242886726127280075323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440828591150751520050215 661242886726127280075323)
      ·
        refine ⟨991864330089190920112985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661242886726127280075323 991864330089190920112985)
        ·
          refine ⟨743898247566893190084739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991864330089190920112985 743898247566893190084739)
          ·
            refine ⟨1115847371350339785127109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743898247566893190084739 1115847371350339785127109)
            ·
              refine ⟨209221382128188709711333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1115847371350339785127109 209221382128188709711333)
              ·
                refine ⟨39229009149035383070875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209221382128188709711333 39229009149035383070875)
                ·
                  rfl

theorem cell20_257844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_257844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257844 prefixEnd_257844 := by exact prefixLift 257844
  have htrace : WordTrace (prefixWord ++ tailWord_257844) baseStart_257844 baseEnd_257844 := by
    simpa [prefixWord, tailWord_257844, baseEnd_257844] using wordTrace_append hprefix tailTrace_257844
  have hstable : (prefixWord ++ tailWord_257844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257844).length < 2 ^ (prefixWord ++ tailWord_257844).sum := by decide
  have hdescent : baseEnd_257844 < baseStart_257844 := by decide
  rcases family_descends (prefixWord ++ tailWord_257844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257848 : List Nat := [2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_257848 : Nat := 118140960795 + 257848 * 2 ^ 59
def prefixEnd_257848 : Nat := 4983230072969 + 3 ^ 40 * 257848 * 2
def baseEnd_257848 : Nat := 39229617718699971026425

theorem tailTrace_257848 : CollatzResearch.WordTrace tailWord_257848 prefixEnd_257848 39229617718699971026425 := by
  unfold tailWord_257848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702244584934103888775099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6269659446578805185033465 4702244584934103888775099)
  ·
    refine ⟨7053366877401155833162649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4702244584934103888775099 7053366877401155833162649)
    ·
      refine ⟨5290025158050866874871987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7053366877401155833162649 5290025158050866874871987)
      ·
        refine ⟨7935037737076300312307981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290025158050866874871987 7935037737076300312307981)
        ·
          refine ⟨2975639151403612617115493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7935037737076300312307981 2975639151403612617115493)
          ·
            refine ⟨557932340888177365709155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2975639151403612617115493 557932340888177365709155)
            ·
              refine ⟨836898511332266048563733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557932340888177365709155 836898511332266048563733)
              ·
                refine ⟨39229617718699971026425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 836898511332266048563733 39229617718699971026425)
                ·
                  rfl

theorem cell20_257848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_257848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257848 prefixEnd_257848 := by exact prefixLift 257848
  have htrace : WordTrace (prefixWord ++ tailWord_257848) baseStart_257848 baseEnd_257848 := by
    simpa [prefixWord, tailWord_257848, baseEnd_257848] using wordTrace_append hprefix tailTrace_257848
  have hstable : (prefixWord ++ tailWord_257848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257848).length < 2 ^ (prefixWord ++ tailWord_257848).sum := by decide
  have hdescent : baseEnd_257848 < baseStart_257848 := by decide
  rcases family_descends (prefixWord ++ tailWord_257848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257854 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_257854 : Nat := 118140960795 + 257854 * 2 ^ 59
def prefixEnd_257854 : Nat := 4983230072969 + 3 ^ 40 * 257854 * 2
def baseEnd_257854 : Nat := 117691591719590558879251

theorem tailTrace_257854 : CollatzResearch.WordTrace tailWord_257854 prefixEnd_257854 117691591719590558879251 := by
  unfold tailWord_257854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175588500980808850283577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6269805338564313868179077 1175588500980808850283577)
  ·
    refine ⟨881691375735606637712683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1175588500980808850283577 881691375735606637712683)
    ·
      refine ⟨1322537063603409956569025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881691375735606637712683 1322537063603409956569025)
      ·
        refine ⟨991902797702557467426769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322537063603409956569025 991902797702557467426769)
        ·
          refine ⟨743927098276918100570077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991902797702557467426769 743927098276918100570077)
          ·
            refine ⟨278972661853844287713779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743927098276918100570077 278972661853844287713779)
            ·
              refine ⟨418458992780766431570669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278972661853844287713779 418458992780766431570669)
              ·
                refine ⟨156922122292787411839001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418458992780766431570669 156922122292787411839001)
                ·
                  refine ⟨117691591719590558879251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156922122292787411839001 117691591719590558879251)
                  ·
                    rfl

theorem cell20_257854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_257854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257854 prefixEnd_257854 := by exact prefixLift 257854
  have htrace : WordTrace (prefixWord ++ tailWord_257854) baseStart_257854 baseEnd_257854 := by
    simpa [prefixWord, tailWord_257854, baseEnd_257854] using wordTrace_append hprefix tailTrace_257854
  have hstable : (prefixWord ++ tailWord_257854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257854).length < 2 ^ (prefixWord ++ tailWord_257854).sum := by decide
  have hdescent : baseEnd_257854 < baseStart_257854 := by decide
  rcases family_descends (prefixWord ++ tailWord_257854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257927 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_257927 : Nat := 118140960795 + 257927 * 2 ^ 59
def prefixEnd_257927 : Nat := 4983230072969 + 3 ^ 40 * 257927 * 2
def baseEnd_257927 : Nat := 117724910908726749445619

theorem tailTrace_257927 : CollatzResearch.WordTrace tailWord_257927 prefixEnd_257927 117724910908726749445619 := by
  unfold tailWord_257927
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407370536582004269676035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6271580357721336179784023 9407370536582004269676035)
  ·
    refine ⟨14111055804873006404514053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407370536582004269676035 14111055804873006404514053)
    ·
      refine ⟨2645822963413688700846385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14111055804873006404514053 2645822963413688700846385)
      ·
        refine ⟨1984367222560266525634789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645822963413688700846385 1984367222560266525634789)
        ·
          refine ⟨372068854230049973556523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1984367222560266525634789 372068854230049973556523)
          ·
            refine ⟨558103281345074960334785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372068854230049973556523 558103281345074960334785)
            ·
              refine ⟨418577461008806220251089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558103281345074960334785 418577461008806220251089)
              ·
                refine ⟨313933095756604665188317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418577461008806220251089 313933095756604665188317)
                ·
                  refine ⟨117724910908726749445619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313933095756604665188317 117724910908726749445619)
                  ·
                    rfl

theorem cell20_257927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_257927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257927 prefixEnd_257927 := by exact prefixLift 257927
  have htrace : WordTrace (prefixWord ++ tailWord_257927) baseStart_257927 baseEnd_257927 := by
    simpa [prefixWord, tailWord_257927, baseEnd_257927] using wordTrace_append hprefix tailTrace_257927
  have hstable : (prefixWord ++ tailWord_257927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257927).length < 2 ^ (prefixWord ++ tailWord_257927).sum := by decide
  have hdescent : baseEnd_257927 < baseStart_257927 := by decide
  rcases family_descends (prefixWord ++ tailWord_257927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257976 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_257976 : Nat := 118140960795 + 257976 * 2 ^ 59
def prefixEnd_257976 : Nat := 4983230072969 + 3 ^ 40 * 257976 * 2
def baseEnd_257976 : Nat := 117747275843900356812085

theorem tailTrace_257976 : CollatzResearch.WordTrace tailWord_257976 prefixEnd_257976 117747275843900356812085 := by
  unfold tailWord_257976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704578856702242819104891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6272771808936323758806521 4704578856702242819104891)
  ·
    refine ⟨7056868285053364228657337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4704578856702242819104891 7056868285053364228657337)
    ·
      refine ⟨5292651213790023171493003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7056868285053364228657337 5292651213790023171493003)
      ·
        refine ⟨7938976820685034757239505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292651213790023171493003 7938976820685034757239505)
        ·
          refine ⟨5954232615513776067929629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7938976820685034757239505 5954232615513776067929629)
          ·
            refine ⟨2232837230817666025473611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5954232615513776067929629 2232837230817666025473611)
            ·
              refine ⟨3349255846226499038210417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232837230817666025473611 3349255846226499038210417)
              ·
                refine ⟨2511941884669874278657813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349255846226499038210417 2511941884669874278657813)
                ·
                  refine ⟨117747275843900356812085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2511941884669874278657813 117747275843900356812085)
                  ·
                    rfl

theorem cell20_257976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_257976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257976 prefixEnd_257976 := by exact prefixLift 257976
  have htrace : WordTrace (prefixWord ++ tailWord_257976) baseStart_257976 baseEnd_257976 := by
    simpa [prefixWord, tailWord_257976, baseEnd_257976] using wordTrace_append hprefix tailTrace_257976
  have hstable : (prefixWord ++ tailWord_257976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257976).length < 2 ^ (prefixWord ++ tailWord_257976).sum := by decide
  have hdescent : baseEnd_257976 < baseStart_257976 := by decide
  rcases family_descends (prefixWord ++ tailWord_257976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257983 : List Nat := [1, 1, 2, 2, 2, 1, 11]
def baseStart_257983 : Nat := 118140960795 + 257983 * 2 ^ 59
def prefixEnd_257983 : Nat := 4983230072969 + 3 ^ 40 * 257983 * 2
def baseEnd_257983 : Nat := 13083385648293271508747

theorem tailTrace_257983 : CollatzResearch.WordTrace tailWord_257983 prefixEnd_257983 13083385648293271508747 := by
  unfold tailWord_257983
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409413024379125833714603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6272942016252750555809735 9409413024379125833714603)
  ·
    refine ⟨14114119536568688750571905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9409413024379125833714603 14114119536568688750571905)
    ·
      refine ⟨10585589652426516562928929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14114119536568688750571905 10585589652426516562928929)
      ·
        refine ⟨7939192239319887422196697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585589652426516562928929 7939192239319887422196697)
        ·
          refine ⟨5954394179489915566647523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939192239319887422196697 5954394179489915566647523)
          ·
            refine ⟨8931591269234873349971285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954394179489915566647523 8931591269234873349971285)
            ·
              refine ⟨13083385648293271508747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8931591269234873349971285 13083385648293271508747)
              ·
                rfl

theorem cell20_257983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_257983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_257983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_257983 prefixEnd_257983 := by exact prefixLift 257983
  have htrace : WordTrace (prefixWord ++ tailWord_257983) baseStart_257983 baseEnd_257983 := by
    simpa [prefixWord, tailWord_257983, baseEnd_257983] using wordTrace_append hprefix tailTrace_257983
  have hstable : (prefixWord ++ tailWord_257983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257983).length < 2 ^ (prefixWord ++ tailWord_257983).sum := by decide
  have hdescent : baseEnd_257983 < baseStart_257983 := by decide
  rcases family_descends (prefixWord ++ tailWord_257983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258013 : List Nat := [1, 4, 3, 1, 4, 1, 2, 4]
def baseStart_258013 : Nat := 118140960795 + 258013 * 2 ^ 59
def prefixEnd_258013 : Nat := 4983230072969 + 3 ^ 40 * 258013 * 2
def baseEnd_258013 : Nat := 39254721217364224192867

theorem tailTrace_258013 : CollatzResearch.WordTrace tailWord_258013 prefixEnd_258013 39254721217364224192867 := by
  unfold tailWord_258013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9410507214270440957306693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6273671476180293971537795 9410507214270440957306693)
  ·
    refine ⟨1764470102675707679495005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9410507214270440957306693 1764470102675707679495005)
    ·
      refine ⟨661676288503390379810627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1764470102675707679495005 661676288503390379810627)
      ·
        refine ⟨992514432755085569715941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661676288503390379810627 992514432755085569715941)
        ·
          refine ⟨186096456141578544321739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 992514432755085569715941 186096456141578544321739)
          ·
            refine ⟨279144684212367816482609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186096456141578544321739 279144684212367816482609)
            ·
              refine ⟨209358513159275862361957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279144684212367816482609 209358513159275862361957)
              ·
                refine ⟨39254721217364224192867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209358513159275862361957 39254721217364224192867)
                ·
                  rfl

theorem cell20_258013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_258013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258013 prefixEnd_258013 := by exact prefixLift 258013
  have htrace : WordTrace (prefixWord ++ tailWord_258013) baseStart_258013 baseEnd_258013 := by
    simpa [prefixWord, tailWord_258013, baseEnd_258013] using wordTrace_append hprefix tailTrace_258013
  have hstable : (prefixWord ++ tailWord_258013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258013).length < 2 ^ (prefixWord ++ tailWord_258013).sum := by decide
  have hdescent : baseEnd_258013 < baseStart_258013 := by decide
  rcases family_descends (prefixWord ++ tailWord_258013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258045 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_258045 : Nat := 118140960795 + 258045 * 2 ^ 59
def prefixEnd_258045 : Nat := 4983230072969 + 3 ^ 40 * 258045 * 2
def baseEnd_258045 : Nat := 117778769324042783511803

theorem tailTrace_258045 : CollatzResearch.WordTrace tailWord_258045 prefixEnd_258045 117778769324042783511803 := by
  unfold tailWord_258045
  simp only [CollatzResearch.WordTrace]
  refine ⟨9411674350154510422471589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6274449566769673614981059 9411674350154510422471589)
  ·
    refine ⟨1764688940653970704213423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9411674350154510422471589 1764688940653970704213423)
    ·
      refine ⟨2647033410980956056320135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764688940653970704213423 2647033410980956056320135)
      ·
        refine ⟨3970550116471434084480203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647033410980956056320135 3970550116471434084480203)
        ·
          refine ⟨5955825174707151126720305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970550116471434084480203 5955825174707151126720305)
          ·
            refine ⟨4466868881030363345040229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5955825174707151126720305 4466868881030363345040229)
            ·
              refine ⟨837537915193193127195043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4466868881030363345040229 837537915193193127195043)
              ·
                refine ⟨1256306872789789690792565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837537915193193127195043 1256306872789789690792565)
                ·
                  refine ⟨117778769324042783511803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1256306872789789690792565 117778769324042783511803)
                  ·
                    rfl

theorem cell20_258045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_258045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258045 prefixEnd_258045 := by exact prefixLift 258045
  have htrace : WordTrace (prefixWord ++ tailWord_258045) baseStart_258045 baseEnd_258045 := by
    simpa [prefixWord, tailWord_258045, baseEnd_258045] using wordTrace_append hprefix tailTrace_258045
  have hstable : (prefixWord ++ tailWord_258045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258045).length < 2 ^ (prefixWord ++ tailWord_258045).sum := by decide
  have hdescent : baseEnd_258045 < baseStart_258045 := by decide
  rcases family_descends (prefixWord ++ tailWord_258045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258054 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_258054 : Nat := 118140960795 + 258054 * 2 ^ 59
def prefixEnd_258054 : Nat := 4983230072969 + 3 ^ 40 * 258054 * 2
def baseEnd_258054 : Nat := 117782877169278752211767

theorem tailTrace_258054 : CollatzResearch.WordTrace tailWord_258054 prefixEnd_258054 117782877169278752211767 := by
  unfold tailWord_258054
  simp only [CollatzResearch.WordTrace]
  refine ⟨294125081472559529985913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6274668404747936639699477 294125081472559529985913)
  ·
    refine ⟨220593811104419647489435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294125081472559529985913 220593811104419647489435)
    ·
      refine ⟨330890716656629471234153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220593811104419647489435 330890716656629471234153)
      ·
        refine ⟨248168037492472103425615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330890716656629471234153 248168037492472103425615)
        ·
          refine ⟨372252056238708155138423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248168037492472103425615 372252056238708155138423)
          ·
            refine ⟨558378084358062232707635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372252056238708155138423 558378084358062232707635)
            ·
              refine ⟨837567126537093349061453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558378084358062232707635 837567126537093349061453)
              ·
                refine ⟨314087672451410005898045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837567126537093349061453 314087672451410005898045)
                ·
                  refine ⟨117782877169278752211767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314087672451410005898045 117782877169278752211767)
                  ·
                    rfl

theorem cell20_258054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_258054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258054 prefixEnd_258054 := by exact prefixLift 258054
  have htrace : WordTrace (prefixWord ++ tailWord_258054) baseStart_258054 baseEnd_258054 := by
    simpa [prefixWord, tailWord_258054, baseEnd_258054] using wordTrace_append hprefix tailTrace_258054
  have hstable : (prefixWord ++ tailWord_258054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258054).length < 2 ^ (prefixWord ++ tailWord_258054).sum := by decide
  have hdescent : baseEnd_258054 < baseStart_258054 := by decide
  rcases family_descends (prefixWord ++ tailWord_258054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258058 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_258058 : Nat := 118140960795 + 258058 * 2 ^ 59
def prefixEnd_258058 : Nat := 4983230072969 + 3 ^ 40 * 258058 * 2
def baseEnd_258058 : Nat := 117784702878272516078417

theorem tailTrace_258058 : CollatzResearch.WordTrace tailWord_258058 prefixEnd_258058 117784702878272516078417 := by
  unfold tailWord_258058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353037124776853410673707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6274765666071609095129885 2353037124776853410673707)
  ·
    refine ⟨3529555687165280116010561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353037124776853410673707 3529555687165280116010561)
    ·
      refine ⟨2647166765373960087007921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3529555687165280116010561 2647166765373960087007921)
      ·
        refine ⟨1985375074030470065255941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647166765373960087007921 1985375074030470065255941)
        ·
          refine ⟨372257826380713137235489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1985375074030470065255941 372257826380713137235489)
          ·
            refine ⟨279193369785534852926617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372257826380713137235489 279193369785534852926617)
            ·
              refine ⟨209395027339151139694963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279193369785534852926617 209395027339151139694963)
              ·
                refine ⟨314092541008726709542445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209395027339151139694963 314092541008726709542445)
                ·
                  refine ⟨117784702878272516078417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314092541008726709542445 117784702878272516078417)
                  ·
                    rfl

theorem cell20_258058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_258058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258058 prefixEnd_258058 := by exact prefixLift 258058
  have htrace : WordTrace (prefixWord ++ tailWord_258058) baseStart_258058 baseEnd_258058 := by
    simpa [prefixWord, tailWord_258058, baseEnd_258058] using wordTrace_append hprefix tailTrace_258058
  have hstable : (prefixWord ++ tailWord_258058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258058).length < 2 ^ (prefixWord ++ tailWord_258058).sum := by decide
  have hdescent : baseEnd_258058 < baseStart_258058 := by decide
  rcases family_descends (prefixWord ++ tailWord_258058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258062 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_258062 : Nat := 118140960795 + 258062 * 2 ^ 59
def prefixEnd_258062 : Nat := 4983230072969 + 3 ^ 40 * 258062 * 2
def baseEnd_258062 : Nat := 117786528587266279945067

theorem tailTrace_258062 : CollatzResearch.WordTrace tailWord_258062 prefixEnd_258062 117786528587266279945067 := by
  unfold tailWord_258062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176536798886615290730055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6274862927395281550560293 1176536798886615290730055)
  ·
    refine ⟨1764805198329922936095083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1176536798886615290730055 1764805198329922936095083)
    ·
      refine ⟨2647207797494884404142625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764805198329922936095083 2647207797494884404142625)
      ·
        refine ⟨1985405848121163303106969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647207797494884404142625 1985405848121163303106969)
        ·
          refine ⟨1489054386090872477330227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985405848121163303106969 1489054386090872477330227)
          ·
            refine ⟨2233581579136308715995341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489054386090872477330227 2233581579136308715995341)
            ·
              refine ⟨837593092176115768498253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233581579136308715995341 837593092176115768498253)
              ·
                refine ⟨314097409566043413186845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837593092176115768498253 314097409566043413186845)
                ·
                  refine ⟨117786528587266279945067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314097409566043413186845 117786528587266279945067)
                  ·
                    rfl

theorem cell20_258062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_258062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258062 prefixEnd_258062 := by exact prefixLift 258062
  have htrace : WordTrace (prefixWord ++ tailWord_258062) baseStart_258062 baseEnd_258062 := by
    simpa [prefixWord, tailWord_258062, baseEnd_258062] using wordTrace_append hprefix tailTrace_258062
  have hstable : (prefixWord ++ tailWord_258062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258062).length < 2 ^ (prefixWord ++ tailWord_258062).sum := by decide
  have hdescent : baseEnd_258062 < baseStart_258062 := by decide
  rcases family_descends (prefixWord ++ tailWord_258062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258076 : List Nat := [2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_258076 : Nat := 118140960795 + 258076 * 2 ^ 59
def prefixEnd_258076 : Nat := 4983230072969 + 3 ^ 40 * 258076 * 2
def baseEnd_258076 : Nat := 39264306189581484492781

theorem tailTrace_258076 : CollatzResearch.WordTrace tailWord_258076 prefixEnd_258076 39264306189581484492781 := by
  unfold tailWord_258076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706402506521101358425041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6275203342028135144566721 4706402506521101358425041)
  ·
    refine ⟨3529801879890826018818781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4706402506521101358425041 3529801879890826018818781)
    ·
      refine ⟨1323675704959059757057043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3529801879890826018818781 1323675704959059757057043)
      ·
        refine ⟨1985513557438589635585565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323675704959059757057043 1985513557438589635585565)
        ·
          refine ⟨744567584039471113344587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1985513557438589635585565 744567584039471113344587)
          ·
            refine ⟨1116851376059206670016881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744567584039471113344587 1116851376059206670016881)
            ·
              refine ⟨837638532044405002512661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116851376059206670016881 837638532044405002512661)
              ·
                refine ⟨39264306189581484492781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 837638532044405002512661 39264306189581484492781)
                ·
                  rfl

theorem cell20_258076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_258076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258076 prefixEnd_258076 := by exact prefixLift 258076
  have htrace : WordTrace (prefixWord ++ tailWord_258076) baseStart_258076 baseEnd_258076 := by
    simpa [prefixWord, tailWord_258076, baseEnd_258076] using wordTrace_append hprefix tailTrace_258076
  have hstable : (prefixWord ++ tailWord_258076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258076).length < 2 ^ (prefixWord ++ tailWord_258076).sum := by decide
  have hdescent : baseEnd_258076 < baseStart_258076 := by decide
  rcases family_descends (prefixWord ++ tailWord_258076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258097 : List Nat := [1, 2, 2, 3, 1, 11]
def baseStart_258097 : Nat := 118140960795 + 258097 * 2 ^ 59
def prefixEnd_258097 : Nat := 4983230072969 + 3 ^ 40 * 258097 * 2
def baseEnd_258097 : Nat := 4363055686702285695491

theorem tailTrace_258097 : CollatzResearch.WordTrace tailWord_258097 prefixEnd_258097 4363055686702285695491 := by
  unfold tailWord_258097
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413570945966123303364545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6275713963977415535576363 9413570945966123303364545)
  ·
    refine ⟨7060178209474592477523409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9413570945966123303364545 7060178209474592477523409)
    ·
      refine ⟨5295133657105944358142557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7060178209474592477523409 5295133657105944358142557)
      ·
        refine ⟨1985675121414729134303459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5295133657105944358142557 1985675121414729134303459)
        ·
          refine ⟨2978512682122093701455189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985675121414729134303459 2978512682122093701455189)
          ·
            refine ⟨4363055686702285695491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2978512682122093701455189 4363055686702285695491)
            ·
              rfl

theorem cell20_258097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 11].length) (baseStart_258097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258097 prefixEnd_258097 := by exact prefixLift 258097
  have htrace : WordTrace (prefixWord ++ tailWord_258097) baseStart_258097 baseEnd_258097 := by
    simpa [prefixWord, tailWord_258097, baseEnd_258097] using wordTrace_append hprefix tailTrace_258097
  have hstable : (prefixWord ++ tailWord_258097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258097).length < 2 ^ (prefixWord ++ tailWord_258097).sum := by decide
  have hdescent : baseEnd_258097 < baseStart_258097 := by decide
  rcases family_descends (prefixWord ++ tailWord_258097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 2]
def baseStart_258107 : Nat := 118140960795 + 258107 * 2 ^ 59
def prefixEnd_258107 : Nat := 4983230072969 + 3 ^ 40 * 258107 * 2
def baseEnd_258107 : Nat := 117807067813446123444883

theorem tailTrace_258107 : CollatzResearch.WordTrace tailWord_258107 prefixEnd_258107 117807067813446123444883 := by
  unfold tailWord_258107
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413935675929895011228575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6275957117286596674152383 9413935675929895011228575)
  ·
    refine ⟨14120903513894842516842863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413935675929895011228575 14120903513894842516842863)
    ·
      refine ⟨21181355270842263775264295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120903513894842516842863 21181355270842263775264295)
      ·
        refine ⟨31772032906263395662896443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21181355270842263775264295 31772032906263395662896443)
        ·
          refine ⟨47658049359395093494344665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31772032906263395662896443 47658049359395093494344665)
          ·
            refine ⟨35743537019546320120758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47658049359395093494344665 35743537019546320120758499)
            ·
              refine ⟨53615305529319480181137749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35743537019546320120758499 53615305529319480181137749)
              ·
                refine ⟨157076090417928164593177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53615305529319480181137749 157076090417928164593177)
                ·
                  refine ⟨117807067813446123444883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157076090417928164593177 117807067813446123444883)
                  ·
                    rfl

theorem cell20_258107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2].length) (baseStart_258107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258107 prefixEnd_258107 := by exact prefixLift 258107
  have htrace : WordTrace (prefixWord ++ tailWord_258107) baseStart_258107 baseEnd_258107 := by
    simpa [prefixWord, tailWord_258107, baseEnd_258107] using wordTrace_append hprefix tailTrace_258107
  have hstable : (prefixWord ++ tailWord_258107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258107).length < 2 ^ (prefixWord ++ tailWord_258107).sum := by decide
  have hdescent : baseEnd_258107 < baseStart_258107 := by decide
  rcases family_descends (prefixWord ++ tailWord_258107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258110 : List Nat := [4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_258110 : Nat := 118140960795 + 258110 * 2 ^ 59
def prefixEnd_258110 : Nat := 4983230072969 + 3 ^ 40 * 258110 * 2
def baseEnd_258110 : Nat := 39269479031730482114957

theorem tailTrace_258110 : CollatzResearch.WordTrace tailWord_258110 prefixEnd_258110 39269479031730482114957 := by
  unfold tailWord_258110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176755636864878315448473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6276030063279351015725189 1176755636864878315448473)
  ·
    refine ⟨882566727648658736586355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1176755636864878315448473 882566727648658736586355)
    ·
      refine ⟨1323850091472988104879533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882566727648658736586355 1323850091472988104879533)
      ·
        refine ⟨496443784302370539329825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1323850091472988104879533 496443784302370539329825)
        ·
          refine ⟨372332838226777904497369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496443784302370539329825 372332838226777904497369)
          ·
            refine ⟨279249628670083428373027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372332838226777904497369 279249628670083428373027)
            ·
              refine ⟨418874443005125142559541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279249628670083428373027 418874443005125142559541)
              ·
                refine ⟨39269479031730482114957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418874443005125142559541 39269479031730482114957)
                ·
                  rfl

theorem cell20_258110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_258110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258110 prefixEnd_258110 := by exact prefixLift 258110
  have htrace : WordTrace (prefixWord ++ tailWord_258110) baseStart_258110 baseEnd_258110 := by
    simpa [prefixWord, tailWord_258110, baseEnd_258110] using wordTrace_append hprefix tailTrace_258110
  have hstable : (prefixWord ++ tailWord_258110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258110).length < 2 ^ (prefixWord ++ tailWord_258110).sum := by decide
  have hdescent : baseEnd_258110 < baseStart_258110 := by decide
  rcases family_descends (prefixWord ++ tailWord_258110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258121 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_258121 : Nat := 118140960795 + 258121 * 2 ^ 59
def prefixEnd_258121 : Nat := 4983230072969 + 3 ^ 40 * 258121 * 2
def baseEnd_258121 : Nat := 117813457794924296978159

theorem tailTrace_258121 : CollatzResearch.WordTrace tailWord_258121 prefixEnd_258121 117813457794924296978159 := by
  unfold tailWord_258121
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414446297879175402238217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6276297531919450268158811 9414446297879175402238217)
  ·
    refine ⟨7060834723409381551678663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9414446297879175402238217 7060834723409381551678663)
    ·
      refine ⟨10591252085114072327517995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060834723409381551678663 10591252085114072327517995)
      ·
        refine ⟨15886878127671108491276993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10591252085114072327517995 15886878127671108491276993)
        ·
          refine ⟨11915158595753331368457745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15886878127671108491276993 11915158595753331368457745)
          ·
            refine ⟨8936368946814998526343309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11915158595753331368457745 8936368946814998526343309)
            ·
              refine ⟨3351138355055624447378741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8936368946814998526343309 3351138355055624447378741)
              ·
                refine ⟨314169220786464791941757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3351138355055624447378741 314169220786464791941757)
                ·
                  refine ⟨117813457794924296978159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314169220786464791941757 117813457794924296978159)
                  ·
                    rfl

theorem cell20_258121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_258121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258121 prefixEnd_258121 := by exact prefixLift 258121
  have htrace : WordTrace (prefixWord ++ tailWord_258121) baseStart_258121 baseEnd_258121 := by
    simpa [prefixWord, tailWord_258121, baseEnd_258121] using wordTrace_append hprefix tailTrace_258121
  have hstable : (prefixWord ++ tailWord_258121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258121).length < 2 ^ (prefixWord ++ tailWord_258121).sum := by decide
  have hdescent : baseEnd_258121 < baseStart_258121 := by decide
  rcases family_descends (prefixWord ++ tailWord_258121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258135 : List Nat := [1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_258135 : Nat := 118140960795 + 258135 * 2 ^ 59
def prefixEnd_258135 : Nat := 4983230072969 + 3 ^ 40 * 258135 * 2
def baseEnd_258135 : Nat := 39273282592134156837145

theorem tailTrace_258135 : CollatzResearch.WordTrace tailWord_258135 prefixEnd_258135 39273282592134156837145 := by
  unfold tailWord_258135
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414956919828455793247859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6276637946552303862165239 9414956919828455793247859)
  ·
    refine ⟨14122435379742683689871789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9414956919828455793247859 14122435379742683689871789)
    ·
      refine ⟨5295913267403506383701921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14122435379742683689871789 5295913267403506383701921)
      ·
        refine ⟨3971934950552629787776441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5295913267403506383701921 3971934950552629787776441)
        ·
          refine ⟨2978951212914472340832331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3971934950552629787776441 2978951212914472340832331)
          ·
            refine ⟨4468426819371708511248497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978951212914472340832331 4468426819371708511248497)
            ·
              refine ⟨3351320114528781383436373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4468426819371708511248497 3351320114528781383436373)
              ·
                refine ⟨39273282592134156837145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3351320114528781383436373 39273282592134156837145)
                ·
                  rfl

theorem cell20_258135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_258135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258135 prefixEnd_258135 := by exact prefixLift 258135
  have htrace : WordTrace (prefixWord ++ tailWord_258135) baseStart_258135 baseEnd_258135 := by
    simpa [prefixWord, tailWord_258135, baseEnd_258135] using wordTrace_append hprefix tailTrace_258135
  have hstable : (prefixWord ++ tailWord_258135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258135).length < 2 ^ (prefixWord ++ tailWord_258135).sum := by decide
  have hdescent : baseEnd_258135 < baseStart_258135 := by decide
  rcases family_descends (prefixWord ++ tailWord_258135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258141 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 2]
def baseStart_258141 : Nat := 118140960795 + 258141 * 2 ^ 59
def prefixEnd_258141 : Nat := 4983230072969 + 3 ^ 40 * 258141 * 2
def baseEnd_258141 : Nat := 117822586339893116311411

theorem tailTrace_258141 : CollatzResearch.WordTrace tailWord_258141 prefixEnd_258141 117822586339893116311411 := by
  unfold tailWord_258141
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415175757806718817966277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6276783838537812545310851 9415175757806718817966277)
  ·
    refine ⟨1765345454588759778368677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9415175757806718817966277 1765345454588759778368677)
    ·
      refine ⟨331002272735392458444127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1765345454588759778368677 331002272735392458444127)
      ·
        refine ⟨496503409103088687666191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331002272735392458444127 496503409103088687666191)
        ·
          refine ⟨744755113654633031499287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496503409103088687666191 744755113654633031499287)
          ·
            refine ⟨1117132670481949547248931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744755113654633031499287 1117132670481949547248931)
            ·
              refine ⟨1675699005722924320873397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117132670481949547248931 1675699005722924320873397)
              ·
                refine ⟨157096781786524155081881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675699005722924320873397 157096781786524155081881)
                ·
                  refine ⟨117822586339893116311411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157096781786524155081881 117822586339893116311411)
                  ·
                    rfl

theorem cell20_258141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_258141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258141 prefixEnd_258141 := by exact prefixLift 258141
  have htrace : WordTrace (prefixWord ++ tailWord_258141) baseStart_258141 baseEnd_258141 := by
    simpa [prefixWord, tailWord_258141, baseEnd_258141] using wordTrace_append hprefix tailTrace_258141
  have hstable : (prefixWord ++ tailWord_258141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258141).length < 2 ^ (prefixWord ++ tailWord_258141).sum := by decide
  have hdescent : baseEnd_258141 < baseStart_258141 := by decide
  rcases family_descends (prefixWord ++ tailWord_258141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258159 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_258159 : Nat := 118140960795 + 258159 * 2 ^ 59
def prefixEnd_258159 : Nat := 4983230072969 + 3 ^ 40 * 258159 * 2
def baseEnd_258159 : Nat := 117830802030365053711337

theorem tailTrace_258159 : CollatzResearch.WordTrace tailWord_258159 prefixEnd_258159 117830802030365053711337 := by
  unfold tailWord_258159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415832271741507892121531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6277221514494338594747687 9415832271741507892121531)
  ·
    refine ⟨14123748407612261838182297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9415832271741507892121531 14123748407612261838182297)
    ·
      refine ⟨10592811305709196378636723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14123748407612261838182297 10592811305709196378636723)
      ·
        refine ⟨15889216958563794567955085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592811305709196378636723 15889216958563794567955085)
        ·
          refine ⟨5958456359461422962983157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15889216958563794567955085 5958456359461422962983157)
          ·
            refine ⟨558605283699508402779671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5958456359461422962983157 558605283699508402779671)
            ·
              refine ⟨837907925549262604169507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558605283699508402779671 837907925549262604169507)
              ·
                refine ⟨1256861888323893906254261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837907925549262604169507 1256861888323893906254261)
                ·
                  refine ⟨117830802030365053711337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1256861888323893906254261 117830802030365053711337)
                  ·
                    rfl

theorem cell20_258159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_258159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258159 prefixEnd_258159 := by exact prefixLift 258159
  have htrace : WordTrace (prefixWord ++ tailWord_258159) baseStart_258159 baseEnd_258159 := by
    simpa [prefixWord, tailWord_258159, baseEnd_258159] using wordTrace_append hprefix tailTrace_258159
  have hstable : (prefixWord ++ tailWord_258159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258159).length < 2 ^ (prefixWord ++ tailWord_258159).sum := by decide
  have hdescent : baseEnd_258159 < baseStart_258159 := by decide
  rcases family_descends (prefixWord ++ tailWord_258159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258162 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_258162 : Nat := 118140960795 + 258162 * 2 ^ 59
def prefixEnd_258162 : Nat := 4983230072969 + 3 ^ 40 * 258162 * 2
def baseEnd_258162 : Nat := 117832171312110376611325

theorem tailTrace_258162 : CollatzResearch.WordTrace tailWord_258162 prefixEnd_258162 117832171312110376611325 := by
  unfold tailWord_258162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353985422682659851120185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6277294460487092936320493 2353985422682659851120185)
  ·
    refine ⟨1765489067011994888340139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2353985422682659851120185 1765489067011994888340139)
    ·
      refine ⟨2648233600517992332510209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765489067011994888340139 2648233600517992332510209)
      ·
        refine ⟨1986175200388494249382657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2648233600517992332510209 1986175200388494249382657)
        ·
          refine ⟨1489631400291370687036993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1986175200388494249382657 1489631400291370687036993)
          ·
            refine ⟨1117223550218528015277745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489631400291370687036993 1117223550218528015277745)
            ·
              refine ⟨837917662663896011458309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117223550218528015277745 837917662663896011458309)
              ·
                refine ⟨157109561749480502148433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837917662663896011458309 157109561749480502148433)
                ·
                  refine ⟨117832171312110376611325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157109561749480502148433 117832171312110376611325)
                  ·
                    rfl

theorem cell20_258162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_258162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258162 prefixEnd_258162 := by exact prefixLift 258162
  have htrace : WordTrace (prefixWord ++ tailWord_258162) baseStart_258162 baseEnd_258162 := by
    simpa [prefixWord, tailWord_258162, baseEnd_258162] using wordTrace_append hprefix tailTrace_258162
  have hstable : (prefixWord ++ tailWord_258162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258162).length < 2 ^ (prefixWord ++ tailWord_258162).sum := by decide
  have hdescent : baseEnd_258162 < baseStart_258162 := by decide
  rcases family_descends (prefixWord ++ tailWord_258162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258231 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 3]
def baseStart_258231 : Nat := 118140960795 + 258231 * 2 ^ 59
def prefixEnd_258231 : Nat := 4983230072969 + 3 ^ 40 * 258231 * 2
def baseEnd_258231 : Nat := 117863664792252803311043

theorem tailTrace_258231 : CollatzResearch.WordTrace tailWord_258231 prefixEnd_258231 117863664792252803311043 := by
  unfold tailWord_258231
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418458327480664188742547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6278972218320442792495031 9418458327480664188742547)
  ·
    refine ⟨14127687491220996283113821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9418458327480664188742547 14127687491220996283113821)
    ·
      refine ⟨5297882809207873606167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14127687491220996283113821 5297882809207873606167683)
      ·
        refine ⟨7946824213811810409251525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297882809207873606167683 7946824213811810409251525)
        ·
          refine ⟨1490029540089714451734661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7946824213811810409251525 1490029540089714451734661)
          ·
            refine ⟨279380538766821459700249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1490029540089714451734661 279380538766821459700249)
            ·
              refine ⟨209535404075116094775187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279380538766821459700249 209535404075116094775187)
              ·
                refine ⟨314303106112674142162781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209535404075116094775187 314303106112674142162781)
                ·
                  refine ⟨117863664792252803311043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314303106112674142162781 117863664792252803311043)
                  ·
                    rfl

theorem cell20_258231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_258231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258231 prefixEnd_258231 := by exact prefixLift 258231
  have htrace : WordTrace (prefixWord ++ tailWord_258231) baseStart_258231 baseEnd_258231 := by
    simpa [prefixWord, tailWord_258231, baseEnd_258231] using wordTrace_append hprefix tailTrace_258231
  have hstable : (prefixWord ++ tailWord_258231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258231).length < 2 ^ (prefixWord ++ tailWord_258231).sum := by decide
  have hdescent : baseEnd_258231 < baseStart_258231 := by decide
  rcases family_descends (prefixWord ++ tailWord_258231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258235 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_258235 : Nat := 118140960795 + 258235 * 2 ^ 59
def prefixEnd_258235 : Nat := 4983230072969 + 3 ^ 40 * 258235 * 2
def baseEnd_258235 : Nat := 117865490501246567177693

theorem tailTrace_258235 : CollatzResearch.WordTrace tailWord_258235 prefixEnd_258235 117865490501246567177693 := by
  unfold tailWord_258235
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418604219466172871888159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6279069479644115247925439 9418604219466172871888159)
  ·
    refine ⟨14127906329199259307832239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9418604219466172871888159 14127906329199259307832239)
    ·
      refine ⟨21191859493798888961748359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14127906329199259307832239 21191859493798888961748359)
      ·
        refine ⟨31787789240698333442622539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21191859493798888961748359 31787789240698333442622539)
        ·
          refine ⟨47681683861047500163933809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31787789240698333442622539 47681683861047500163933809)
          ·
            refine ⟨35761262895785625122950357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47681683861047500163933809 35761262895785625122950357)
            ·
              refine ⟨838154599119975588819149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35761262895785625122950357 838154599119975588819149)
              ·
                refine ⟨314307974669990845807181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838154599119975588819149 314307974669990845807181)
                ·
                  refine ⟨117865490501246567177693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314307974669990845807181 117865490501246567177693)
                  ·
                    rfl

theorem cell20_258235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_258235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258235 prefixEnd_258235 := by exact prefixLift 258235
  have htrace : WordTrace (prefixWord ++ tailWord_258235) baseStart_258235 baseEnd_258235 := by
    simpa [prefixWord, tailWord_258235, baseEnd_258235] using wordTrace_append hprefix tailTrace_258235
  have hstable : (prefixWord ++ tailWord_258235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258235).length < 2 ^ (prefixWord ++ tailWord_258235).sum := by decide
  have hdescent : baseEnd_258235 < baseStart_258235 := by decide
  rcases family_descends (prefixWord ++ tailWord_258235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258268 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_258268 : Nat := 118140960795 + 258268 * 2 ^ 59
def prefixEnd_258268 : Nat := 4983230072969 + 3 ^ 40 * 258268 * 2
def baseEnd_258268 : Nat := 117880552600445119077559

theorem tailTrace_258268 : CollatzResearch.WordTrace tailWord_258268 prefixEnd_258268 117880552600445119077559 := by
  unfold tailWord_258268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709903914173309753919729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6279871885564413005226305 4709903914173309753919729)
  ·
    refine ⟨3532427935629982315439797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4709903914173309753919729 3532427935629982315439797)
    ·
      refine ⟨331165118965310842072481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3532427935629982315439797 331165118965310842072481)
      ·
        refine ⟨248373839223983131554361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331165118965310842072481 248373839223983131554361)
        ·
          refine ⟨186280379417987348665771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248373839223983131554361 186280379417987348665771)
          ·
            refine ⟨279420569126981022998657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186280379417987348665771 279420569126981022998657)
            ·
              refine ⟨209565426845235767248993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279420569126981022998657 209565426845235767248993)
              ·
                refine ⟨157174070133926825436745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209565426845235767248993 157174070133926825436745)
                ·
                  refine ⟨117880552600445119077559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157174070133926825436745 117880552600445119077559)
                  ·
                    rfl

theorem cell20_258268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_258268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258268 prefixEnd_258268 := by exact prefixLift 258268
  have htrace : WordTrace (prefixWord ++ tailWord_258268) baseStart_258268 baseEnd_258268 := by
    simpa [prefixWord, tailWord_258268, baseEnd_258268] using wordTrace_append hprefix tailTrace_258268
  have hstable : (prefixWord ++ tailWord_258268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258268).length < 2 ^ (prefixWord ++ tailWord_258268).sum := by decide
  have hdescent : baseEnd_258268 < baseStart_258268 := by decide
  rcases family_descends (prefixWord ++ tailWord_258268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258269 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_258269 : Nat := 118140960795 + 258269 * 2 ^ 59
def prefixEnd_258269 : Nat := 4983230072969 + 3 ^ 40 * 258269 * 2
def baseEnd_258269 : Nat := 117881009027693560044221

theorem tailTrace_258269 : CollatzResearch.WordTrace tailWord_258269 prefixEnd_258269 117881009027693560044221 := by
  unfold tailWord_258269
  simp only [CollatzResearch.WordTrace]
  refine ⟨9419844301342996678625861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6279896200895331119083907 9419844301342996678625861)
  ·
    refine ⟨1766220806501811877242349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9419844301342996678625861 1766220806501811877242349)
    ·
      refine ⟨662332802438179453965881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1766220806501811877242349 662332802438179453965881)
      ·
        refine ⟨496749601828634590474411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662332802438179453965881 496749601828634590474411)
        ·
          refine ⟨745124402742951885711617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496749601828634590474411 745124402742951885711617)
          ·
            refine ⟨558843302057213914283713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745124402742951885711617 558843302057213914283713)
            ·
              refine ⟨419132476542910435712785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558843302057213914283713 419132476542910435712785)
              ·
                refine ⟨314349357407182826784589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419132476542910435712785 314349357407182826784589)
                ·
                  refine ⟨117881009027693560044221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314349357407182826784589 117881009027693560044221)
                  ·
                    rfl

theorem cell20_258269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_258269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258269 prefixEnd_258269 := by exact prefixLift 258269
  have htrace : WordTrace (prefixWord ++ tailWord_258269) baseStart_258269 baseEnd_258269 := by
    simpa [prefixWord, tailWord_258269, baseEnd_258269] using wordTrace_append hprefix tailTrace_258269
  have hstable : (prefixWord ++ tailWord_258269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258269).length < 2 ^ (prefixWord ++ tailWord_258269).sum := by decide
  have hdescent : baseEnd_258269 < baseStart_258269 := by decide
  rcases family_descends (prefixWord ++ tailWord_258269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258290 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_258290 : Nat := 118140960795 + 258290 * 2 ^ 59
def prefixEnd_258290 : Nat := 4983230072969 + 3 ^ 40 * 258290 * 2
def baseEnd_258290 : Nat := 117890593999910820344135

theorem tailTrace_258290 : CollatzResearch.WordTrace tailWord_258290 prefixEnd_258290 117890593999910820344135 := by
  unfold tailWord_258290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355152558566729316285081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6280406822844611510093549 2355152558566729316285081)
  ·
    refine ⟨1766364418925046987213811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2355152558566729316285081 1766364418925046987213811)
    ·
      refine ⟨2649546628387570480820717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766364418925046987213811 2649546628387570480820717)
      ·
        refine ⟨993579985645338930307769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2649546628387570480820717 993579985645338930307769)
        ·
          refine ⟨745184989234004197730827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993579985645338930307769 745184989234004197730827)
          ·
            refine ⟨1117777483851006296596241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745184989234004197730827 1117777483851006296596241)
            ·
              refine ⟨838333112888254722447181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117777483851006296596241 838333112888254722447181)
              ·
                refine ⟨314374917333095520917693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838333112888254722447181 314374917333095520917693)
                ·
                  refine ⟨117890593999910820344135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314374917333095520917693 117890593999910820344135)
                  ·
                    rfl

theorem cell20_258290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_258290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258290 prefixEnd_258290 := by exact prefixLift 258290
  have htrace : WordTrace (prefixWord ++ tailWord_258290) baseStart_258290 baseEnd_258290 := by
    simpa [prefixWord, tailWord_258290, baseEnd_258290] using wordTrace_append hprefix tailTrace_258290
  have hstable : (prefixWord ++ tailWord_258290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258290).length < 2 ^ (prefixWord ++ tailWord_258290).sum := by decide
  have hdescent : baseEnd_258290 < baseStart_258290 := by decide
  rcases family_descends (prefixWord ++ tailWord_258290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258318 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_258318 : Nat := 118140960795 + 258318 * 2 ^ 59
def prefixEnd_258318 : Nat := 4983230072969 + 3 ^ 40 * 258318 * 2
def baseEnd_258318 : Nat := 117903373962867167410687

theorem tailTrace_258318 : CollatzResearch.WordTrace tailWord_258318 prefixEnd_258318 117903373962867167410687 := by
  unfold tailWord_258318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177703934770684755894951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6281087652110318698106405 1177703934770684755894951)
  ·
    refine ⟨1766555902156027133842427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177703934770684755894951 1766555902156027133842427)
    ·
      refine ⟨2649833853234040700763641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766555902156027133842427 2649833853234040700763641)
      ·
        refine ⟨1987375389925530525572731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2649833853234040700763641 1987375389925530525572731)
        ·
          refine ⟨2981063084888295788359097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987375389925530525572731 2981063084888295788359097)
          ·
            refine ⟨2235797313666221841269323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981063084888295788359097 2235797313666221841269323)
            ·
              refine ⟨3353695970499332761903985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235797313666221841269323 3353695970499332761903985)
              ·
                refine ⟨2515271977874499571427989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353695970499332761903985 2515271977874499571427989)
                ·
                  refine ⟨117903373962867167410687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2515271977874499571427989 117903373962867167410687)
                  ·
                    rfl

theorem cell20_258318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_258318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258318 prefixEnd_258318 := by exact prefixLift 258318
  have htrace : WordTrace (prefixWord ++ tailWord_258318) baseStart_258318 baseEnd_258318 := by
    simpa [prefixWord, tailWord_258318, baseEnd_258318] using wordTrace_append hprefix tailTrace_258318
  have hstable : (prefixWord ++ tailWord_258318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258318).length < 2 ^ (prefixWord ++ tailWord_258318).sum := by decide
  have hdescent : baseEnd_258318 < baseStart_258318 := by decide
  rcases family_descends (prefixWord ++ tailWord_258318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258335 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_258335 : Nat := 118140960795 + 258335 * 2 ^ 59
def prefixEnd_258335 : Nat := 4983230072969 + 3 ^ 40 * 258335 * 2
def baseEnd_258335 : Nat := 117911133226090663843951

theorem tailTrace_258335 : CollatzResearch.WordTrace tailWord_258335 prefixEnd_258335 117911133226090663843951 := by
  unfold tailWord_258335
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422251519103889950528459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6281501012735926633685639 9422251519103889950528459)
  ·
    refine ⟨14133377278655834925792689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422251519103889950528459 14133377278655834925792689)
    ·
      refine ⟨10600032958991876194344517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14133377278655834925792689 10600032958991876194344517)
      ·
        refine ⟨1987506179810976786439597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10600032958991876194344517 1987506179810976786439597)
        ·
          refine ⟨745314817429116294914849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1987506179810976786439597 745314817429116294914849)
          ·
            refine ⟨558986113071837221186137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745314817429116294914849 558986113071837221186137)
            ·
              refine ⟨419239584803877915889603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558986113071837221186137 419239584803877915889603)
              ·
                refine ⟨628859377205816873834405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419239584803877915889603 628859377205816873834405)
                ·
                  refine ⟨117911133226090663843951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628859377205816873834405 117911133226090663843951)
                  ·
                    rfl

theorem cell20_258335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_258335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258335 prefixEnd_258335 := by exact prefixLift 258335
  have htrace : WordTrace (prefixWord ++ tailWord_258335) baseStart_258335 baseEnd_258335 := by
    simpa [prefixWord, tailWord_258335, baseEnd_258335] using wordTrace_append hprefix tailTrace_258335
  have hstable : (prefixWord ++ tailWord_258335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258335).length < 2 ^ (prefixWord ++ tailWord_258335).sum := by decide
  have hdescent : baseEnd_258335 < baseStart_258335 := by decide
  rcases family_descends (prefixWord ++ tailWord_258335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258400 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_258400 : Nat := 118140960795 + 258400 * 2 ^ 59
def prefixEnd_258400 : Nat := 4983230072969 + 3 ^ 40 * 258400 * 2
def baseEnd_258400 : Nat := 117940800997239326677019

theorem tailTrace_258400 : CollatzResearch.WordTrace tailWord_258400 prefixEnd_258400 117940800997239326677019 := by
  unfold tailWord_258400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712311131934203025822327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6283081509245604034429769 4712311131934203025822327)
  ·
    refine ⟨7068466697901304538733491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4712311131934203025822327 7068466697901304538733491)
    ·
      refine ⟨10602700046851956808100237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7068466697901304538733491 10602700046851956808100237)
      ·
        refine ⟨3976012517569483803037589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10602700046851956808100237 3976012517569483803037589)
        ·
          refine ⟨186375586761069553267387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3976012517569483803037589 186375586761069553267387)
          ·
            refine ⟨279563380141604329901081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186375586761069553267387 279563380141604329901081)
            ·
              refine ⟨209672535106203247425811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279563380141604329901081 209672535106203247425811)
              ·
                refine ⟨314508802659304871138717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209672535106203247425811 314508802659304871138717)
                ·
                  refine ⟨117940800997239326677019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314508802659304871138717 117940800997239326677019)
                  ·
                    rfl

theorem cell20_258400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_258400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258400 prefixEnd_258400 := by exact prefixLift 258400
  have htrace : WordTrace (prefixWord ++ tailWord_258400) baseStart_258400 baseEnd_258400 := by
    simpa [prefixWord, tailWord_258400, baseEnd_258400] using wordTrace_append hprefix tailTrace_258400
  have hstable : (prefixWord ++ tailWord_258400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258400).length < 2 ^ (prefixWord ++ tailWord_258400).sum := by decide
  have hdescent : baseEnd_258400 < baseStart_258400 := by decide
  rcases family_descends (prefixWord ++ tailWord_258400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258452 : List Nat := [2, 4, 2, 1, 4, 1, 1, 5]
def baseStart_258452 : Nat := 118140960795 + 258452 * 2 ^ 59
def prefixEnd_258452 : Nat := 4983230072969 + 3 ^ 40 * 258452 * 2
def baseEnd_258452 : Nat := 39321511738052752314491

theorem tailTrace_258452 : CollatzResearch.WordTrace tailWord_258452 prefixEnd_258452 39321511738052752314491 := by
  unfold tailWord_258452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713259429840009466268805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6284345906453345955025073 4713259429840009466268805)
  ·
    refine ⟨883736143095001774925401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4713259429840009466268805 883736143095001774925401)
    ·
      refine ⟨662802107321251331194051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883736143095001774925401 662802107321251331194051)
      ·
        refine ⟨994203160981876996791077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662802107321251331194051 994203160981876996791077)
        ·
          refine ⟨186413092684101936898327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 994203160981876996791077 186413092684101936898327)
          ·
            refine ⟨279619639026152905347491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186413092684101936898327 279619639026152905347491)
            ·
              refine ⟨419429458539229358021237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279619639026152905347491 419429458539229358021237)
              ·
                refine ⟨39321511738052752314491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 419429458539229358021237 39321511738052752314491)
                ·
                  rfl

theorem cell20_258452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_258452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258452 prefixEnd_258452 := by exact prefixLift 258452
  have htrace : WordTrace (prefixWord ++ tailWord_258452) baseStart_258452 baseEnd_258452 := by
    simpa [prefixWord, tailWord_258452, baseEnd_258452] using wordTrace_append hprefix tailTrace_258452
  have hstable : (prefixWord ++ tailWord_258452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258452).length < 2 ^ (prefixWord ++ tailWord_258452).sum := by decide
  have hdescent : baseEnd_258452 < baseStart_258452 := by decide
  rcases family_descends (prefixWord ++ tailWord_258452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258456 : List Nat := [2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_258456 : Nat := 118140960795 + 258456 * 2 ^ 59
def prefixEnd_258456 : Nat := 4983230072969 + 3 ^ 40 * 258456 * 2
def baseEnd_258456 : Nat := 39322120307717340270041

theorem tailTrace_258456 : CollatzResearch.WordTrace tailWord_258456 prefixEnd_258456 39322120307717340270041 := by
  unfold tailWord_258456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713332375832763807841611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6284443167777018410455481 4713332375832763807841611)
  ·
    refine ⟨7069998563749145711762417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713332375832763807841611 7069998563749145711762417)
    ·
      refine ⟨5302498922811859283821813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7069998563749145711762417 5302498922811859283821813)
      ·
        refine ⟨497109274013611807858295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5302498922811859283821813 497109274013611807858295)
        ·
          refine ⟨745663911020417711787443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497109274013611807858295 745663911020417711787443)
          ·
            refine ⟨1118495866530626567681165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745663911020417711787443 1118495866530626567681165)
            ·
              refine ⟨419435949948984962880437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118495866530626567681165 419435949948984962880437)
              ·
                refine ⟨39322120307717340270041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 419435949948984962880437 39322120307717340270041)
                ·
                  rfl

theorem cell20_258456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_258456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258456 prefixEnd_258456 := by exact prefixLift 258456
  have htrace : WordTrace (prefixWord ++ tailWord_258456) baseStart_258456 baseEnd_258456 := by
    simpa [prefixWord, tailWord_258456, baseEnd_258456] using wordTrace_append hprefix tailTrace_258456
  have hstable : (prefixWord ++ tailWord_258456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258456).length < 2 ^ (prefixWord ++ tailWord_258456).sum := by decide
  have hdescent : baseEnd_258456 < baseStart_258456 := by decide
  rcases family_descends (prefixWord ++ tailWord_258456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258463 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_258463 : Nat := 118140960795 + 258463 * 2 ^ 59
def prefixEnd_258463 : Nat := 4983230072969 + 3 ^ 40 * 258463 * 2
def baseEnd_258463 : Nat := 117969555913891107576761

theorem tailTrace_258463 : CollatzResearch.WordTrace tailWord_258463 prefixEnd_258463 117969555913891107576761 := by
  unfold tailWord_258463
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426920062640167811188043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6284613375093445207458695 9426920062640167811188043)
  ·
    refine ⟨14140380093960251716782065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9426920062640167811188043 14140380093960251716782065)
    ·
      refine ⟨10605285070470188787586549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14140380093960251716782065 10605285070470188787586549)
      ·
        refine ⟨994245475356580198836239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10605285070470188787586549 994245475356580198836239)
        ·
          refine ⟨1491368213034870298254359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994245475356580198836239 1491368213034870298254359)
          ·
            refine ⟨2237052319552305447381539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491368213034870298254359 2237052319552305447381539)
            ·
              refine ⟨3355578479328458171072309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237052319552305447381539 3355578479328458171072309)
              ·
                refine ⟨314585482437042953538029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3355578479328458171072309 314585482437042953538029)
                ·
                  refine ⟨117969555913891107576761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314585482437042953538029 117969555913891107576761)
                  ·
                    rfl

theorem cell20_258463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_258463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258463 prefixEnd_258463 := by exact prefixLift 258463
  have htrace : WordTrace (prefixWord ++ tailWord_258463) baseStart_258463 baseEnd_258463 := by
    simpa [prefixWord, tailWord_258463, baseEnd_258463] using wordTrace_append hprefix tailTrace_258463
  have hstable : (prefixWord ++ tailWord_258463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258463).length < 2 ^ (prefixWord ++ tailWord_258463).sum := by decide
  have hdescent : baseEnd_258463 < baseStart_258463 := by decide
  rcases family_descends (prefixWord ++ tailWord_258463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258487 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 2]
def baseStart_258487 : Nat := 118140960795 + 258487 * 2 ^ 59
def prefixEnd_258487 : Nat := 4983230072969 + 3 ^ 40 * 258487 * 2
def baseEnd_258487 : Nat := 117980510167853690776663

theorem tailTrace_258487 : CollatzResearch.WordTrace tailWord_258487 prefixEnd_258487 117980510167853690776663 := by
  unfold tailWord_258487
  simp only [CollatzResearch.WordTrace]
  refine ⟨9427795414553219910061715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6285196943035479940041143 9427795414553219910061715)
  ·
    refine ⟨14141693121829829865092573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9427795414553219910061715 14141693121829829865092573)
    ·
      refine ⟨5303134920686186199409715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14141693121829829865092573 5303134920686186199409715)
      ·
        refine ⟨7954702381029279299114573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303134920686186199409715 7954702381029279299114573)
        ·
          refine ⟨2983013392885979737167965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7954702381029279299114573 2983013392885979737167965)
          ·
            refine ⟨1118630022332242401437987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2983013392885979737167965 1118630022332242401437987)
            ·
              refine ⟨1677945033498363602156981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118630022332242401437987 1677945033498363602156981)
              ·
                refine ⟨157307346890471587702217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677945033498363602156981 157307346890471587702217)
                ·
                  refine ⟨117980510167853690776663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157307346890471587702217 117980510167853690776663)
                  ·
                    rfl

theorem cell20_258487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2].length) (baseStart_258487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258487 prefixEnd_258487 := by exact prefixLift 258487
  have htrace : WordTrace (prefixWord ++ tailWord_258487) baseStart_258487 baseEnd_258487 := by
    simpa [prefixWord, tailWord_258487, baseEnd_258487] using wordTrace_append hprefix tailTrace_258487
  have hstable : (prefixWord ++ tailWord_258487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258487).length < 2 ^ (prefixWord ++ tailWord_258487).sum := by decide
  have hdescent : baseEnd_258487 < baseStart_258487 := by decide
  rcases family_descends (prefixWord ++ tailWord_258487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258514 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_258514 : Nat := 118140960795 + 258514 * 2 ^ 59
def prefixEnd_258514 : Nat := 4983230072969 + 3 ^ 40 * 258514 * 2
def baseEnd_258514 : Nat := 117992833703561596876553

theorem tailTrace_258514 : CollatzResearch.WordTrace tailWord_258514 prefixEnd_258514 117992833703561596876553 := by
  unfold tailWord_258514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357195046363850880323649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6285853456970269014196397 2357195046363850880323649)
  ·
    refine ⟨1767896284772888160242737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2357195046363850880323649 1767896284772888160242737)
    ·
      refine ⟨1325922213579666120182053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1767896284772888160242737 1325922213579666120182053)
      ·
        refine ⟨248610415046187397534135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1325922213579666120182053 248610415046187397534135)
        ·
          refine ⟨372915622569281096301203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248610415046187397534135 372915622569281096301203)
          ·
            refine ⟨559373433853921644451805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372915622569281096301203 559373433853921644451805)
            ·
              refine ⟨209765037695220616669427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559373433853921644451805 209765037695220616669427)
              ·
                refine ⟨314647556542830925004141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209765037695220616669427 314647556542830925004141)
                ·
                  refine ⟨117992833703561596876553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314647556542830925004141 117992833703561596876553)
                  ·
                    rfl

theorem cell20_258514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_258514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258514 prefixEnd_258514 := by exact prefixLift 258514
  have htrace : WordTrace (prefixWord ++ tailWord_258514) baseStart_258514 baseEnd_258514 := by
    simpa [prefixWord, tailWord_258514, baseEnd_258514] using wordTrace_append hprefix tailTrace_258514
  have hstable : (prefixWord ++ tailWord_258514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258514).length < 2 ^ (prefixWord ++ tailWord_258514).sum := by decide
  have hdescent : baseEnd_258514 < baseStart_258514 := by decide
  rcases family_descends (prefixWord ++ tailWord_258514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258542 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_258542 : Nat := 118140960795 + 258542 * 2 ^ 59
def prefixEnd_258542 : Nat := 4983230072969 + 3 ^ 40 * 258542 * 2
def baseEnd_258542 : Nat := 118005613666517943943105

theorem tailTrace_258542 : CollatzResearch.WordTrace tailWord_258542 prefixEnd_258542 118005613666517943943105 := by
  unfold tailWord_258542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178725178669245537914235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6286534286235976202209253 1178725178669245537914235)
  ·
    refine ⟨1768087768003868306871353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1178725178669245537914235 1768087768003868306871353)
    ·
      refine ⟨1326065826002901230153515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768087768003868306871353 1326065826002901230153515)
      ·
        refine ⟨1989098739004351845230273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326065826002901230153515 1989098739004351845230273)
        ·
          refine ⟨1491824054253263883922705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989098739004351845230273 1491824054253263883922705)
          ·
            refine ⟨1118868040689947912942029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491824054253263883922705 1118868040689947912942029)
            ·
              refine ⟨419575515258730467353261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118868040689947912942029 419575515258730467353261)
              ·
                refine ⟨157340818222023925257473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419575515258730467353261 157340818222023925257473)
                ·
                  refine ⟨118005613666517943943105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157340818222023925257473 118005613666517943943105)
                  ·
                    rfl

theorem cell20_258542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_258542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258542 prefixEnd_258542 := by exact prefixLift 258542
  have htrace : WordTrace (prefixWord ++ tailWord_258542) baseStart_258542 baseEnd_258542 := by
    simpa [prefixWord, tailWord_258542, baseEnd_258542] using wordTrace_append hprefix tailTrace_258542
  have hstable : (prefixWord ++ tailWord_258542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258542).length < 2 ^ (prefixWord ++ tailWord_258542).sum := by decide
  have hdescent : baseEnd_258542 < baseStart_258542 := by decide
  rcases family_descends (prefixWord ++ tailWord_258542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258549 : List Nat := [1, 3, 5, 1, 2, 2, 6]
def baseStart_258549 : Nat := 118140960795 + 258549 * 2 ^ 59
def prefixEnd_258549 : Nat := 4983230072969 + 3 ^ 40 * 258549 * 2
def baseEnd_258549 : Nat := 13112089850806336745527

theorem tailTrace_258549 : CollatzResearch.WordTrace tailWord_258549 prefixEnd_258549 13112089850806336745527 := by
  unfold tailWord_258549
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430056740328604498818701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6286704493552402999212467 9430056740328604498818701)
  ·
    refine ⟨3536271277623226687057013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9430056740328604498818701 3536271277623226687057013)
    ·
      refine ⟨331525432277177501911595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3536271277623226687057013 331525432277177501911595)
      ·
        refine ⟨497288148415766252867393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331525432277177501911595 497288148415766252867393)
        ·
          refine ⟨372966111311824689650545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497288148415766252867393 372966111311824689650545)
          ·
            refine ⟨279724583483868517237909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372966111311824689650545 279724583483868517237909)
            ·
              refine ⟨13112089850806336745527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279724583483868517237909 13112089850806336745527)
              ·
                rfl

theorem cell20_258549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_258549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258549 prefixEnd_258549 := by exact prefixLift 258549
  have htrace : WordTrace (prefixWord ++ tailWord_258549) baseStart_258549 baseEnd_258549 := by
    simpa [prefixWord, tailWord_258549, baseEnd_258549] using wordTrace_append hprefix tailTrace_258549
  have hstable : (prefixWord ++ tailWord_258549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258549).length < 2 ^ (prefixWord ++ tailWord_258549).sum := by decide
  have hdescent : baseEnd_258549 < baseStart_258549 := by decide
  rcases family_descends (prefixWord ++ tailWord_258549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258566 : List Nat := [6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_258566 : Nat := 118140960795 + 258566 * 2 ^ 59
def prefixEnd_258566 : Nat := 4983230072969 + 3 ^ 40 * 258566 * 2
def baseEnd_258566 : Nat := 39338855973493509047669

theorem tailTrace_258566 : CollatzResearch.WordTrace tailWord_258566 prefixEnd_258566 39338855973493509047669 := by
  unfold tailWord_258566
  simp only [CollatzResearch.WordTrace]
  refine ⟨294708649414594262568361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6287117854178010934791701 294708649414594262568361)
  ·
    refine ⟨221031487060945696926271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294708649414594262568361 221031487060945696926271)
    ·
      refine ⟨331547230591418545389407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221031487060945696926271 331547230591418545389407)
      ·
        refine ⟨497320845887127818084111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331547230591418545389407 497320845887127818084111)
        ·
          refine ⟨745981268830691727126167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497320845887127818084111 745981268830691727126167)
          ·
            refine ⟨1118971903246037590689251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745981268830691727126167 1118971903246037590689251)
            ·
              refine ⟨1678457854869056386033877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118971903246037590689251 1678457854869056386033877)
              ·
                refine ⟨39338855973493509047669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1678457854869056386033877 39338855973493509047669)
                ·
                  rfl

theorem cell20_258566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_258566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258566 prefixEnd_258566 := by exact prefixLift 258566
  have htrace : WordTrace (prefixWord ++ tailWord_258566) baseStart_258566 baseEnd_258566 := by
    simpa [prefixWord, tailWord_258566, baseEnd_258566] using wordTrace_append hprefix tailTrace_258566
  have hstable : (prefixWord ++ tailWord_258566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258566).length < 2 ^ (prefixWord ++ tailWord_258566).sum := by decide
  have hdescent : baseEnd_258566 < baseStart_258566 := by decide
  rcases family_descends (prefixWord ++ tailWord_258566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258614 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_258614 : Nat := 118140960795 + 258614 * 2 ^ 59
def prefixEnd_258614 : Nat := 4983230072969 + 3 ^ 40 * 258614 * 2
def baseEnd_258614 : Nat := 118038476428405693542811

theorem tailTrace_258614 : CollatzResearch.WordTrace tailWord_258614 prefixEnd_258614 118038476428405693542811 := by
  unfold tailWord_258614
  simp only [CollatzResearch.WordTrace]
  refine ⟨589526717818320037495931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6288284990062080399956597 589526717818320037495931)
  ·
    refine ⟨884290076727480056243897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589526717818320037495931 884290076727480056243897)
    ·
      refine ⟨663217557545610042182923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884290076727480056243897 663217557545610042182923)
      ·
        refine ⟨994826336318415063274385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663217557545610042182923 994826336318415063274385)
        ·
          refine ⟨746119752238811297455789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994826336318415063274385 746119752238811297455789)
          ·
            refine ⟨279794907089554236545921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746119752238811297455789 279794907089554236545921)
            ·
              refine ⟨209846180317165677409441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279794907089554236545921 209846180317165677409441)
              ·
                refine ⟨157384635237874258057081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209846180317165677409441 157384635237874258057081)
                ·
                  refine ⟨118038476428405693542811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157384635237874258057081 118038476428405693542811)
                  ·
                    rfl

theorem cell20_258614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_258614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258614 prefixEnd_258614 := by exact prefixLift 258614
  have htrace : WordTrace (prefixWord ++ tailWord_258614) baseStart_258614 baseEnd_258614 := by
    simpa [prefixWord, tailWord_258614, baseEnd_258614] using wordTrace_append hprefix tailTrace_258614
  have hstable : (prefixWord ++ tailWord_258614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258614).length < 2 ^ (prefixWord ++ tailWord_258614).sum := by decide
  have hdescent : baseEnd_258614 < baseStart_258614 := by decide
  rcases family_descends (prefixWord ++ tailWord_258614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258615 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_258615 : Nat := 118140960795 + 258615 * 2 ^ 59
def prefixEnd_258615 : Nat := 4983230072969 + 3 ^ 40 * 258615 * 2
def baseEnd_258615 : Nat := 118038932855654134509473

theorem tailTrace_258615 : CollatzResearch.WordTrace tailWord_258615 prefixEnd_258615 118038932855654134509473 := by
  unfold tailWord_258615
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432463958089497770721299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6288309305392998513814199 9432463958089497770721299)
  ·
    refine ⟨14148695937134246656081949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9432463958089497770721299 14148695937134246656081949)
    ·
      refine ⟨5305760976425342496030731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14148695937134246656081949 5305760976425342496030731)
      ·
        refine ⟨7958641464638013744046097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305760976425342496030731 7958641464638013744046097)
        ·
          refine ⟨5968981098478510308034573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7958641464638013744046097 5968981098478510308034573)
          ·
            refine ⟨2238367911929441365512965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5968981098478510308034573 2238367911929441365512965)
            ·
              refine ⟨419693983486770256033681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2238367911929441365512965 419693983486770256033681)
              ·
                refine ⟨314770487615077692025261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419693983486770256033681 314770487615077692025261)
                ·
                  refine ⟨118038932855654134509473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314770487615077692025261 118038932855654134509473)
                  ·
                    rfl

theorem cell20_258615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_258615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258615 prefixEnd_258615 := by exact prefixLift 258615
  have htrace : WordTrace (prefixWord ++ tailWord_258615) baseStart_258615 baseEnd_258615 := by
    simpa [prefixWord, tailWord_258615, baseEnd_258615] using wordTrace_append hprefix tailTrace_258615
  have hstable : (prefixWord ++ tailWord_258615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258615).length < 2 ^ (prefixWord ++ tailWord_258615).sum := by decide
  have hdescent : baseEnd_258615 < baseStart_258615 := by decide
  rcases family_descends (prefixWord ++ tailWord_258615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258618 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_258618 : Nat := 118140960795 + 258618 * 2 ^ 59
def prefixEnd_258618 : Nat := 4983230072969 + 3 ^ 40 * 258618 * 2
def baseEnd_258618 : Nat := 118040302137399457409461

theorem tailTrace_258618 : CollatzResearch.WordTrace tailWord_258618 prefixEnd_258618 118040302137399457409461 := by
  unfold tailWord_258618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358143344269657320770127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6288382251385752855387005 2358143344269657320770127)
  ·
    refine ⟨3537215016404485981155191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2358143344269657320770127 3537215016404485981155191)
    ·
      refine ⟨5305822524606728971732787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3537215016404485981155191 5305822524606728971732787)
      ·
        refine ⟨7958733786910093457599181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305822524606728971732787 7958733786910093457599181)
        ·
          refine ⟨2984525170091285046599693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7958733786910093457599181 2984525170091285046599693)
          ·
            refine ⟨1119196938784231892474885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2984525170091285046599693 1119196938784231892474885)
            ·
              refine ⟨209849426022043479839041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1119196938784231892474885 209849426022043479839041)
              ·
                refine ⟨157387069516532609879281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209849426022043479839041 157387069516532609879281)
                ·
                  refine ⟨118040302137399457409461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157387069516532609879281 118040302137399457409461)
                  ·
                    rfl

theorem cell20_258618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_258618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258618 prefixEnd_258618 := by exact prefixLift 258618
  have htrace : WordTrace (prefixWord ++ tailWord_258618) baseStart_258618 baseEnd_258618 := by
    simpa [prefixWord, tailWord_258618, baseEnd_258618] using wordTrace_append hprefix tailTrace_258618
  have hstable : (prefixWord ++ tailWord_258618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258618).length < 2 ^ (prefixWord ++ tailWord_258618).sum := by decide
  have hdescent : baseEnd_258618 < baseStart_258618 := by decide
  rcases family_descends (prefixWord ++ tailWord_258618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258629 : List Nat := [1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_258629 : Nat := 118140960795 + 258629 * 2 ^ 59
def prefixEnd_258629 : Nat := 4983230072969 + 3 ^ 40 * 258629 * 2
def baseEnd_258629 : Nat := 39348440945710769347583

theorem tailTrace_258629 : CollatzResearch.WordTrace tailWord_258629 prefixEnd_258629 39348440945710769347583 := by
  unfold tailWord_258629
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432974580038778161730941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6288649720025852107820627 9432974580038778161730941)
  ·
    refine ⟨3537365467514541810649103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9432974580038778161730941 3537365467514541810649103)
    ·
      refine ⟨5306048201271812715973655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3537365467514541810649103 5306048201271812715973655)
      ·
        refine ⟨7959072301907719073960483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306048201271812715973655 7959072301907719073960483)
        ·
          refine ⟨11938608452861578610940725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959072301907719073960483 11938608452861578610940725)
          ·
            refine ⟨1119244542455772994775693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11938608452861578610940725 1119244542455772994775693)
            ·
              refine ⟨419716703420914873040885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119244542455772994775693 419716703420914873040885)
              ·
                refine ⟨39348440945710769347583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 419716703420914873040885 39348440945710769347583)
                ·
                  rfl

theorem cell20_258629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_258629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258629 prefixEnd_258629 := by exact prefixLift 258629
  have htrace : WordTrace (prefixWord ++ tailWord_258629) baseStart_258629 baseEnd_258629 := by
    simpa [prefixWord, tailWord_258629, baseEnd_258629] using wordTrace_append hprefix tailTrace_258629
  have hstable : (prefixWord ++ tailWord_258629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258629).length < 2 ^ (prefixWord ++ tailWord_258629).sum := by decide
  have hdescent : baseEnd_258629 < baseStart_258629 := by decide
  rcases family_descends (prefixWord ++ tailWord_258629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258670 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_258670 : Nat := 118140960795 + 258670 * 2 ^ 59
def prefixEnd_258670 : Nat := 4983230072969 + 3 ^ 40 * 258670 * 2
def baseEnd_258670 : Nat := 118064036354318387675915

theorem tailTrace_258670 : CollatzResearch.WordTrace tailWord_258670 prefixEnd_258670 118064036354318387675915 := by
  unfold tailWord_258670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179308746611280270496683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6289646648593494775982309 1179308746611280270496683)
  ·
    refine ⟨1768963119916920405745025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179308746611280270496683 1768963119916920405745025)
    ·
      refine ⟨1326722339937690304308769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768963119916920405745025 1326722339937690304308769)
      ·
        refine ⟨995041754953267728231577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1326722339937690304308769 995041754953267728231577)
        ·
          refine ⟨746281316214950796173683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995041754953267728231577 746281316214950796173683)
          ·
            refine ⟨1119421974322426194260525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746281316214950796173683 1119421974322426194260525)
            ·
              refine ⟨419783240370909822847697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119421974322426194260525 419783240370909822847697)
              ·
                refine ⟨314837430278182367135773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419783240370909822847697 314837430278182367135773)
                ·
                  refine ⟨118064036354318387675915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314837430278182367135773 118064036354318387675915)
                  ·
                    rfl

theorem cell20_258670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_258670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258670 prefixEnd_258670 := by exact prefixLift 258670
  have htrace : WordTrace (prefixWord ++ tailWord_258670) baseStart_258670 baseEnd_258670 := by
    simpa [prefixWord, tailWord_258670, baseEnd_258670] using wordTrace_append hprefix tailTrace_258670
  have hstable : (prefixWord ++ tailWord_258670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258670).length < 2 ^ (prefixWord ++ tailWord_258670).sum := by decide
  have hdescent : baseEnd_258670 < baseStart_258670 := by decide
  rcases family_descends (prefixWord ++ tailWord_258670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258712 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_258712 : Nat := 118140960795 + 258712 * 2 ^ 59
def prefixEnd_258712 : Nat := 4983230072969 + 3 ^ 40 * 258712 * 2
def baseEnd_258712 : Nat := 118083206298752908275743

theorem tailTrace_258712 : CollatzResearch.WordTrace tailWord_258712 prefixEnd_258712 118083206298752908275743 := by
  unfold tailWord_258712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718000919369041668501195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6290667892492055558001593 4718000919369041668501195)
  ·
    refine ⟨7077001379053562502751793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718000919369041668501195 7077001379053562502751793)
    ·
      refine ⟨5307751034290171877063845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7077001379053562502751793 5307751034290171877063845)
      ·
        refine ⟨995203318929407226949471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5307751034290171877063845 995203318929407226949471)
        ·
          refine ⟨1492804978394110840424207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995203318929407226949471 1492804978394110840424207)
          ·
            refine ⟨2239207467591166260636311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492804978394110840424207 2239207467591166260636311)
            ·
              refine ⟨3358811201386749390954467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239207467591166260636311 3358811201386749390954467)
              ·
                refine ⟨5038216802080124086431701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358811201386749390954467 5038216802080124086431701)
                ·
                  refine ⟨118083206298752908275743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5038216802080124086431701 118083206298752908275743)
                  ·
                    rfl

theorem cell20_258712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_258712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258712 prefixEnd_258712 := by exact prefixLift 258712
  have htrace : WordTrace (prefixWord ++ tailWord_258712) baseStart_258712 baseEnd_258712 := by
    simpa [prefixWord, tailWord_258712, baseEnd_258712] using wordTrace_append hprefix tailTrace_258712
  have hstable : (prefixWord ++ tailWord_258712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258712).length < 2 ^ (prefixWord ++ tailWord_258712).sum := by decide
  have hdescent : baseEnd_258712 < baseStart_258712 := by decide
  rcases family_descends (prefixWord ++ tailWord_258712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258787 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 2]
def baseStart_258787 : Nat := 118140960795 + 258787 * 2 ^ 59
def prefixEnd_258787 : Nat := 4983230072969 + 3 ^ 40 * 258787 * 2
def baseEnd_258787 : Nat := 118117438342385980775437

theorem tailTrace_258787 : CollatzResearch.WordTrace tailWord_258787 prefixEnd_258787 118117438342385980775437 := by
  unfold tailWord_258787
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438737313466371145982615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6292491542310914097321743 9438737313466371145982615)
  ·
    refine ⟨14158105970199556718973923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9438737313466371145982615 14158105970199556718973923)
    ·
      refine ⟨21237158955299335078460885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14158105970199556718973923 21237158955299335078460885)
      ·
        refine ⟨497745913014828165901427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21237158955299335078460885 497745913014828165901427)
        ·
          refine ⟨746618869522242248852141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497745913014828165901427 746618869522242248852141)
          ·
            refine ⟨279982076070840843319553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746618869522242248852141 279982076070840843319553)
            ·
              refine ⟨209986557053130632489665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279982076070840843319553 209986557053130632489665)
              ·
                refine ⟨157489917789847974367249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209986557053130632489665 157489917789847974367249)
                ·
                  refine ⟨118117438342385980775437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157489917789847974367249 118117438342385980775437)
                  ·
                    rfl

theorem cell20_258787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2].length) (baseStart_258787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258787 prefixEnd_258787 := by exact prefixLift 258787
  have htrace : WordTrace (prefixWord ++ tailWord_258787) baseStart_258787 baseEnd_258787 := by
    simpa [prefixWord, tailWord_258787, baseEnd_258787] using wordTrace_append hprefix tailTrace_258787
  have hstable : (prefixWord ++ tailWord_258787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258787).length < 2 ^ (prefixWord ++ tailWord_258787).sum := by decide
  have hdescent : baseEnd_258787 < baseStart_258787 := by decide
  rcases family_descends (prefixWord ++ tailWord_258787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258795 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_258795 : Nat := 118140960795 + 258795 * 2 ^ 59
def prefixEnd_258795 : Nat := 4983230072969 + 3 ^ 40 * 258795 * 2
def baseEnd_258795 : Nat := 118121089760373508508737

theorem tailTrace_258795 : CollatzResearch.WordTrace tailWord_258795 prefixEnd_258795 118121089760373508508737 := by
  unfold tailWord_258795
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439029097437388512273839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6292686064958259008182559 9439029097437388512273839)
  ·
    refine ⟨14158543646156082768410759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9439029097437388512273839 14158543646156082768410759)
    ·
      refine ⟨21237815469234124152616139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14158543646156082768410759 21237815469234124152616139)
      ·
        refine ⟨31856723203851186228924209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21237815469234124152616139 31856723203851186228924209)
        ·
          refine ⟨23892542402888389671693157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31856723203851186228924209 23892542402888389671693157)
          ·
            refine ⟨4479851700541573063442467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23892542402888389671693157 4479851700541573063442467)
            ·
              refine ⟨6719777550812359595163701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479851700541573063442467 6719777550812359595163701)
              ·
                refine ⟨629979145388658712046597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6719777550812359595163701 629979145388658712046597)
                ·
                  refine ⟨118121089760373508508737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629979145388658712046597 118121089760373508508737)
                  ·
                    rfl

theorem cell20_258795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_258795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258795 prefixEnd_258795 := by exact prefixLift 258795
  have htrace : WordTrace (prefixWord ++ tailWord_258795) baseStart_258795 baseEnd_258795 := by
    simpa [prefixWord, tailWord_258795, baseEnd_258795] using wordTrace_append hprefix tailTrace_258795
  have hstable : (prefixWord ++ tailWord_258795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258795).length < 2 ^ (prefixWord ++ tailWord_258795).sum := by decide
  have hdescent : baseEnd_258795 < baseStart_258795 := by decide
  rcases family_descends (prefixWord ++ tailWord_258795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258798 : List Nat := [4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_258798 : Nat := 118140960795 + 258798 * 2 ^ 59
def prefixEnd_258798 : Nat := 4983230072969 + 3 ^ 40 * 258798 * 2
def baseEnd_258798 : Nat := 39374153014039610469575

theorem tailTrace_258798 : CollatzResearch.WordTrace tailWord_258798 prefixEnd_258798 39374153014039610469575 := by
  unfold tailWord_258798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179892314553315003079131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6292759010951013349755365 1179892314553315003079131)
  ·
    refine ⟨1769838471829972504618697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179892314553315003079131 1769838471829972504618697)
    ·
      refine ⟨1327378853872479378464023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1769838471829972504618697 1327378853872479378464023)
      ·
        refine ⟨1991068280808719067696035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327378853872479378464023 1991068280808719067696035)
        ·
          refine ⟨2986602421213078601544053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991068280808719067696035 2986602421213078601544053)
          ·
            refine ⟨279993976988726118894755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2986602421213078601544053 279993976988726118894755)
            ·
              refine ⟨419990965483089178342133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279993976988726118894755 419990965483089178342133)
              ·
                refine ⟨39374153014039610469575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 419990965483089178342133 39374153014039610469575)
                ·
                  rfl

theorem cell20_258798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_258798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258798 prefixEnd_258798 := by exact prefixLift 258798
  have htrace : WordTrace (prefixWord ++ tailWord_258798) baseStart_258798 baseEnd_258798 := by
    simpa [prefixWord, tailWord_258798, baseEnd_258798] using wordTrace_append hprefix tailTrace_258798
  have hstable : (prefixWord ++ tailWord_258798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258798).length < 2 ^ (prefixWord ++ tailWord_258798).sum := by decide
  have hdescent : baseEnd_258798 < baseStart_258798 := by decide
  rcases family_descends (prefixWord ++ tailWord_258798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258812 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_258812 : Nat := 118140960795 + 258812 * 2 ^ 59
def prefixEnd_258812 : Nat := 4983230072969 + 3 ^ 40 * 258812 * 2
def baseEnd_258812 : Nat := 118128849023597004942001

theorem tailTrace_258812 : CollatzResearch.WordTrace tailWord_258812 prefixEnd_258812 118128849023597004942001 := by
  unfold tailWord_258812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719824569187900207821345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6293099425583866943761793 4719824569187900207821345)
  ·
    refine ⟨3539868426890925155866009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4719824569187900207821345 3539868426890925155866009)
    ·
      refine ⟨2654901320168193866899507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3539868426890925155866009 2654901320168193866899507)
      ·
        refine ⟨3982351980252290800349261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654901320168193866899507 3982351980252290800349261)
        ·
          refine ⟨1493381992594609050130973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3982351980252290800349261 1493381992594609050130973)
          ·
            refine ⟨560018247222978393799115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1493381992594609050130973 560018247222978393799115)
            ·
              refine ⟨840027370834467590698673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560018247222978393799115 840027370834467590698673)
              ·
                refine ⟨630020528125850693024005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840027370834467590698673 630020528125850693024005)
                ·
                  refine ⟨118128849023597004942001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630020528125850693024005 118128849023597004942001)
                  ·
                    rfl

theorem cell20_258812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_258812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258812 prefixEnd_258812 := by exact prefixLift 258812
  have htrace : WordTrace (prefixWord ++ tailWord_258812) baseStart_258812 baseEnd_258812 := by
    simpa [prefixWord, tailWord_258812, baseEnd_258812] using wordTrace_append hprefix tailTrace_258812
  have hstable : (prefixWord ++ tailWord_258812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258812).length < 2 ^ (prefixWord ++ tailWord_258812).sum := by decide
  have hdescent : baseEnd_258812 < baseStart_258812 := by decide
  rcases family_descends (prefixWord ++ tailWord_258812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258826 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_258826 : Nat := 118140960795 + 258826 * 2 ^ 59
def prefixEnd_258826 : Nat := 4983230072969 + 3 ^ 40 * 258826 * 2
def baseEnd_258826 : Nat := 118135239005075178475277

theorem tailTrace_258826 : CollatzResearch.WordTrace tailWord_258826 prefixEnd_258826 118135239005075178475277 := by
  unfold tailWord_258826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360039940081270201663083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6293439840216720537768221 2360039940081270201663083)
  ·
    refine ⟨3540059910121905302494625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2360039940081270201663083 3540059910121905302494625)
    ·
      refine ⟨2655044932591428976870969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3540059910121905302494625 2655044932591428976870969)
      ·
        refine ⟨1991283699443571732653227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655044932591428976870969 1991283699443571732653227)
        ·
          refine ⟨2986925549165357598979841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991283699443571732653227 2986925549165357598979841)
          ·
            refine ⟨2240194161874018199234881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986925549165357598979841 2240194161874018199234881)
            ·
              refine ⟨1680145621405513649426161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240194161874018199234881 1680145621405513649426161)
              ·
                refine ⟨1260109216054135237069621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680145621405513649426161 1260109216054135237069621)
                ·
                  refine ⟨118135239005075178475277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1260109216054135237069621 118135239005075178475277)
                  ·
                    rfl

theorem cell20_258826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_258826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258826 prefixEnd_258826 := by exact prefixLift 258826
  have htrace : WordTrace (prefixWord ++ tailWord_258826) baseStart_258826 baseEnd_258826 := by
    simpa [prefixWord, tailWord_258826, baseEnd_258826] using wordTrace_append hprefix tailTrace_258826
  have hstable : (prefixWord ++ tailWord_258826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258826).length < 2 ^ (prefixWord ++ tailWord_258826).sum := by decide
  have hdescent : baseEnd_258826 < baseStart_258826 := by decide
  rcases family_descends (prefixWord ++ tailWord_258826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258839 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 3]
def baseStart_258839 : Nat := 118140960795 + 258839 * 2 ^ 59
def prefixEnd_258839 : Nat := 4983230072969 + 3 ^ 40 * 258839 * 2
def baseEnd_258839 : Nat := 118141172559304911041891

theorem tailTrace_258839 : CollatzResearch.WordTrace tailWord_258839 prefixEnd_258839 118141172559304911041891 := by
  unfold tailWord_258839
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440633909277984026875571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6293755939518656017917047 9440633909277984026875571)
  ·
    refine ⟨14160950863916976040313357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9440633909277984026875571 14160950863916976040313357)
    ·
      refine ⟨5310356573968866015117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14160950863916976040313357 5310356573968866015117509)
      ·
        refine ⟨995691857619162377834533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5310356573968866015117509 995691857619162377834533)
        ·
          refine ⟨186692223303592945843975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 995691857619162377834533 186692223303592945843975)
          ·
            refine ⟨280038334955389418765963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186692223303592945843975 280038334955389418765963)
            ·
              refine ⟨420057502433084128148945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280038334955389418765963 420057502433084128148945)
              ·
                refine ⟨315043126824813096111709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420057502433084128148945 315043126824813096111709)
                ·
                  refine ⟨118141172559304911041891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315043126824813096111709 118141172559304911041891)
                  ·
                    rfl

theorem cell20_258839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3].length) (baseStart_258839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258839 prefixEnd_258839 := by exact prefixLift 258839
  have htrace : WordTrace (prefixWord ++ tailWord_258839) baseStart_258839 baseEnd_258839 := by
    simpa [prefixWord, tailWord_258839, baseEnd_258839] using wordTrace_append hprefix tailTrace_258839
  have hstable : (prefixWord ++ tailWord_258839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258839).length < 2 ^ (prefixWord ++ tailWord_258839).sum := by decide
  have hdescent : baseEnd_258839 < baseStart_258839 := by decide
  rcases family_descends (prefixWord ++ tailWord_258839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258850 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_258850 : Nat := 118140960795 + 258850 * 2 ^ 59
def prefixEnd_258850 : Nat := 4983230072969 + 3 ^ 40 * 258850 * 2
def baseEnd_258850 : Nat := 118146193259037761675179

theorem tailTrace_258850 : CollatzResearch.WordTrace tailWord_258850 prefixEnd_258850 118146193259037761675179 := by
  unfold tailWord_258850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360258778059533226381501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6294023408158755270350669 2360258778059533226381501)
  ·
    refine ⟨885097041772324959893063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2360258778059533226381501 885097041772324959893063)
    ·
      refine ⟨1327645562658487439839595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885097041772324959893063 1327645562658487439839595)
      ·
        refine ⟨1991468343987731159759393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327645562658487439839595 1991468343987731159759393)
        ·
          refine ⟨1493601257990798369819545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991468343987731159759393 1493601257990798369819545)
          ·
            refine ⟨1120200943493098777364659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493601257990798369819545 1120200943493098777364659)
            ·
              refine ⟨1680301415239648166046989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120200943493098777364659 1680301415239648166046989)
              ·
                refine ⟨630113030714868062267621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680301415239648166046989 630113030714868062267621)
                ·
                  refine ⟨118146193259037761675179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630113030714868062267621 118146193259037761675179)
                  ·
                    rfl

theorem cell20_258850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_258850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258850 prefixEnd_258850 := by exact prefixLift 258850
  have htrace : WordTrace (prefixWord ++ tailWord_258850) baseStart_258850 baseEnd_258850 := by
    simpa [prefixWord, tailWord_258850, baseEnd_258850] using wordTrace_append hprefix tailTrace_258850
  have hstable : (prefixWord ++ tailWord_258850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258850).length < 2 ^ (prefixWord ++ tailWord_258850).sum := by decide
  have hdescent : baseEnd_258850 < baseStart_258850 := by decide
  rcases family_descends (prefixWord ++ tailWord_258850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258864 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_258864 : Nat := 118140960795 + 258864 * 2 ^ 59
def prefixEnd_258864 : Nat := 4983230072969 + 3 ^ 40 * 258864 * 2
def baseEnd_258864 : Nat := 118152583240515935208455

theorem tailTrace_258864 : CollatzResearch.WordTrace tailWord_258864 prefixEnd_258864 118152583240515935208455 := by
  unfold tailWord_258864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720772867093706648267823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6294363822791608864357097 4720772867093706648267823)
  ·
    refine ⟨7081159300640559972401735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720772867093706648267823 7081159300640559972401735)
    ·
      refine ⟨10621738950960839958602603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081159300640559972401735 10621738950960839958602603)
      ·
        refine ⟨15932608426441259937903905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621738950960839958602603 15932608426441259937903905)
        ·
          refine ⟨11949456319830944953427929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15932608426441259937903905 11949456319830944953427929)
          ·
            refine ⟨8962092239873208715070947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11949456319830944953427929 8962092239873208715070947)
            ·
              refine ⟨13443138359809813072606421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962092239873208715070947 13443138359809813072606421)
              ·
                refine ⟨315073555308042493889213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13443138359809813072606421 315073555308042493889213)
                ·
                  refine ⟨118152583240515935208455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315073555308042493889213 118152583240515935208455)
                  ·
                    rfl

theorem cell20_258864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_258864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258864 prefixEnd_258864 := by exact prefixLift 258864
  have htrace : WordTrace (prefixWord ++ tailWord_258864) baseStart_258864 baseEnd_258864 := by
    simpa [prefixWord, tailWord_258864, baseEnd_258864] using wordTrace_append hprefix tailTrace_258864
  have hstable : (prefixWord ++ tailWord_258864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258864).length < 2 ^ (prefixWord ++ tailWord_258864).sum := by decide
  have hdescent : baseEnd_258864 < baseStart_258864 := by decide
  rcases family_descends (prefixWord ++ tailWord_258864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258870 : List Nat := [5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_258870 : Nat := 118140960795 + 258870 * 2 ^ 59
def prefixEnd_258870 : Nat := 4983230072969 + 3 ^ 40 * 258870 * 2
def baseEnd_258870 : Nat := 39385107268002193669477

theorem tailTrace_258870 : CollatzResearch.WordTrace tailWord_258870 prefixEnd_258870 39385107268002193669477 := by
  unfold tailWord_258870
  simp only [CollatzResearch.WordTrace]
  refine ⟨590110285760354770078379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6294509714777117547502709 590110285760354770078379)
  ·
    refine ⟨885165428640532155117569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590110285760354770078379 885165428640532155117569)
    ·
      refine ⟨663874071480399116338177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 885165428640532155117569 663874071480399116338177)
      ·
        refine ⟨497905553610299337253633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663874071480399116338177 497905553610299337253633)
        ·
          refine ⟨373429165207724502940225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497905553610299337253633 373429165207724502940225)
          ·
            refine ⟨280071873905793377205169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373429165207724502940225 280071873905793377205169)
            ·
              refine ⟨210053905429345032903877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280071873905793377205169 210053905429345032903877)
              ·
                refine ⟨39385107268002193669477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210053905429345032903877 39385107268002193669477)
                ·
                  rfl

theorem cell20_258870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_258870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258870 prefixEnd_258870 := by exact prefixLift 258870
  have htrace : WordTrace (prefixWord ++ tailWord_258870) baseStart_258870 baseEnd_258870 := by
    simpa [prefixWord, tailWord_258870, baseEnd_258870] using wordTrace_append hprefix tailTrace_258870
  have hstable : (prefixWord ++ tailWord_258870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258870).length < 2 ^ (prefixWord ++ tailWord_258870).sum := by decide
  have hdescent : baseEnd_258870 < baseStart_258870 := by decide
  rcases family_descends (prefixWord ++ tailWord_258870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258871 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_258871 : Nat := 118140960795 + 258871 * 2 ^ 59
def prefixEnd_258871 : Nat := 4983230072969 + 3 ^ 40 * 258871 * 2
def baseEnd_258871 : Nat := 118155778231255021975093

theorem tailTrace_258871 : CollatzResearch.WordTrace tailWord_258871 prefixEnd_258871 118155778231255021975093 := by
  unfold tailWord_258871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441801045162053492040467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6294534030108035661360311 9441801045162053492040467)
  ·
    refine ⟨14162701567743080238060701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441801045162053492040467 14162701567743080238060701)
    ·
      refine ⟨5311013087903655089272763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14162701567743080238060701 5311013087903655089272763)
      ·
        refine ⟨7966519631855482633909145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311013087903655089272763 7966519631855482633909145)
        ·
          refine ⟨5974889723891611975431859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7966519631855482633909145 5974889723891611975431859)
          ·
            refine ⟨8962334585837417963147789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974889723891611975431859 8962334585837417963147789)
            ·
              refine ⟨3360875469689031736180421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8962334585837417963147789 3360875469689031736180421)
              ·
                refine ⟨630164150566693450533829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3360875469689031736180421 630164150566693450533829)
                ·
                  refine ⟨118155778231255021975093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630164150566693450533829 118155778231255021975093)
                  ·
                    rfl

theorem cell20_258871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_258871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258871 prefixEnd_258871 := by exact prefixLift 258871
  have htrace : WordTrace (prefixWord ++ tailWord_258871) baseStart_258871 baseEnd_258871 := by
    simpa [prefixWord, tailWord_258871, baseEnd_258871] using wordTrace_append hprefix tailTrace_258871
  have hstable : (prefixWord ++ tailWord_258871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258871).length < 2 ^ (prefixWord ++ tailWord_258871).sum := by decide
  have hdescent : baseEnd_258871 < baseStart_258871 := by decide
  rcases family_descends (prefixWord ++ tailWord_258871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258919 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_258919 : Nat := 118140960795 + 258919 * 2 ^ 59
def prefixEnd_258919 : Nat := 4983230072969 + 3 ^ 40 * 258919 * 2
def baseEnd_258919 : Nat := 118177686739180188374897

theorem tailTrace_258919 : CollatzResearch.WordTrace tailWord_258919 prefixEnd_258919 118177686739180188374897 := by
  unfold tailWord_258919
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443551748988157689787811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6295701165992105126525207 9443551748988157689787811)
  ·
    refine ⟨14165327623482236534681717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9443551748988157689787811 14165327623482236534681717)
    ·
      refine ⟨1327999464701459675126411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14165327623482236534681717 1327999464701459675126411)
      ·
        refine ⟨1991999197052189512689617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327999464701459675126411 1991999197052189512689617)
        ·
          refine ⟨1493999397789142134517213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991999197052189512689617 1493999397789142134517213)
          ·
            refine ⟨560249774170928300443955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1493999397789142134517213 560249774170928300443955)
            ·
              refine ⟨840374661256392450665933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560249774170928300443955 840374661256392450665933)
              ·
                refine ⟨315140497971147168999725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840374661256392450665933 315140497971147168999725)
                ·
                  refine ⟨118177686739180188374897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315140497971147168999725 118177686739180188374897)
                  ·
                    rfl

theorem cell20_258919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_258919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258919 prefixEnd_258919 := by exact prefixLift 258919
  have htrace : WordTrace (prefixWord ++ tailWord_258919) baseStart_258919 baseEnd_258919 := by
    simpa [prefixWord, tailWord_258919, baseEnd_258919] using wordTrace_append hprefix tailTrace_258919
  have hstable : (prefixWord ++ tailWord_258919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258919).length < 2 ^ (prefixWord ++ tailWord_258919).sum := by decide
  have hdescent : baseEnd_258919 < baseStart_258919 := by decide
  rcases family_descends (prefixWord ++ tailWord_258919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258933 : List Nat := [1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_258933 : Nat := 118140960795 + 258933 * 2 ^ 59
def prefixEnd_258933 : Nat := 4983230072969 + 3 ^ 40 * 258933 * 2
def baseEnd_258933 : Nat := 39394692240219453969391

theorem tailTrace_258933 : CollatzResearch.WordTrace tailWord_258933 prefixEnd_258933 39394692240219453969391 := by
  unfold tailWord_258933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444062370937438080797453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6296041580624958720531635 9444062370937438080797453)
  ·
    refine ⟨3541523389101539280299045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9444062370937438080797453 3541523389101539280299045)
    ·
      refine ⟨664035635456538615056071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3541523389101539280299045 664035635456538615056071)
      ·
        refine ⟨996053453184807922584107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664035635456538615056071 996053453184807922584107)
        ·
          refine ⟨1494080179777211883876161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996053453184807922584107 1494080179777211883876161)
          ·
            refine ⟨1120560134832908912907121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494080179777211883876161 1120560134832908912907121)
            ·
              refine ⟨840420101124681684680341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120560134832908912907121 840420101124681684680341)
              ·
                refine ⟨39394692240219453969391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 840420101124681684680341 39394692240219453969391)
                ·
                  rfl

theorem cell20_258933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_258933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258933 prefixEnd_258933 := by exact prefixLift 258933
  have htrace : WordTrace (prefixWord ++ tailWord_258933) baseStart_258933 baseEnd_258933 := by
    simpa [prefixWord, tailWord_258933, baseEnd_258933] using wordTrace_append hprefix tailTrace_258933
  have hstable : (prefixWord ++ tailWord_258933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258933).length < 2 ^ (prefixWord ++ tailWord_258933).sum := by decide
  have hdescent : baseEnd_258933 < baseStart_258933 := by decide
  rcases family_descends (prefixWord ++ tailWord_258933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258964 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_258964 : Nat := 118140960795 + 258964 * 2 ^ 59
def prefixEnd_258964 : Nat := 4983230072969 + 3 ^ 40 * 258964 * 2
def baseEnd_258964 : Nat := 118198225965360031874713

theorem tailTrace_258964 : CollatzResearch.WordTrace tailWord_258964 prefixEnd_258964 118198225965360031874713 := by
  unfold tailWord_258964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4722596516912565187587973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6296795355883420250117297 4722596516912565187587973)
  ·
    refine ⟨885486846921105972672745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4722596516912565187587973 885486846921105972672745)
    ·
      refine ⟨664115135190829479504559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 885486846921105972672745 664115135190829479504559)
      ·
        refine ⟨996172702786244219256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664115135190829479504559 996172702786244219256839)
        ·
          refine ⟨1494259054179366328885259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996172702786244219256839 1494259054179366328885259)
          ·
            refine ⟨2241388581269049493327889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494259054179366328885259 2241388581269049493327889)
            ·
              refine ⟨1681041435951787119995917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241388581269049493327889 1681041435951787119995917)
              ·
                refine ⟨630390538481920169998469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681041435951787119995917 630390538481920169998469)
                ·
                  refine ⟨118198225965360031874713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630390538481920169998469 118198225965360031874713)
                  ·
                    rfl

theorem cell20_258964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_258964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258964 prefixEnd_258964 := by exact prefixLift 258964
  have htrace : WordTrace (prefixWord ++ tailWord_258964) baseStart_258964 baseEnd_258964 := by
    simpa [prefixWord, tailWord_258964, baseEnd_258964] using wordTrace_append hprefix tailTrace_258964
  have hstable : (prefixWord ++ tailWord_258964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258964).length < 2 ^ (prefixWord ++ tailWord_258964).sum := by decide
  have hdescent : baseEnd_258964 < baseStart_258964 := by decide
  rcases family_descends (prefixWord ++ tailWord_258964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258985 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_258985 : Nat := 118140960795 + 258985 * 2 ^ 59
def prefixEnd_258985 : Nat := 4983230072969 + 3 ^ 40 * 258985 * 2
def baseEnd_258985 : Nat := 118207810937577292174627

theorem tailTrace_258985 : CollatzResearch.WordTrace tailWord_258985 prefixEnd_258985 118207810937577292174627 := by
  unfold tailWord_258985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445958966749050961690409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6297305977832700641126939 9445958966749050961690409)
  ·
    refine ⟨7084469225061788221267807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9445958966749050961690409 7084469225061788221267807)
    ·
      refine ⟨10626703837592682331901711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7084469225061788221267807 10626703837592682331901711)
      ·
        refine ⟨15940055756389023497852567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626703837592682331901711 15940055756389023497852567)
        ·
          refine ⟨23910083634583535246778851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15940055756389023497852567 23910083634583535246778851)
          ·
            refine ⟨35865125451875302870168277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23910083634583535246778851 35865125451875302870168277)
            ·
              refine ⟨840588877778327411019569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35865125451875302870168277 840588877778327411019569)
              ·
                refine ⟨630441658333745558264677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840588877778327411019569 630441658333745558264677)
                ·
                  refine ⟨118207810937577292174627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630441658333745558264677 118207810937577292174627)
                  ·
                    rfl

theorem cell20_258985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_258985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_258985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_258985 prefixEnd_258985 := by exact prefixLift 258985
  have htrace : WordTrace (prefixWord ++ tailWord_258985) baseStart_258985 baseEnd_258985 := by
    simpa [prefixWord, tailWord_258985, baseEnd_258985] using wordTrace_append hprefix tailTrace_258985
  have hstable : (prefixWord ++ tailWord_258985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258985).length < 2 ^ (prefixWord ++ tailWord_258985).sum := by decide
  have hdescent : baseEnd_258985 < baseStart_258985 := by decide
  rcases family_descends (prefixWord ++ tailWord_258985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259012 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_259012 : Nat := 118140960795 + 259012 * 2 ^ 59
def prefixEnd_259012 : Nat := 4983230072969 + 3 ^ 40 * 259012 * 2
def baseEnd_259012 : Nat := 118220134473285198274517

theorem tailTrace_259012 : CollatzResearch.WordTrace tailWord_259012 prefixEnd_259012 118220134473285198274517 := by
  unfold tailWord_259012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723471868825617286461645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6297962491767489715282193 4723471868825617286461645)
  ·
    refine ⟨1771301950809606482423117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4723471868825617286461645 1771301950809606482423117)
    ·
      refine ⟨664238231553602430908669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1771301950809606482423117 664238231553602430908669)
      ·
        refine ⟨249089336832600911590751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664238231553602430908669 249089336832600911590751)
        ·
          refine ⟨373634005248901367386127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249089336832600911590751 373634005248901367386127)
          ·
            refine ⟨560451007873352051079191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373634005248901367386127 560451007873352051079191)
            ·
              refine ⟨840676511810028076618787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560451007873352051079191 840676511810028076618787)
              ·
                refine ⟨1261014767715042114928181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840676511810028076618787 1261014767715042114928181)
                ·
                  refine ⟨118220134473285198274517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1261014767715042114928181 118220134473285198274517)
                  ·
                    rfl

theorem cell20_259012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_259012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259012 prefixEnd_259012 := by exact prefixLift 259012
  have htrace : WordTrace (prefixWord ++ tailWord_259012) baseStart_259012 baseEnd_259012 := by
    simpa [prefixWord, tailWord_259012, baseEnd_259012] using wordTrace_append hprefix tailTrace_259012
  have hstable : (prefixWord ++ tailWord_259012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259012).length < 2 ^ (prefixWord ++ tailWord_259012).sum := by decide
  have hdescent : baseEnd_259012 < baseStart_259012 := by decide
  rcases family_descends (prefixWord ++ tailWord_259012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259023 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_259023 : Nat := 118140960795 + 259023 * 2 ^ 59
def prefixEnd_259023 : Nat := 4983230072969 + 3 ^ 40 * 259023 * 2
def baseEnd_259023 : Nat := 118225155173018048907805

theorem tailTrace_259023 : CollatzResearch.WordTrace tailWord_259023 prefixEnd_259023 118225155173018048907805 := by
  unfold tailWord_259023
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447344940611383451573723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6298229960407588967715815 9447344940611383451573723)
  ·
    refine ⟨14171017410917075177360585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9447344940611383451573723 14171017410917075177360585)
    ·
      refine ⟨10628263058187806383020439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14171017410917075177360585 10628263058187806383020439)
      ·
        refine ⟨15942394587281709574530659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628263058187806383020439 15942394587281709574530659)
        ·
          refine ⟨23913591880922564361795989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942394587281709574530659 23913591880922564361795989)
          ·
            refine ⟨1120949619418245204459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23913591880922564361795989 1120949619418245204459187)
            ·
              refine ⟨1681424429127367806688781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120949619418245204459187 1681424429127367806688781)
              ·
                refine ⟨630534160922762927508293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681424429127367806688781 630534160922762927508293)
                ·
                  refine ⟨118225155173018048907805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630534160922762927508293 118225155173018048907805)
                  ·
                    rfl

theorem cell20_259023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_259023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259023 prefixEnd_259023 := by exact prefixLift 259023
  have htrace : WordTrace (prefixWord ++ tailWord_259023) baseStart_259023 baseEnd_259023 := by
    simpa [prefixWord, tailWord_259023, baseEnd_259023] using wordTrace_append hprefix tailTrace_259023
  have hstable : (prefixWord ++ tailWord_259023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259023).length < 2 ^ (prefixWord ++ tailWord_259023).sum := by decide
  have hdescent : baseEnd_259023 < baseStart_259023 := by decide
  rcases family_descends (prefixWord ++ tailWord_259023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259047 : List Nat := [1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_259047 : Nat := 118140960795 + 259047 * 2 ^ 59
def prefixEnd_259047 : Nat := 4983230072969 + 3 ^ 40 * 259047 * 2
def baseEnd_259047 : Nat := 39412036475660210702569

theorem tailTrace_259047 : CollatzResearch.WordTrace tailWord_259047 prefixEnd_259047 39412036475660210702569 := by
  unfold tailWord_259047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448220292524435550447395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6298813528349623700298263 9448220292524435550447395)
  ·
    refine ⟨14172330438786653325671093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9448220292524435550447395 14172330438786653325671093)
    ·
      refine ⟨1328655978636248749281665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14172330438786653325671093 1328655978636248749281665)
      ·
        refine ⟨996491983977186561961249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1328655978636248749281665 996491983977186561961249)
        ·
          refine ⟨747368987982889921470937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996491983977186561961249 747368987982889921470937)
          ·
            refine ⟨560526740987167441103203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747368987982889921470937 560526740987167441103203)
            ·
              refine ⟨840790111480751161654805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560526740987167441103203 840790111480751161654805)
              ·
                refine ⟨39412036475660210702569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 840790111480751161654805 39412036475660210702569)
                ·
                  rfl

theorem cell20_259047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_259047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259047 prefixEnd_259047 := by exact prefixLift 259047
  have htrace : WordTrace (prefixWord ++ tailWord_259047) baseStart_259047 baseEnd_259047 := by
    simpa [prefixWord, tailWord_259047, baseEnd_259047] using wordTrace_append hprefix tailTrace_259047
  have hstable : (prefixWord ++ tailWord_259047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259047).length < 2 ^ (prefixWord ++ tailWord_259047).sum := by decide
  have hdescent : baseEnd_259047 < baseStart_259047 := by decide
  rcases family_descends (prefixWord ++ tailWord_259047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259057 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 2]
def baseStart_259057 : Nat := 118140960795 + 259057 * 2 ^ 59
def prefixEnd_259057 : Nat := 4983230072969 + 3 ^ 40 * 259057 * 2
def baseEnd_259057 : Nat := 118240673699465041774333

theorem tailTrace_259057 : CollatzResearch.WordTrace tailWord_259057 prefixEnd_259057 118240673699465041774333 := by
  unfold tailWord_259057
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448585022488207258311425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6299056681658804838874283 9448585022488207258311425)
  ·
    refine ⟨7086438766866155443733569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9448585022488207258311425 7086438766866155443733569)
    ·
      refine ⟨5314829075149616582800177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086438766866155443733569 5314829075149616582800177)
      ·
        refine ⟨3986121806362212437100133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5314829075149616582800177 3986121806362212437100133)
        ·
          refine ⟨747397838692914831956275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3986121806362212437100133 747397838692914831956275)
          ·
            refine ⟨1121096758039372247934413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747397838692914831956275 1121096758039372247934413)
            ·
              refine ⟨420411284264764592975405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121096758039372247934413 420411284264764592975405)
              ·
                refine ⟨157654231599286722365777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420411284264764592975405 157654231599286722365777)
                ·
                  refine ⟨118240673699465041774333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157654231599286722365777 118240673699465041774333)
                  ·
                    rfl

theorem cell20_259057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_259057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259057 prefixEnd_259057 := by exact prefixLift 259057
  have htrace : WordTrace (prefixWord ++ tailWord_259057) baseStart_259057 baseEnd_259057 := by
    simpa [prefixWord, tailWord_259057, baseEnd_259057] using wordTrace_append hprefix tailTrace_259057
  have hstable : (prefixWord ++ tailWord_259057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259057).length < 2 ^ (prefixWord ++ tailWord_259057).sum := by decide
  have hdescent : baseEnd_259057 < baseStart_259057 := by decide
  rcases family_descends (prefixWord ++ tailWord_259057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259068 : List Nat := [2, 2, 2, 1, 2, 3, 8]
def baseStart_259068 : Nat := 118140960795 + 259068 * 2 ^ 59
def prefixEnd_259068 : Nat := 4983230072969 + 3 ^ 40 * 259068 * 2
def baseEnd_259068 : Nat := 13138410488799765823069

theorem tailTrace_259068 : CollatzResearch.WordTrace tailWord_259068 prefixEnd_259068 13138410488799765823069 := by
  unfold tailWord_259068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724493112724178068480929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6299324150298904091307905 4724493112724178068480929)
  ·
    refine ⟨3543369834543133551360697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4724493112724178068480929 3543369834543133551360697)
    ·
      refine ⟨2657527375907350163520523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3543369834543133551360697 2657527375907350163520523)
      ·
        refine ⟨3986291063861025245280785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657527375907350163520523 3986291063861025245280785)
        ·
          refine ⟨2989718297895768933960589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986291063861025245280785 2989718297895768933960589)
          ·
            refine ⟨1121144361710913350235221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2989718297895768933960589 1121144361710913350235221)
            ·
              refine ⟨13138410488799765823069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1121144361710913350235221 13138410488799765823069)
              ·
                rfl

theorem cell20_259068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_259068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259068 prefixEnd_259068 := by exact prefixLift 259068
  have htrace : WordTrace (prefixWord ++ tailWord_259068) baseStart_259068 baseEnd_259068 := by
    simpa [prefixWord, tailWord_259068, baseEnd_259068] using wordTrace_append hprefix tailTrace_259068
  have hstable : (prefixWord ++ tailWord_259068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259068).length < 2 ^ (prefixWord ++ tailWord_259068).sum := by decide
  have hdescent : baseEnd_259068 < baseStart_259068 := by decide
  rcases family_descends (prefixWord ++ tailWord_259068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259116 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_259116 : Nat := 118140960795 + 259116 * 2 ^ 59
def prefixEnd_259116 : Nat := 4983230072969 + 3 ^ 40 * 259116 * 2
def baseEnd_259116 : Nat := 118267602907123058807425

theorem tailTrace_259116 : CollatzResearch.WordTrace tailWord_259116 prefixEnd_259116 118267602907123058807425 := by
  unfold tailWord_259116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725368464637230167354601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6300491286182973556472801 4725368464637230167354601)
  ·
    refine ⟨3544026348477922625515951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4725368464637230167354601 3544026348477922625515951)
    ·
      refine ⟨5316039522716883938273927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544026348477922625515951 5316039522716883938273927)
      ·
        refine ⟨7974059284075325907410891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316039522716883938273927 7974059284075325907410891)
        ·
          refine ⟨11961088926112988861116337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974059284075325907410891 11961088926112988861116337)
          ·
            refine ⟨8970816694584741645837253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11961088926112988861116337 8970816694584741645837253)
            ·
              refine ⟨1682028130234639058594485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8970816694584741645837253 1682028130234639058594485)
              ·
                refine ⟨157690137209497411743233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1682028130234639058594485 157690137209497411743233)
                ·
                  refine ⟨118267602907123058807425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157690137209497411743233 118267602907123058807425)
                  ·
                    rfl

theorem cell20_259116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_259116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259116 prefixEnd_259116 := by exact prefixLift 259116
  have htrace : WordTrace (prefixWord ++ tailWord_259116) baseStart_259116 baseEnd_259116 := by
    simpa [prefixWord, tailWord_259116, baseEnd_259116] using wordTrace_append hprefix tailTrace_259116
  have hstable : (prefixWord ++ tailWord_259116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259116).length < 2 ^ (prefixWord ++ tailWord_259116).sum := by decide
  have hdescent : baseEnd_259116 < baseStart_259116 := by decide
  rcases family_descends (prefixWord ++ tailWord_259116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259126 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_259126 : Nat := 118140960795 + 259126 * 2 ^ 59
def prefixEnd_259126 : Nat := 4983230072969 + 3 ^ 40 * 259126 * 2
def baseEnd_259126 : Nat := 118272167179607468474051

theorem tailTrace_259126 : CollatzResearch.WordTrace tailWord_259126 prefixEnd_259126 118272167179607468474051 := by
  unfold tailWord_259126
  simp only [CollatzResearch.WordTrace]
  refine ⟨590693853702389502660827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6300734439492154695048821 590693853702389502660827)
  ·
    refine ⟨886040780553584253991241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590693853702389502660827 886040780553584253991241)
    ·
      refine ⟨664530585415188190493431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886040780553584253991241 664530585415188190493431)
      ·
        refine ⟨996795878122782285740147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664530585415188190493431 996795878122782285740147)
        ·
          refine ⟨1495193817184173428610221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996795878122782285740147 1495193817184173428610221)
          ·
            refine ⟨560697681444065035728833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1495193817184173428610221 560697681444065035728833)
            ·
              refine ⟨420523261083048776796625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560697681444065035728833 420523261083048776796625)
              ·
                refine ⟨315392445812286582597469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420523261083048776796625 315392445812286582597469)
                ·
                  refine ⟨118272167179607468474051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315392445812286582597469 118272167179607468474051)
                  ·
                    rfl

theorem cell20_259126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_259126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259126 prefixEnd_259126 := by exact prefixLift 259126
  have htrace : WordTrace (prefixWord ++ tailWord_259126) baseStart_259126 baseEnd_259126 := by
    simpa [prefixWord, tailWord_259126, baseEnd_259126] using wordTrace_append hprefix tailTrace_259126
  have hstable : (prefixWord ++ tailWord_259126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259126).length < 2 ^ (prefixWord ++ tailWord_259126).sum := by decide
  have hdescent : baseEnd_259126 < baseStart_259126 := by decide
  rcases family_descends (prefixWord ++ tailWord_259126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259130 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_259130 : Nat := 118140960795 + 259130 * 2 ^ 59
def prefixEnd_259130 : Nat := 4983230072969 + 3 ^ 40 * 259130 * 2
def baseEnd_259130 : Nat := 118273992888601232340701

theorem tailTrace_259130 : CollatzResearch.WordTrace tailWord_259130 prefixEnd_259130 118273992888601232340701 := by
  unfold tailWord_259130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362811887805935181429711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6300831700815827150479229 2362811887805935181429711)
  ·
    refine ⟨3544217831708902772144567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2362811887805935181429711 3544217831708902772144567)
    ·
      refine ⟨5316326747563354158216851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544217831708902772144567 5316326747563354158216851)
      ·
        refine ⟨7974490121345031237325277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316326747563354158216851 7974490121345031237325277)
        ·
          refine ⟨2990433795504386713996979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7974490121345031237325277 2990433795504386713996979)
          ·
            refine ⟨4485650693256580070995469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990433795504386713996979 4485650693256580070995469)
            ·
              refine ⟨1682119009971217526623301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4485650693256580070995469 1682119009971217526623301)
              ·
                refine ⟨315397314369603286241869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1682119009971217526623301 315397314369603286241869)
                ·
                  refine ⟨118273992888601232340701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315397314369603286241869 118273992888601232340701)
                  ·
                    rfl

theorem cell20_259130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_259130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259130 prefixEnd_259130 := by exact prefixLift 259130
  have htrace : WordTrace (prefixWord ++ tailWord_259130) baseStart_259130 baseEnd_259130 := by
    simpa [prefixWord, tailWord_259130, baseEnd_259130] using wordTrace_append hprefix tailTrace_259130
  have hstable : (prefixWord ++ tailWord_259130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259130).length < 2 ^ (prefixWord ++ tailWord_259130).sum := by decide
  have hdescent : baseEnd_259130 < baseStart_259130 := by decide
  rcases family_descends (prefixWord ++ tailWord_259130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259133 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 2]
def baseStart_259133 : Nat := 118140960795 + 259133 * 2 ^ 59
def prefixEnd_259133 : Nat := 4983230072969 + 3 ^ 40 * 259133 * 2
def baseEnd_259133 : Nat := 118275362170346555240689

theorem tailTrace_259133 : CollatzResearch.WordTrace tailWord_259133 prefixEnd_259133 118275362170346555240689 := by
  unfold tailWord_259133
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451356970212872238078053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6300904646808581492052035 9451356970212872238078053)
  ·
    refine ⟨1772129431914913544639635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9451356970212872238078053 1772129431914913544639635)
    ·
      refine ⟨2658194147872370316959453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772129431914913544639635 2658194147872370316959453)
      ·
        refine ⟨996822805452138868859795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2658194147872370316959453 996822805452138868859795)
        ·
          refine ⟨1495234208178208303289693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996822805452138868859795 1495234208178208303289693)
          ·
            refine ⟨560712828066828113733635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1495234208178208303289693 560712828066828113733635)
            ·
              refine ⟨841069242100242170600453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560712828066828113733635 841069242100242170600453)
              ·
                refine ⟨157700482893795406987585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841069242100242170600453 157700482893795406987585)
                ·
                  refine ⟨118275362170346555240689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157700482893795406987585 118275362170346555240689)
                  ·
                    rfl

theorem cell20_259133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_259133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259133 prefixEnd_259133 := by exact prefixLift 259133
  have htrace : WordTrace (prefixWord ++ tailWord_259133) baseStart_259133 baseEnd_259133 := by
    simpa [prefixWord, tailWord_259133, baseEnd_259133] using wordTrace_append hprefix tailTrace_259133
  have hstable : (prefixWord ++ tailWord_259133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259133).length < 2 ^ (prefixWord ++ tailWord_259133).sum := by decide
  have hdescent : baseEnd_259133 < baseStart_259133 := by decide
  rcases family_descends (prefixWord ++ tailWord_259133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259154 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_259154 : Nat := 118140960795 + 259154 * 2 ^ 59
def prefixEnd_259154 : Nat := 4983230072969 + 3 ^ 40 * 259154 * 2
def baseEnd_259154 : Nat := 118284947142563815540603

theorem tailTrace_259154 : CollatzResearch.WordTrace tailWord_259154 prefixEnd_259154 118284947142563815540603 := by
  unfold tailWord_259154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363030725784198206148129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6301415268757861883061677 2363030725784198206148129)
  ·
    refine ⟨1772273044338148654611097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2363030725784198206148129 1772273044338148654611097)
    ·
      refine ⟨1329204783253611490958323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1772273044338148654611097 1329204783253611490958323)
      ·
        refine ⟨1993807174880417236437485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329204783253611490958323 1993807174880417236437485)
        ·
          refine ⟨747677690580156463664057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1993807174880417236437485 747677690580156463664057)
          ·
            refine ⟨560758267935117347748043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747677690580156463664057 560758267935117347748043)
            ·
              refine ⟨841137401902676021622065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560758267935117347748043 841137401902676021622065)
              ·
                refine ⟨630853051427007016216549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841137401902676021622065 630853051427007016216549)
                ·
                  refine ⟨118284947142563815540603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630853051427007016216549 118284947142563815540603)
                  ·
                    rfl

theorem cell20_259154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_259154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259154 prefixEnd_259154 := by exact prefixLift 259154
  have htrace : WordTrace (prefixWord ++ tailWord_259154) baseStart_259154 baseEnd_259154 := by
    simpa [prefixWord, tailWord_259154, baseEnd_259154] using wordTrace_append hprefix tailTrace_259154
  have hstable : (prefixWord ++ tailWord_259154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259154).length < 2 ^ (prefixWord ++ tailWord_259154).sum := by decide
  have hdescent : baseEnd_259154 < baseStart_259154 := by decide
  rcases family_descends (prefixWord ++ tailWord_259154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259192 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_259192 : Nat := 118140960795 + 259192 * 2 ^ 59
def prefixEnd_259192 : Nat := 4983230072969 + 3 ^ 40 * 259192 * 2
def baseEnd_259192 : Nat := 118302291378004572273781

theorem tailTrace_259192 : CollatzResearch.WordTrace tailWord_259192 prefixEnd_259192 118302291378004572273781 := by
  unfold tailWord_259192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726754438499562657237915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6302339251332750209650553 4726754438499562657237915)
  ·
    refine ⟨7090131657749343985856873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726754438499562657237915 7090131657749343985856873)
    ·
      refine ⟨5317598743312007989392655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7090131657749343985856873 5317598743312007989392655)
      ·
        refine ⟨7976398114968011984088983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317598743312007989392655 7976398114968011984088983)
        ·
          refine ⟨11964597172452017976133475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976398114968011984088983 11964597172452017976133475)
          ·
            refine ⟨17946895758678026964200213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964597172452017976133475 17946895758678026964200213)
            ·
              refine ⟨841260738688032513946885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17946895758678026964200213 841260738688032513946885)
              ·
                refine ⟨157736388504006096365041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841260738688032513946885 157736388504006096365041)
                ·
                  refine ⟨118302291378004572273781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157736388504006096365041 118302291378004572273781)
                  ·
                    rfl

theorem cell20_259192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_259192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259192 prefixEnd_259192 := by exact prefixLift 259192
  have htrace : WordTrace (prefixWord ++ tailWord_259192) baseStart_259192 baseEnd_259192 := by
    simpa [prefixWord, tailWord_259192, baseEnd_259192] using wordTrace_append hprefix tailTrace_259192
  have hstable : (prefixWord ++ tailWord_259192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259192).length < 2 ^ (prefixWord ++ tailWord_259192).sum := by decide
  have hdescent : baseEnd_259192 < baseStart_259192 := by decide
  rcases family_descends (prefixWord ++ tailWord_259192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259226 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_259226 : Nat := 118140960795 + 259226 * 2 ^ 59
def prefixEnd_259226 : Nat := 4983230072969 + 3 ^ 40 * 259226 * 2
def baseEnd_259226 : Nat := 118317809904451565140309

theorem tailTrace_259226 : CollatzResearch.WordTrace tailWord_259226 prefixEnd_259226 118317809904451565140309 := by
  unfold tailWord_259226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363687239718987280303383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6303165972583966080809021 2363687239718987280303383)
  ·
    refine ⟨3545530859578480920455075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363687239718987280303383 3545530859578480920455075)
    ·
      refine ⟨5318296289367721380682613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545530859578480920455075 5318296289367721380682613)
      ·
        refine ⟨498590277128223879438995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5318296289367721380682613 498590277128223879438995)
        ·
          refine ⟨747885415692335819158493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498590277128223879438995 747885415692335819158493)
          ·
            refine ⟨280457030884625932184435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747885415692335819158493 280457030884625932184435)
            ·
              refine ⟨420685546326938898276653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280457030884625932184435 420685546326938898276653)
              ·
                refine ⟨157757079872602086853745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420685546326938898276653 157757079872602086853745)
                ·
                  refine ⟨118317809904451565140309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157757079872602086853745 118317809904451565140309)
                  ·
                    rfl

theorem cell20_259226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_259226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259226 prefixEnd_259226 := by exact prefixLift 259226
  have htrace : WordTrace (prefixWord ++ tailWord_259226) baseStart_259226 baseEnd_259226 := by
    simpa [prefixWord, tailWord_259226, baseEnd_259226] using wordTrace_append hprefix tailTrace_259226
  have hstable : (prefixWord ++ tailWord_259226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259226).length < 2 ^ (prefixWord ++ tailWord_259226).sum := by decide
  have hdescent : baseEnd_259226 < baseStart_259226 := by decide
  rcases family_descends (prefixWord ++ tailWord_259226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259251 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_259251 : Nat := 118140960795 + 259251 * 2 ^ 59
def prefixEnd_259251 : Nat := 4983230072969 + 3 ^ 40 * 259251 * 2
def baseEnd_259251 : Nat := 118329220585662589306873

theorem tailTrace_259251 : CollatzResearch.WordTrace tailWord_259251 prefixEnd_259251 118329220585662589306873 := by
  unfold tailWord_259251
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455660783785378390873607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6303773855856918927249071 9455660783785378390873607)
  ·
    refine ⟨14183491175678067586310411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9455660783785378390873607 14183491175678067586310411)
    ·
      refine ⟨21275236763517101379465617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183491175678067586310411 21275236763517101379465617)
      ·
        refine ⟨15956427572637826034599213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21275236763517101379465617 15956427572637826034599213)
        ·
          refine ⟨5983660339739184762974705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15956427572637826034599213 5983660339739184762974705)
          ·
            refine ⟨4487745254804388572231029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5983660339739184762974705 4487745254804388572231029)
            ·
              refine ⟨420726117637911428646659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4487745254804388572231029 420726117637911428646659)
              ·
                refine ⟨631089176456867142969989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420726117637911428646659 631089176456867142969989)
                ·
                  refine ⟨118329220585662589306873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631089176456867142969989 118329220585662589306873)
                  ·
                    rfl

theorem cell20_259251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_259251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259251 prefixEnd_259251 := by exact prefixLift 259251
  have htrace : WordTrace (prefixWord ++ tailWord_259251) baseStart_259251 baseEnd_259251 := by
    simpa [prefixWord, tailWord_259251, baseEnd_259251] using wordTrace_append hprefix tailTrace_259251
  have hstable : (prefixWord ++ tailWord_259251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259251).length < 2 ^ (prefixWord ++ tailWord_259251).sum := by decide
  have hdescent : baseEnd_259251 < baseStart_259251 := by decide
  rcases family_descends (prefixWord ++ tailWord_259251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259261 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 3]
def baseStart_259261 : Nat := 118140960795 + 259261 * 2 ^ 59
def prefixEnd_259261 : Nat := 4983230072969 + 3 ^ 40 * 259261 * 2
def baseEnd_259261 : Nat := 118333784858146998973499

theorem tailTrace_259261 : CollatzResearch.WordTrace tailWord_259261 prefixEnd_259261 118333784858146998973499 := by
  unfold tailWord_259261
  simp only [CollatzResearch.WordTrace]
  refine ⟨9456025513749150098737637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6304017009166100065825091 9456025513749150098737637)
  ·
    refine ⟨1773004783827965643513307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9456025513749150098737637 1773004783827965643513307)
    ·
      refine ⟨2659507175741948465269961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773004783827965643513307 2659507175741948465269961)
      ·
        refine ⟨1994630381806461348952471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659507175741948465269961 1994630381806461348952471)
        ·
          refine ⟨2991945572709692023428707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994630381806461348952471 2991945572709692023428707)
          ·
            refine ⟨4487918359064538035143061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991945572709692023428707 4487918359064538035143061)
            ·
              refine ⟨210371173081150220397331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4487918359064538035143061 210371173081150220397331)
              ·
                refine ⟨315556759621725330595997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210371173081150220397331 315556759621725330595997)
                ·
                  refine ⟨118333784858146998973499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315556759621725330595997 118333784858146998973499)
                  ·
                    rfl

theorem cell20_259261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_259261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259261 prefixEnd_259261 := by exact prefixLift 259261
  have htrace : WordTrace (prefixWord ++ tailWord_259261) baseStart_259261 baseEnd_259261 := by
    simpa [prefixWord, tailWord_259261, baseEnd_259261] using wordTrace_append hprefix tailTrace_259261
  have hstable : (prefixWord ++ tailWord_259261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259261).length < 2 ^ (prefixWord ++ tailWord_259261).sum := by decide
  have hdescent : baseEnd_259261 < baseStart_259261 := by decide
  rcases family_descends (prefixWord ++ tailWord_259261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259327 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_259327 : Nat := 118140960795 + 259327 * 2 ^ 59
def prefixEnd_259327 : Nat := 4983230072969 + 3 ^ 40 * 259327 * 2
def baseEnd_259327 : Nat := 118363909056544102773229

theorem tailTrace_259327 : CollatzResearch.WordTrace tailWord_259327 prefixEnd_259327 118363909056544102773229 := by
  unfold tailWord_259327
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458432731510043370640235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6305621821006695580426823 9458432731510043370640235)
  ·
    refine ⟨14187649097265065055960353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9458432731510043370640235 14187649097265065055960353)
    ·
      refine ⟨10640736822948798791970265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14187649097265065055960353 10640736822948798791970265)
      ·
        refine ⟨7980552617211599093977699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10640736822948798791970265 7980552617211599093977699)
        ·
          refine ⟨11970828925817398640966549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7980552617211599093977699 11970828925817398640966549)
          ·
            refine ⟨561132605897690561295307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11970828925817398640966549 561132605897690561295307)
            ·
              refine ⟨841698908846535841942961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561132605897690561295307 841698908846535841942961)
              ·
                refine ⟨631274181634901881457221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841698908846535841942961 631274181634901881457221)
                ·
                  refine ⟨118363909056544102773229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631274181634901881457221 118363909056544102773229)
                  ·
                    rfl

theorem cell20_259327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_259327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259327 prefixEnd_259327 := by exact prefixLift 259327
  have htrace : WordTrace (prefixWord ++ tailWord_259327) baseStart_259327 baseEnd_259327 := by
    simpa [prefixWord, tailWord_259327, baseEnd_259327] using wordTrace_append hprefix tailTrace_259327
  have hstable : (prefixWord ++ tailWord_259327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259327).length < 2 ^ (prefixWord ++ tailWord_259327).sum := by decide
  have hdescent : baseEnd_259327 < baseStart_259327 := by decide
  rcases family_descends (prefixWord ++ tailWord_259327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259365 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_259365 : Nat := 118140960795 + 259365 * 2 ^ 59
def prefixEnd_259365 : Nat := 4983230072969 + 3 ^ 40 * 259365 * 2
def baseEnd_259365 : Nat := 118381253291984859506407

theorem tailTrace_259365 : CollatzResearch.WordTrace tailWord_259365 prefixEnd_259365 118381253291984859506407 := by
  unfold tailWord_259365
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459818705372375860523549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6306545803581583907015699 9459818705372375860523549)
  ·
    refine ⟨3547432014514640947696331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9459818705372375860523549 3547432014514640947696331)
    ·
      refine ⟨5321148021771961421544497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547432014514640947696331 5321148021771961421544497)
      ·
        refine ⟨3990861016328971066158373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5321148021771961421544497 3990861016328971066158373)
        ·
          refine ⟨748286440561682074904695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3990861016328971066158373 748286440561682074904695)
          ·
            refine ⟨1122429660842523112357043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748286440561682074904695 1122429660842523112357043)
            ·
              refine ⟨1683644491263784668535565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122429660842523112357043 1683644491263784668535565)
              ·
                refine ⟨631366684223919250700837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683644491263784668535565 631366684223919250700837)
                ·
                  refine ⟨118381253291984859506407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631366684223919250700837 118381253291984859506407)
                  ·
                    rfl

theorem cell20_259365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_259365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259365 prefixEnd_259365 := by exact prefixLift 259365
  have htrace : WordTrace (prefixWord ++ tailWord_259365) baseStart_259365 baseEnd_259365 := by
    simpa [prefixWord, tailWord_259365, baseEnd_259365] using wordTrace_append hprefix tailTrace_259365
  have hstable : (prefixWord ++ tailWord_259365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259365).length < 2 ^ (prefixWord ++ tailWord_259365).sum := by decide
  have hdescent : baseEnd_259365 < baseStart_259365 := by decide
  rcases family_descends (prefixWord ++ tailWord_259365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259385 : List Nat := [1, 2, 1, 6, 3, 1, 2, 4]
def baseStart_259385 : Nat := 118140960795 + 259385 * 2 ^ 59
def prefixEnd_259385 : Nat := 4983230072969 + 3 ^ 40 * 259385 * 2
def baseEnd_259385 : Nat := 39463460612317892946553

theorem tailTrace_259385 : CollatzResearch.WordTrace tailWord_259385 prefixEnd_259385 39463460612317892946553 := by
  unfold tailWord_259385
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460548165299919276251609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307032110199946184167739 9460548165299919276251609)
  ·
    refine ⟨7095411123974939457188707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9460548165299919276251609 7095411123974939457188707)
    ·
      refine ⟨10643116685962409185783061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095411123974939457188707 10643116685962409185783061)
      ·
        refine ⟨498896094654487930583581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10643116685962409185783061 498896094654487930583581)
        ·
          refine ⟨187086035495432973968843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498896094654487930583581 187086035495432973968843)
          ·
            refine ⟨280629053243149460953265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187086035495432973968843 280629053243149460953265)
            ·
              refine ⟨210471789932362095714949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280629053243149460953265 210471789932362095714949)
              ·
                refine ⟨39463460612317892946553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210471789932362095714949 39463460612317892946553)
                ·
                  rfl

theorem cell20_259385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_259385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259385 prefixEnd_259385 := by exact prefixLift 259385
  have htrace : WordTrace (prefixWord ++ tailWord_259385) baseStart_259385 baseEnd_259385 := by
    simpa [prefixWord, tailWord_259385, baseEnd_259385] using wordTrace_append hprefix tailTrace_259385
  have hstable : (prefixWord ++ tailWord_259385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259385).length < 2 ^ (prefixWord ++ tailWord_259385).sum := by decide
  have hdescent : baseEnd_259385 < baseStart_259385 := by decide
  rcases family_descends (prefixWord ++ tailWord_259385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259399 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 2]
def baseStart_259399 : Nat := 118140960795 + 259399 * 2 ^ 59
def prefixEnd_259399 : Nat := 4983230072969 + 3 ^ 40 * 259399 * 2
def baseEnd_259399 : Nat := 118396771818431852372935

theorem tailTrace_259399 : CollatzResearch.WordTrace tailWord_259399 prefixEnd_259399 118396771818431852372935 := by
  unfold tailWord_259399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461058787249199667261251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307372524832799778174167 9461058787249199667261251)
  ·
    refine ⟨14191588180873799500891877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9461058787249199667261251 14191588180873799500891877)
    ·
      refine ⟨2660922783913837406417227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14191588180873799500891877 2660922783913837406417227)
      ·
        refine ⟨3991384175870756109625841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660922783913837406417227 3991384175870756109625841)
        ·
          refine ⟨2993538131903067082219381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3991384175870756109625841 2993538131903067082219381)
          ·
            refine ⟨280644199865912538958067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2993538131903067082219381 280644199865912538958067)
            ·
              refine ⟨420966299798868808437101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280644199865912538958067 420966299798868808437101)
              ·
                refine ⟨157862362424575803163913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420966299798868808437101 157862362424575803163913)
                ·
                  refine ⟨118396771818431852372935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157862362424575803163913 118396771818431852372935)
                  ·
                    rfl

theorem cell20_259399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2].length) (baseStart_259399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259399 prefixEnd_259399 := by exact prefixLift 259399
  have htrace : WordTrace (prefixWord ++ tailWord_259399) baseStart_259399 baseEnd_259399 := by
    simpa [prefixWord, tailWord_259399, baseEnd_259399] using wordTrace_append hprefix tailTrace_259399
  have hstable : (prefixWord ++ tailWord_259399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259399).length < 2 ^ (prefixWord ++ tailWord_259399).sum := by decide
  have hdescent : baseEnd_259399 < baseStart_259399 := by decide
  rcases family_descends (prefixWord ++ tailWord_259399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259417 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_259417 : Nat := 118140960795 + 259417 * 2 ^ 59
def prefixEnd_259417 : Nat := 4983230072969 + 3 ^ 40 * 259417 * 2
def baseEnd_259417 : Nat := 118404987508903789772861

theorem tailTrace_259417 : CollatzResearch.WordTrace tailWord_259417 prefixEnd_259417 118404987508903789772861 := by
  unfold tailWord_259417
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461715301183988741416505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307810200789325827611003 9461715301183988741416505)
  ·
    refine ⟨7096286475887991556062379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9461715301183988741416505 7096286475887991556062379)
    ·
      refine ⟨10644429713831987334093569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096286475887991556062379 10644429713831987334093569)
      ·
        refine ⟨7983322285373990500570177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10644429713831987334093569 7983322285373990500570177)
        ·
          refine ⟨5987491714030492875427633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7983322285373990500570177 5987491714030492875427633)
          ·
            refine ⟨4490618785522869656570725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987491714030492875427633 4490618785522869656570725)
            ·
              refine ⟨841991022285538060607011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4490618785522869656570725 841991022285538060607011)
              ·
                refine ⟨1262986533428307090910517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841991022285538060607011 1262986533428307090910517)
                ·
                  refine ⟨118404987508903789772861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1262986533428307090910517 118404987508903789772861)
                  ·
                    rfl

theorem cell20_259417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_259417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259417 prefixEnd_259417 := by exact prefixLift 259417
  have htrace : WordTrace (prefixWord ++ tailWord_259417) baseStart_259417 baseEnd_259417 := by
    simpa [prefixWord, tailWord_259417, baseEnd_259417] using wordTrace_append hprefix tailTrace_259417
  have hstable : (prefixWord ++ tailWord_259417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259417).length < 2 ^ (prefixWord ++ tailWord_259417).sum := by decide
  have hdescent : baseEnd_259417 < baseStart_259417 := by decide
  rcases family_descends (prefixWord ++ tailWord_259417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259500 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_259500 : Nat := 118140960795 + 259500 * 2 ^ 59
def prefixEnd_259500 : Nat := 4983230072969 + 3 ^ 40 * 259500 * 2
def baseEnd_259500 : Nat := 118442870970524390005855

theorem tailTrace_259500 : CollatzResearch.WordTrace tailWord_259500 prefixEnd_259500 118442870970524390005855 := by
  unfold tailWord_259500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732371279941646958343977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6309828373255529277791969 4732371279941646958343977)
  ·
    refine ⟨3549278459956235218757983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732371279941646958343977 3549278459956235218757983)
    ·
      refine ⟨5323917689934352828136975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549278459956235218757983 5323917689934352828136975)
      ·
        refine ⟨7985876534901529242205463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323917689934352828136975 7985876534901529242205463)
        ·
          refine ⟨11978814802352293863308195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7985876534901529242205463 11978814802352293863308195)
          ·
            refine ⟨17968222203528440794962293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978814802352293863308195 17968222203528440794962293)
            ·
              refine ⟨1684520831580791324527715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17968222203528440794962293 1684520831580791324527715)
              ·
                refine ⟨2526781247371186986791573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684520831580791324527715 2526781247371186986791573)
                ·
                  refine ⟨118442870970524390005855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2526781247371186986791573 118442870970524390005855)
                  ·
                    rfl

theorem cell20_259500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_259500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259500 prefixEnd_259500 := by exact prefixLift 259500
  have htrace : WordTrace (prefixWord ++ tailWord_259500) baseStart_259500 baseEnd_259500 := by
    simpa [prefixWord, tailWord_259500, baseEnd_259500] using wordTrace_append hprefix tailTrace_259500
  have hstable : (prefixWord ++ tailWord_259500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259500).length < 2 ^ (prefixWord ++ tailWord_259500).sum := by decide
  have hdescent : baseEnd_259500 < baseStart_259500 := by decide
  rcases family_descends (prefixWord ++ tailWord_259500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259507 : List Nat := [1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_259507 : Nat := 118140960795 + 259507 * 2 ^ 59
def prefixEnd_259507 : Nat := 4983230072969 + 3 ^ 40 * 259507 * 2
def baseEnd_259507 : Nat := 39482021987087825590831

theorem tailTrace_259507 : CollatzResearch.WordTrace tailWord_259507 prefixEnd_259507 39482021987087825590831 := by
  unfold tailWord_259507
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464997870857934112192775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6309998580571956074795183 9464997870857934112192775)
  ·
    refine ⟨14197496806286901168289163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464997870857934112192775 14197496806286901168289163)
    ·
      refine ⟨21296245209430351752433745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14197496806286901168289163 21296245209430351752433745)
      ·
        refine ⟨15972183907072763814325309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21296245209430351752433745 15972183907072763814325309)
        ·
          refine ⟨5989568965152286430371991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15972183907072763814325309 5989568965152286430371991)
          ·
            refine ⟨8984353447728429645557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989568965152286430371991 8984353447728429645557987)
            ·
              refine ⟨13476530171592644468336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984353447728429645557987 13476530171592644468336981)
              ·
                refine ⟨39482021987087825590831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13476530171592644468336981 39482021987087825590831)
                ·
                  rfl

theorem cell20_259507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_259507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259507 prefixEnd_259507 := by exact prefixLift 259507
  have htrace : WordTrace (prefixWord ++ tailWord_259507) baseStart_259507 baseEnd_259507 := by
    simpa [prefixWord, tailWord_259507, baseEnd_259507] using wordTrace_append hprefix tailTrace_259507
  have hstable : (prefixWord ++ tailWord_259507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259507).length < 2 ^ (prefixWord ++ tailWord_259507).sum := by decide
  have hdescent : baseEnd_259507 < baseStart_259507 := by decide
  rcases family_descends (prefixWord ++ tailWord_259507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259513 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 2]
def baseStart_259513 : Nat := 118140960795 + 259513 * 2 ^ 59
def prefixEnd_259513 : Nat := 4983230072969 + 3 ^ 40 * 259513 * 2
def baseEnd_259513 : Nat := 118448804524754122572469

theorem tailTrace_259513 : CollatzResearch.WordTrace tailWord_259513 prefixEnd_259513 118448804524754122572469 := by
  unfold tailWord_259513
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465216708836197136911193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6310144472557464757940795 9465216708836197136911193)
  ·
    refine ⟨7098912531627147852683395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9465216708836197136911193 7098912531627147852683395)
    ·
      refine ⟨10648368797440721779025093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098912531627147852683395 10648368797440721779025093)
      ·
        refine ⟨1996569149520135333567205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10648368797440721779025093 1996569149520135333567205)
        ·
          refine ⟨374356715535025375043851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1996569149520135333567205 374356715535025375043851)
          ·
            refine ⟨561535073302538062565777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374356715535025375043851 561535073302538062565777)
            ·
              refine ⟨421151304976903546924333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561535073302538062565777 421151304976903546924333)
              ·
                refine ⟨157931739366338830096625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421151304976903546924333 157931739366338830096625)
                ·
                  refine ⟨118448804524754122572469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157931739366338830096625 118448804524754122572469)
                  ·
                    rfl

theorem cell20_259513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_259513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259513 prefixEnd_259513 := by exact prefixLift 259513
  have htrace : WordTrace (prefixWord ++ tailWord_259513) baseStart_259513 baseEnd_259513 := by
    simpa [prefixWord, tailWord_259513, baseEnd_259513] using wordTrace_append hprefix tailTrace_259513
  have hstable : (prefixWord ++ tailWord_259513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259513).length < 2 ^ (prefixWord ++ tailWord_259513).sum := by decide
  have hdescent : baseEnd_259513 < baseStart_259513 := by decide
  rcases family_descends (prefixWord ++ tailWord_259513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259534 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_259534 : Nat := 118140960795 + 259534 * 2 ^ 59
def prefixEnd_259534 : Nat := 4983230072969 + 3 ^ 40 * 259534 * 2
def baseEnd_259534 : Nat := 118458389496971382872383

theorem tailTrace_259534 : CollatzResearch.WordTrace tailWord_259534 prefixEnd_259534 118458389496971382872383 := by
  unfold tailWord_259534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183247830220014715428207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6310655094506745148950437 1183247830220014715428207)
  ·
    refine ⟨1774871745330022073142311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183247830220014715428207 1774871745330022073142311)
    ·
      refine ⟨2662307617995033109713467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774871745330022073142311 2662307617995033109713467)
      ·
        refine ⟨3993461426992549664570201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662307617995033109713467 3993461426992549664570201)
        ·
          refine ⟨2995096070244412248427651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993461426992549664570201 2995096070244412248427651)
          ·
            refine ⟨4492644105366618372641477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995096070244412248427651 4492644105366618372641477)
            ·
              refine ⟨842370769756240944870277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4492644105366618372641477 842370769756240944870277)
              ·
                refine ⟨157944519329295177163177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842370769756240944870277 157944519329295177163177)
                ·
                  refine ⟨118458389496971382872383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157944519329295177163177 118458389496971382872383)
                  ·
                    rfl

theorem cell20_259534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_259534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259534 prefixEnd_259534 := by exact prefixLift 259534
  have htrace : WordTrace (prefixWord ++ tailWord_259534) baseStart_259534 baseEnd_259534 := by
    simpa [prefixWord, tailWord_259534, baseEnd_259534] using wordTrace_append hprefix tailTrace_259534
  have hstable : (prefixWord ++ tailWord_259534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259534).length < 2 ^ (prefixWord ++ tailWord_259534).sum := by decide
  have hdescent : baseEnd_259534 < baseStart_259534 := by decide
  rcases family_descends (prefixWord ++ tailWord_259534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259555 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_259555 : Nat := 118140960795 + 259555 * 2 ^ 59
def prefixEnd_259555 : Nat := 4983230072969 + 3 ^ 40 * 259555 * 2
def baseEnd_259555 : Nat := 118467974469188643172297

theorem tailTrace_259555 : CollatzResearch.WordTrace tailWord_259555 prefixEnd_259555 118467974469188643172297 := by
  unfold tailWord_259555
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466748574684038309940119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6311165716456025539960079 9466748574684038309940119)
  ·
    refine ⟨14200122862026057464910179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9466748574684038309940119 14200122862026057464910179)
    ·
      refine ⟨21300184293039086197365269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14200122862026057464910179 21300184293039086197365269)
      ·
        refine ⟨998446138736207165501497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21300184293039086197365269 998446138736207165501497)
        ·
          refine ⟨748834604052155374126123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998446138736207165501497 748834604052155374126123)
          ·
            refine ⟨1123251906078233061189185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748834604052155374126123 1123251906078233061189185)
            ·
              refine ⟨842438929558674795891889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123251906078233061189185 842438929558674795891889)
              ·
                refine ⟨631829197169006096918917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842438929558674795891889 631829197169006096918917)
                ·
                  refine ⟨118467974469188643172297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631829197169006096918917 118467974469188643172297)
                  ·
                    rfl

theorem cell20_259555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_259555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259555 prefixEnd_259555 := by exact prefixLift 259555
  have htrace : WordTrace (prefixWord ++ tailWord_259555) baseStart_259555 baseEnd_259555 := by
    simpa [prefixWord, tailWord_259555, baseEnd_259555] using wordTrace_append hprefix tailTrace_259555
  have hstable : (prefixWord ++ tailWord_259555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259555).length < 2 ^ (prefixWord ++ tailWord_259555).sum := by decide
  have hdescent : baseEnd_259555 < baseStart_259555 := by decide
  rcases family_descends (prefixWord ++ tailWord_259555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259569 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_259569 : Nat := 118140960795 + 259569 * 2 ^ 59
def prefixEnd_259569 : Nat := 4983230072969 + 3 ^ 40 * 259569 * 2
def baseEnd_259569 : Nat := 118474364450666816705573

theorem tailTrace_259569 : CollatzResearch.WordTrace tailWord_259569 prefixEnd_259569 118474364450666816705573 := by
  unfold tailWord_259569
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467259196633318700949761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6311506131088879133966507 9467259196633318700949761)
  ·
    refine ⟨7100444397474989025712321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9467259196633318700949761 7100444397474989025712321)
    ·
      refine ⟨5325333298106241769284241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7100444397474989025712321 5325333298106241769284241)
      ·
        refine ⟨3993999973579681326963181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5325333298106241769284241 3993999973579681326963181)
        ·
          refine ⟨1497749990092380497611193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993999973579681326963181 1497749990092380497611193)
          ·
            refine ⟨1123312492569285373208395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497749990092380497611193 1123312492569285373208395)
            ·
              refine ⟨1684968738853928059812593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123312492569285373208395 1684968738853928059812593)
              ·
                refine ⟨1263726554140446044859445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684968738853928059812593 1263726554140446044859445)
                ·
                  refine ⟨118474364450666816705573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1263726554140446044859445 118474364450666816705573)
                  ·
                    rfl

theorem cell20_259569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_259569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259569 prefixEnd_259569 := by exact prefixLift 259569
  have htrace : WordTrace (prefixWord ++ tailWord_259569) baseStart_259569 baseEnd_259569 := by
    simpa [prefixWord, tailWord_259569, baseEnd_259569] using wordTrace_append hprefix tailTrace_259569
  have hstable : (prefixWord ++ tailWord_259569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259569).length < 2 ^ (prefixWord ++ tailWord_259569).sum := by decide
  have hdescent : baseEnd_259569 < baseStart_259569 := by decide
  rcases family_descends (prefixWord ++ tailWord_259569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259603 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 3]
def baseStart_259603 : Nat := 118140960795 + 259603 * 2 ^ 59
def prefixEnd_259603 : Nat := 4983230072969 + 3 ^ 40 * 259603 * 2
def baseEnd_259603 : Nat := 118489882977113809572101

theorem tailTrace_259603 : CollatzResearch.WordTrace tailWord_259603 prefixEnd_259603 118489882977113809572101 := by
  unfold tailWord_259603
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468499278510142507687463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6312332852340095005124975 9468499278510142507687463)
  ·
    refine ⟨14202748917765213761531195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9468499278510142507687463 14202748917765213761531195)
    ·
      refine ⟨21304123376647820642296793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202748917765213761531195 21304123376647820642296793)
      ·
        refine ⟨15978092532485865481722595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21304123376647820642296793 15978092532485865481722595)
        ·
          refine ⟨23967138798728798222583893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15978092532485865481722595 23967138798728798222583893)
          ·
            refine ⟨280864907797603104170905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 23967138798728798222583893 280864907797603104170905)
            ·
              refine ⟨210648680848202328128179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280864907797603104170905 210648680848202328128179)
              ·
                refine ⟨315973021272303492192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210648680848202328128179 315973021272303492192269)
                ·
                  refine ⟨118489882977113809572101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315973021272303492192269 118489882977113809572101)
                  ·
                    rfl

theorem cell20_259603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_259603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259603 prefixEnd_259603 := by exact prefixLift 259603
  have htrace : WordTrace (prefixWord ++ tailWord_259603) baseStart_259603 baseEnd_259603 := by
    simpa [prefixWord, tailWord_259603, baseEnd_259603] using wordTrace_append hprefix tailTrace_259603
  have hstable : (prefixWord ++ tailWord_259603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259603).length < 2 ^ (prefixWord ++ tailWord_259603).sum := by decide
  have hdescent : baseEnd_259603 < baseStart_259603 := by decide
  rcases family_descends (prefixWord ++ tailWord_259603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259638 : List Nat := [5, 1, 2, 1, 11]
def baseStart_259638 : Nat := 118140960795 + 259638 * 2 ^ 59
def prefixEnd_259638 : Nat := 4983230072969 + 3 ^ 40 * 259638 * 2
def baseEnd_259638 : Nat := 1463035283096410412411

theorem tailTrace_259638 : CollatzResearch.WordTrace tailWord_259638 prefixEnd_259638 1463035283096410412411 := by
  unfold tailWord_259638
  simp only [CollatzResearch.WordTrace]
  refine ⟨591860989586458967825723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6313183888922228990141045 591860989586458967825723)
  ·
    refine ⟨887791484379688451738585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591860989586458967825723 887791484379688451738585)
    ·
      refine ⟨665843613284766338803939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 887791484379688451738585 665843613284766338803939)
      ·
        refine ⟨998765419927149508205909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665843613284766338803939 998765419927149508205909)
        ·
          refine ⟨1463035283096410412411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 998765419927149508205909 1463035283096410412411)
          ·
            rfl

theorem cell20_259638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 11].length) (baseStart_259638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259638 prefixEnd_259638 := by exact prefixLift 259638
  have htrace : WordTrace (prefixWord ++ tailWord_259638) baseStart_259638 baseEnd_259638 := by
    simpa [prefixWord, tailWord_259638, baseEnd_259638] using wordTrace_append hprefix tailTrace_259638
  have hstable : (prefixWord ++ tailWord_259638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259638).length < 2 ^ (prefixWord ++ tailWord_259638).sum := by decide
  have hdescent : baseEnd_259638 < baseStart_259638 := by decide
  rcases family_descends (prefixWord ++ tailWord_259638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259644 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_259644 : Nat := 118140960795 + 259644 * 2 ^ 59
def prefixEnd_259644 : Nat := 4983230072969 + 3 ^ 40 * 259644 * 2
def baseEnd_259644 : Nat := 118508596494299889205267

theorem tailTrace_259644 : CollatzResearch.WordTrace tailWord_259644 prefixEnd_259644 118508596494299889205267 := by
  unfold tailWord_259644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734997335680803254964993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6313329780907737673286657 4734997335680803254964993)
  ·
    refine ⟨3551248001760602441223745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4734997335680803254964993 3551248001760602441223745)
    ·
      refine ⟨2663436001320451830917809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3551248001760602441223745 2663436001320451830917809)
      ·
        refine ⟨1997577000990338873188357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2663436001320451830917809 1997577000990338873188357)
        ·
          refine ⟨374545687685688538722817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1997577000990338873188357 374545687685688538722817)
          ·
            refine ⟨280909265764266404042113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374545687685688538722817 280909265764266404042113)
            ·
              refine ⟨210681949323199803031585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280909265764266404042113 210681949323199803031585)
              ·
                refine ⟨158011461992399852273689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210681949323199803031585 158011461992399852273689)
                ·
                  refine ⟨118508596494299889205267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158011461992399852273689 118508596494299889205267)
                  ·
                    rfl

theorem cell20_259644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_259644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259644 prefixEnd_259644 := by exact prefixLift 259644
  have htrace : WordTrace (prefixWord ++ tailWord_259644) baseStart_259644 baseEnd_259644 := by
    simpa [prefixWord, tailWord_259644, baseEnd_259644] using wordTrace_append hprefix tailTrace_259644
  have hstable : (prefixWord ++ tailWord_259644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259644).length < 2 ^ (prefixWord ++ tailWord_259644).sum := by decide
  have hdescent : baseEnd_259644 < baseStart_259644 := by decide
  rcases family_descends (prefixWord ++ tailWord_259644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259655 : List Nat := [1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_259655 : Nat := 118140960795 + 259655 * 2 ^ 59
def prefixEnd_259655 : Nat := 4983230072969 + 3 ^ 40 * 259655 * 2
def baseEnd_259655 : Nat := 39504539064677579946185

theorem tailTrace_259655 : CollatzResearch.WordTrace tailWord_259655 prefixEnd_259655 39504539064677579946185 := by
  unfold tailWord_259655
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470395874321755388580419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6313597249547836925720279 9470395874321755388580419)
  ·
    refine ⟨14205593811482633082870629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470395874321755388580419 14205593811482633082870629)
    ·
      refine ⟨2663548839652993703038243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14205593811482633082870629 2663548839652993703038243)
      ·
        refine ⟨3995323259479490554557365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663548839652993703038243 3995323259479490554557365)
        ·
          refine ⟨374561555576202239489753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3995323259479490554557365 374561555576202239489753)
          ·
            refine ⟨280921166682151679617315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374561555576202239489753 280921166682151679617315)
            ·
              refine ⟨421381750023227519425973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280921166682151679617315 421381750023227519425973)
              ·
                refine ⟨39504539064677579946185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421381750023227519425973 39504539064677579946185)
                ·
                  rfl

theorem cell20_259655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_259655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259655 prefixEnd_259655 := by exact prefixLift 259655
  have htrace : WordTrace (prefixWord ++ tailWord_259655) baseStart_259655 baseEnd_259655 := by
    simpa [prefixWord, tailWord_259655, baseEnd_259655] using wordTrace_append hprefix tailTrace_259655
  have hstable : (prefixWord ++ tailWord_259655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259655).length < 2 ^ (prefixWord ++ tailWord_259655).sum := by decide
  have hdescent : baseEnd_259655 < baseStart_259655 := by decide
  rcases family_descends (prefixWord ++ tailWord_259655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259707 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 2]
def baseStart_259707 : Nat := 118140960795 + 259707 * 2 ^ 59
def prefixEnd_259707 : Nat := 4983230072969 + 3 ^ 40 * 259707 * 2
def baseEnd_259707 : Nat := 118537351410951670105009

theorem tailTrace_259707 : CollatzResearch.WordTrace tailWord_259707 prefixEnd_259707 118537351410951670105009 := by
  unfold tailWord_259707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472292470133368269473375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6314861646755578846315583 9472292470133368269473375)
  ·
    refine ⟨14208438705200052404210063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9472292470133368269473375 14208438705200052404210063)
    ·
      refine ⟨21312658057800078606315095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14208438705200052404210063 21312658057800078606315095)
      ·
        refine ⟨31968987086700117909472643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21312658057800078606315095 31968987086700117909472643)
        ·
          refine ⟨47953480630050176864208965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31968987086700117909472643 47953480630050176864208965)
          ·
            refine ⟨8991277618134408162039181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47953480630050176864208965 8991277618134408162039181)
            ·
              refine ⟨3371729106800403060764693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8991277618134408162039181 3371729106800403060764693)
              ·
                refine ⟨158049801881268893473345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3371729106800403060764693 158049801881268893473345)
                ·
                  refine ⟨118537351410951670105009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158049801881268893473345 118537351410951670105009)
                  ·
                    rfl

theorem cell20_259707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2].length) (baseStart_259707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259707 prefixEnd_259707 := by exact prefixLift 259707
  have htrace : WordTrace (prefixWord ++ tailWord_259707) baseStart_259707 baseEnd_259707 := by
    simpa [prefixWord, tailWord_259707, baseEnd_259707] using wordTrace_append hprefix tailTrace_259707
  have hstable : (prefixWord ++ tailWord_259707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259707).length < 2 ^ (prefixWord ++ tailWord_259707).sum := by decide
  have hdescent : baseEnd_259707 < baseStart_259707 := by decide
  rcases family_descends (prefixWord ++ tailWord_259707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259721 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_259721 : Nat := 118140960795 + 259721 * 2 ^ 59
def prefixEnd_259721 : Nat := 4983230072969 + 3 ^ 40 * 259721 * 2
def baseEnd_259721 : Nat := 118543741392429843638285

theorem tailTrace_259721 : CollatzResearch.WordTrace tailWord_259721 prefixEnd_259721 118543741392429843638285 := by
  unfold tailWord_259721
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472803092082648660483017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6315202061388432440322011 9472803092082648660483017)
  ·
    refine ⟨7104602319061986495362263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9472803092082648660483017 7104602319061986495362263)
    ·
      refine ⟨10656903478592979743043395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104602319061986495362263 10656903478592979743043395)
      ·
        refine ⟨15985355217889469614565093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656903478592979743043395 15985355217889469614565093)
        ·
          refine ⟨2997254103354275552730955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15985355217889469614565093 2997254103354275552730955)
          ·
            refine ⟨4495881155031413329096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997254103354275552730955 4495881155031413329096433)
            ·
              refine ⟨3371910866273559996822325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495881155031413329096433 3371910866273559996822325)
              ·
                refine ⟨316116643713146249702093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3371910866273559996822325 316116643713146249702093)
                ·
                  refine ⟨118543741392429843638285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316116643713146249702093 118543741392429843638285)
                  ·
                    rfl

theorem cell20_259721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_259721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259721 prefixEnd_259721 := by exact prefixLift 259721
  have htrace : WordTrace (prefixWord ++ tailWord_259721) baseStart_259721 baseEnd_259721 := by
    simpa [prefixWord, tailWord_259721, baseEnd_259721] using wordTrace_append hprefix tailTrace_259721
  have hstable : (prefixWord ++ tailWord_259721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259721).length < 2 ^ (prefixWord ++ tailWord_259721).sum := by decide
  have hdescent : baseEnd_259721 < baseStart_259721 := by decide
  rcases family_descends (prefixWord ++ tailWord_259721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259758 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_259758 : Nat := 118140960795 + 259758 * 2 ^ 59
def prefixEnd_259758 : Nat := 4983230072969 + 3 ^ 40 * 259758 * 2
def baseEnd_259758 : Nat := 118560629200622159404801

theorem tailTrace_259758 : CollatzResearch.WordTrace tailWord_259758 prefixEnd_259758 118560629200622159404801 := by
  unfold tailWord_259758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184269074118575497447491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6316101728632402653053285 1184269074118575497447491)
  ·
    refine ⟨1776403611177863246171237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184269074118575497447491 1776403611177863246171237)
    ·
      refine ⟨333075677095849358657107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1776403611177863246171237 333075677095849358657107)
      ·
        refine ⟨499613515643774037985661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333075677095849358657107 499613515643774037985661)
        ·
          refine ⟨187355068366415264244623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499613515643774037985661 187355068366415264244623)
          ·
            refine ⟨281032602549622896366935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187355068366415264244623 281032602549622896366935)
            ·
              refine ⟨421548903824434344550403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281032602549622896366935 421548903824434344550403)
              ·
                refine ⟨632323355736651516825605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421548903824434344550403 632323355736651516825605)
                ·
                  refine ⟨118560629200622159404801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632323355736651516825605 118560629200622159404801)
                  ·
                    rfl

theorem cell20_259758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_259758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259758 prefixEnd_259758 := by exact prefixLift 259758
  have htrace : WordTrace (prefixWord ++ tailWord_259758) baseStart_259758 baseEnd_259758 := by
    simpa [prefixWord, tailWord_259758, baseEnd_259758] using wordTrace_append hprefix tailTrace_259758
  have hstable : (prefixWord ++ tailWord_259758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259758).length < 2 ^ (prefixWord ++ tailWord_259758).sum := by decide
  have hdescent : baseEnd_259758 < baseStart_259758 := by decide
  rcases family_descends (prefixWord ++ tailWord_259758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259759 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_259759 : Nat := 118140960795 + 259759 * 2 ^ 59
def prefixEnd_259759 : Nat := 4983230072969 + 3 ^ 40 * 259759 * 2
def baseEnd_259759 : Nat := 118561085627870600371463

theorem tailTrace_259759 : CollatzResearch.WordTrace tailWord_259759 prefixEnd_259759 118561085627870600371463 := by
  unfold tailWord_259759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474189065944981150366331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6316126043963320766910887 9474189065944981150366331)
  ·
    refine ⟨14211283598917471725549497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9474189065944981150366331 14211283598917471725549497)
    ·
      refine ⟨10658462699188103794162123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14211283598917471725549497 10658462699188103794162123)
      ·
        refine ⟨15987694048782155691243185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658462699188103794162123 15987694048782155691243185)
        ·
          refine ⟨11990770536586616768432389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15987694048782155691243185 11990770536586616768432389)
          ·
            refine ⟨2248269475609990644081073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11990770536586616768432389 2248269475609990644081073)
            ·
              refine ⟨1686202106707492983060805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248269475609990644081073 1686202106707492983060805)
              ·
                refine ⟨316162895007654934323901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1686202106707492983060805 316162895007654934323901)
                ·
                  refine ⟨118561085627870600371463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316162895007654934323901 118561085627870600371463)
                  ·
                    rfl

theorem cell20_259759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_259759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259759 prefixEnd_259759 := by exact prefixLift 259759
  have htrace : WordTrace (prefixWord ++ tailWord_259759) baseStart_259759 baseEnd_259759 := by
    simpa [prefixWord, tailWord_259759, baseEnd_259759] using wordTrace_append hprefix tailTrace_259759
  have hstable : (prefixWord ++ tailWord_259759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259759).length < 2 ^ (prefixWord ++ tailWord_259759).sum := by decide
  have hdescent : baseEnd_259759 < baseStart_259759 := by decide
  rcases family_descends (prefixWord ++ tailWord_259759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259811 : List Nat := [1, 1, 1, 7, 10]
def baseStart_259811 : Nat := 118140960795 + 259811 * 2 ^ 59
def prefixEnd_259811 : Nat := 4983230072969 + 3 ^ 40 * 259811 * 2
def baseEnd_259811 : Nat := 1464010121540611489357

theorem tailTrace_259811 : CollatzResearch.WordTrace tailWord_259811 prefixEnd_259811 1464010121540611489357 := by
  unfold tailWord_259811
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476085661756594031259287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6317390441171062687506191 9476085661756594031259287)
  ·
    refine ⟨14214128492634891046888931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476085661756594031259287 14214128492634891046888931)
    ·
      refine ⟨21321192738952336570333397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14214128492634891046888931 21321192738952336570333397)
      ·
        refine ⟨499715454819195388367189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21321192738952336570333397 499715454819195388367189)
        ·
          refine ⟨1464010121540611489357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 499715454819195388367189 1464010121540611489357)
          ·
            rfl

theorem cell20_259811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 10].length) (baseStart_259811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259811 prefixEnd_259811 := by exact prefixLift 259811
  have htrace : WordTrace (prefixWord ++ tailWord_259811) baseStart_259811 baseEnd_259811 := by
    simpa [prefixWord, tailWord_259811, baseEnd_259811] using wordTrace_append hprefix tailTrace_259811
  have hstable : (prefixWord ++ tailWord_259811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259811).length < 2 ^ (prefixWord ++ tailWord_259811).sum := by decide
  have hdescent : baseEnd_259811 < baseStart_259811 := by decide
  rcases family_descends (prefixWord ++ tailWord_259811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259838 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_259838 : Nat := 118140960795 + 259838 * 2 ^ 59
def prefixEnd_259838 : Nat := 4983230072969 + 3 ^ 40 * 259838 * 2
def baseEnd_259838 : Nat := 118597143380497436737807

theorem tailTrace_259838 : CollatzResearch.WordTrace tailWord_259838 prefixEnd_259838 118597143380497436737807 := by
  unfold tailWord_259838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184633804082347205311521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6318046955105851761661445 1184633804082347205311521)
  ·
    refine ⟨888475353061760403983641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1184633804082347205311521 888475353061760403983641)
    ·
      refine ⟨666356514796320302987731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 888475353061760403983641 666356514796320302987731)
      ·
        refine ⟨999534772194480454481597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666356514796320302987731 999534772194480454481597)
        ·
          refine ⟨374825539572930170430599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 999534772194480454481597 374825539572930170430599)
          ·
            refine ⟨562238309359395255645899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374825539572930170430599 562238309359395255645899)
            ·
              refine ⟨843357464039092883468849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562238309359395255645899 843357464039092883468849)
              ·
                refine ⟨632518098029319662601637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843357464039092883468849 632518098029319662601637)
                ·
                  refine ⟨118597143380497436737807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632518098029319662601637 118597143380497436737807)
                  ·
                    rfl

theorem cell20_259838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_259838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259838 prefixEnd_259838 := by exact prefixLift 259838
  have htrace : WordTrace (prefixWord ++ tailWord_259838) baseStart_259838 baseEnd_259838 := by
    simpa [prefixWord, tailWord_259838, baseEnd_259838] using wordTrace_append hprefix tailTrace_259838
  have hstable : (prefixWord ++ tailWord_259838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259838).length < 2 ^ (prefixWord ++ tailWord_259838).sum := by decide
  have hdescent : baseEnd_259838 < baseStart_259838 := by decide
  rcases family_descends (prefixWord ++ tailWord_259838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259873 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_259873 : Nat := 118140960795 + 259873 * 2 ^ 59
def prefixEnd_259873 : Nat := 4983230072969 + 3 ^ 40 * 259873 * 2
def baseEnd_259873 : Nat := 118613118334192870570997

theorem tailTrace_259873 : CollatzResearch.WordTrace tailWord_259873 prefixEnd_259873 118613118334192870570997 := by
  unfold tailWord_259873
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478346987531978620016273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6318897991687985746677515 9478346987531978620016273)
  ·
    refine ⟨7108760240648983965012205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9478346987531978620016273 7108760240648983965012205)
    ·
      refine ⟨2665785090243368986879577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7108760240648983965012205 2665785090243368986879577)
      ·
        refine ⟨1999338817682526740159683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2665785090243368986879577 1999338817682526740159683)
        ·
          refine ⟨2999008226523790110239525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999338817682526740159683 2999008226523790110239525)
          ·
            refine ⟨562314042473210645669911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2999008226523790110239525 562314042473210645669911)
            ·
              refine ⟨843471063709815968504867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562314042473210645669911 843471063709815968504867)
              ·
                refine ⟨1265206595564723952757301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843471063709815968504867 1265206595564723952757301)
                ·
                  refine ⟨118613118334192870570997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1265206595564723952757301 118613118334192870570997)
                  ·
                    rfl

theorem cell20_259873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_259873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259873 prefixEnd_259873 := by exact prefixLift 259873
  have htrace : WordTrace (prefixWord ++ tailWord_259873) baseStart_259873 baseEnd_259873 := by
    simpa [prefixWord, tailWord_259873, baseEnd_259873] using wordTrace_append hprefix tailTrace_259873
  have hstable : (prefixWord ++ tailWord_259873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259873).length < 2 ^ (prefixWord ++ tailWord_259873).sum := by decide
  have hdescent : baseEnd_259873 < baseStart_259873 := by decide
  rcases family_descends (prefixWord ++ tailWord_259873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259876 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_259876 : Nat := 118140960795 + 259876 * 2 ^ 59
def prefixEnd_259876 : Nat := 4983230072969 + 3 ^ 40 * 259876 * 2
def baseEnd_259876 : Nat := 118614487615938193470985

theorem tailTrace_259876 : CollatzResearch.WordTrace tailWord_259876 prefixEnd_259876 118614487615938193470985 := by
  unfold tailWord_259876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739228203260555066187741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6318970937680740088250321 4739228203260555066187741)
  ·
    refine ⟨1777210576222708149820403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4739228203260555066187741 1777210576222708149820403)
    ·
      refine ⟨2665815864334062224730605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777210576222708149820403 2665815864334062224730605)
      ·
        refine ⟨999680949125273334273977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2665815864334062224730605 999680949125273334273977)
        ·
          refine ⟨749760711843955000705483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999680949125273334273977 749760711843955000705483)
          ·
            refine ⟨1124641067765932501058225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749760711843955000705483 1124641067765932501058225)
            ·
              refine ⟨843480800824449375793669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124641067765932501058225 843480800824449375793669)
              ·
                refine ⟨158152650154584257961313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843480800824449375793669 158152650154584257961313)
                ·
                  refine ⟨118614487615938193470985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158152650154584257961313 118614487615938193470985)
                  ·
                    rfl

theorem cell20_259876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_259876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259876 prefixEnd_259876 := by exact prefixLift 259876
  have htrace : WordTrace (prefixWord ++ tailWord_259876) baseStart_259876 baseEnd_259876 := by
    simpa [prefixWord, tailWord_259876, baseEnd_259876] using wordTrace_append hprefix tailTrace_259876
  have hstable : (prefixWord ++ tailWord_259876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259876).length < 2 ^ (prefixWord ++ tailWord_259876).sum := by decide
  have hdescent : baseEnd_259876 < baseStart_259876 := by decide
  rcases family_descends (prefixWord ++ tailWord_259876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259886 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_259886 : Nat := 118140960795 + 259886 * 2 ^ 59
def prefixEnd_259886 : Nat := 4983230072969 + 3 ^ 40 * 259886 * 2
def baseEnd_259886 : Nat := 118619051888422603137611

theorem tailTrace_259886 : CollatzResearch.WordTrace tailWord_259886 prefixEnd_259886 118619051888422603137611 := by
  unfold tailWord_259886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184852642060610230029939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6319214090989921226826341 1184852642060610230029939)
  ·
    refine ⟨1777278963090915345044909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184852642060610230029939 1777278963090915345044909)
    ·
      refine ⟨666479611159093254391841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1777278963090915345044909 666479611159093254391841)
      ·
        refine ⟨499859708369319940793881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666479611159093254391841 499859708369319940793881)
        ·
          refine ⟨374894781276989955595411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499859708369319940793881 374894781276989955595411)
          ·
            refine ⟨562342171915484933393117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374894781276989955595411 562342171915484933393117)
            ·
              refine ⟨210878314468306850022419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562342171915484933393117 210878314468306850022419)
              ·
                refine ⟨316317471702460275033629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210878314468306850022419 316317471702460275033629)
                ·
                  refine ⟨118619051888422603137611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316317471702460275033629 118619051888422603137611)
                  ·
                    rfl

theorem cell20_259886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_259886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259886 prefixEnd_259886 := by exact prefixLift 259886
  have htrace : WordTrace (prefixWord ++ tailWord_259886) baseStart_259886 baseEnd_259886 := by
    simpa [prefixWord, tailWord_259886, baseEnd_259886] using wordTrace_append hprefix tailTrace_259886
  have hstable : (prefixWord ++ tailWord_259886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259886).length < 2 ^ (prefixWord ++ tailWord_259886).sum := by decide
  have hdescent : baseEnd_259886 < baseStart_259886 := by decide
  rcases family_descends (prefixWord ++ tailWord_259886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259910 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_259910 : Nat := 118140960795 + 259910 * 2 ^ 59
def prefixEnd_259910 : Nat := 4983230072969 + 3 ^ 40 * 259910 * 2
def baseEnd_259910 : Nat := 118630006142385186337513

theorem tailTrace_259910 : CollatzResearch.WordTrace tailWord_259910 prefixEnd_259910 118630006142385186337513 := by
  unfold tailWord_259910
  simp only [CollatzResearch.WordTrace]
  refine ⟨296240515262435435597287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6319797658931955959408789 296240515262435435597287)
  ·
    refine ⟨444360772893653153395931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296240515262435435597287 444360772893653153395931)
    ·
      refine ⟨666541159340479730093897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444360772893653153395931 666541159340479730093897)
      ·
        refine ⟨499905869505359797570423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666541159340479730093897 499905869505359797570423)
        ·
          refine ⟨749858804258039696355635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499905869505359797570423 749858804258039696355635)
          ·
            refine ⟨1124788206387059544533453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749858804258039696355635 1124788206387059544533453)
            ·
              refine ⟨421795577395147329200045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1124788206387059544533453 421795577395147329200045)
              ·
                refine ⟨158173341523180248450017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421795577395147329200045 158173341523180248450017)
                ·
                  refine ⟨118630006142385186337513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158173341523180248450017 118630006142385186337513)
                  ·
                    rfl

theorem cell20_259910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_259910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259910 prefixEnd_259910 := by exact prefixLift 259910
  have htrace : WordTrace (prefixWord ++ tailWord_259910) baseStart_259910 baseEnd_259910 := by
    simpa [prefixWord, tailWord_259910, baseEnd_259910] using wordTrace_append hprefix tailTrace_259910
  have hstable : (prefixWord ++ tailWord_259910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259910).length < 2 ^ (prefixWord ++ tailWord_259910).sum := by decide
  have hdescent : baseEnd_259910 < baseStart_259910 := by decide
  rcases family_descends (prefixWord ++ tailWord_259910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259925 : List Nat := [1, 3, 2, 2, 2, 2, 8]
def baseStart_259925 : Nat := 118140960795 + 259925 * 2 ^ 59
def prefixEnd_259925 : Nat := 4983230072969 + 3 ^ 40 * 259925 * 2
def baseEnd_259925 : Nat := 13181872505679088981939

theorem tailTrace_259925 : CollatzResearch.WordTrace tailWord_259925 prefixEnd_259925 13181872505679088981939 := by
  unfold tailWord_259925
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480243583343591500909229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6320162388895727667272819 9480243583343591500909229)
  ·
    refine ⟨3555091343753846812840961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9480243583343591500909229 3555091343753846812840961)
    ·
      refine ⟨2666318507815385109630721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3555091343753846812840961 2666318507815385109630721)
      ·
        refine ⟨1999738880861538832223041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2666318507815385109630721 1999738880861538832223041)
        ·
          refine ⟨1499804160646154124167281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999738880861538832223041 1499804160646154124167281)
          ·
            refine ⟨1124853120484615593125461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499804160646154124167281 1124853120484615593125461)
            ·
              refine ⟨13181872505679088981939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1124853120484615593125461 13181872505679088981939)
              ·
                rfl

theorem cell20_259925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_259925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259925 prefixEnd_259925 := by exact prefixLift 259925
  have htrace : WordTrace (prefixWord ++ tailWord_259925) baseStart_259925 baseEnd_259925 := by
    simpa [prefixWord, tailWord_259925, baseEnd_259925] using wordTrace_append hprefix tailTrace_259925
  have hstable : (prefixWord ++ tailWord_259925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259925).length < 2 ^ (prefixWord ++ tailWord_259925).sum := by decide
  have hdescent : baseEnd_259925 < baseStart_259925 := by decide
  rcases family_descends (prefixWord ++ tailWord_259925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259935 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_259935 : Nat := 118140960795 + 259935 * 2 ^ 59
def prefixEnd_259935 : Nat := 4983230072969 + 3 ^ 40 * 259935 * 2
def baseEnd_259935 : Nat := 118641416823596210504077

theorem tailTrace_259935 : CollatzResearch.WordTrace tailWord_259935 prefixEnd_259935 118641416823596210504077 := by
  unfold tailWord_259935
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480608313307363208773259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6320405542204908805848839 9480608313307363208773259)
  ·
    refine ⟨14220912469961044813159889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480608313307363208773259 14220912469961044813159889)
    ·
      refine ⟨10665684352470783609869917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14220912469961044813159889 10665684352470783609869917)
      ·
        refine ⟨3999631632176543853701219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10665684352470783609869917 3999631632176543853701219)
        ·
          refine ⟨5999447448264815780551829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999631632176543853701219 5999447448264815780551829)
          ·
            refine ⟨281224099137413239713367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5999447448264815780551829 281224099137413239713367)
            ·
              refine ⟨421836148706119859570051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281224099137413239713367 421836148706119859570051)
              ·
                refine ⟨632754223059179789355077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421836148706119859570051 632754223059179789355077)
                ·
                  refine ⟨118641416823596210504077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632754223059179789355077 118641416823596210504077)
                  ·
                    rfl

theorem cell20_259935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_259935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259935 prefixEnd_259935 := by exact prefixLift 259935
  have htrace : WordTrace (prefixWord ++ tailWord_259935) baseStart_259935 baseEnd_259935 := by
    simpa [prefixWord, tailWord_259935, baseEnd_259935] using wordTrace_append hprefix tailTrace_259935
  have hstable : (prefixWord ++ tailWord_259935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259935).length < 2 ^ (prefixWord ++ tailWord_259935).sum := by decide
  have hdescent : baseEnd_259935 < baseStart_259935 := by decide
  rcases family_descends (prefixWord ++ tailWord_259935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259973 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 2]
def baseStart_259973 : Nat := 118140960795 + 259973 * 2 ^ 59
def prefixEnd_259973 : Nat := 4983230072969 + 3 ^ 40 * 259973 * 2
def baseEnd_259973 : Nat := 118658761059036967237255

theorem tailTrace_259973 : CollatzResearch.WordTrace tailWord_259973 prefixEnd_259973 118658761059036967237255 := by
  unfold tailWord_259973
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481994287169695698656573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6321329524779797132437715 9481994287169695698656573)
  ·
    refine ⟨3555747857688635886996215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9481994287169695698656573 3555747857688635886996215)
    ·
      refine ⟨5333621786532953830494323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555747857688635886996215 5333621786532953830494323)
      ·
        refine ⟨8000432679799430745741485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333621786532953830494323 8000432679799430745741485)
        ·
          refine ⟨3000162254924786529653057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8000432679799430745741485 3000162254924786529653057)
          ·
            refine ⟨2250121691193589897239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3000162254924786529653057 2250121691193589897239793)
            ·
              refine ⟨1687591268395192422929845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250121691193589897239793 1687591268395192422929845)
              ·
                refine ⟨158211681412049289649673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1687591268395192422929845 158211681412049289649673)
                ·
                  refine ⟨118658761059036967237255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158211681412049289649673 118658761059036967237255)
                  ·
                    rfl

theorem cell20_259973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_259973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259973 prefixEnd_259973 := by exact prefixLift 259973
  have htrace : WordTrace (prefixWord ++ tailWord_259973) baseStart_259973 baseEnd_259973 := by
    simpa [prefixWord, tailWord_259973, baseEnd_259973] using wordTrace_append hprefix tailTrace_259973
  have hstable : (prefixWord ++ tailWord_259973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259973).length < 2 ^ (prefixWord ++ tailWord_259973).sum := by decide
  have hdescent : baseEnd_259973 < baseStart_259973 := by decide
  rcases family_descends (prefixWord ++ tailWord_259973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259986 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_259986 : Nat := 118140960795 + 259986 * 2 ^ 59
def prefixEnd_259986 : Nat := 4983230072969 + 3 ^ 40 * 259986 * 2
def baseEnd_259986 : Nat := 118664694613266699803869

theorem tailTrace_259986 : CollatzResearch.WordTrace tailWord_259986 prefixEnd_259986 118664694613266699803869 := by
  unfold tailWord_259986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370617109030649729719953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6321645624081732612586541 2370617109030649729719953)
  ·
    refine ⟨1777962831772987297289965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2370617109030649729719953 1777962831772987297289965)
    ·
      refine ⟨666736061914870236483737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1777962831772987297289965 666736061914870236483737)
      ·
        refine ⟨500052046436152677362803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666736061914870236483737 500052046436152677362803)
        ·
          refine ⟨750078069654229016044205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500052046436152677362803 750078069654229016044205)
          ·
            refine ⟨281279276120335881016577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750078069654229016044205 281279276120335881016577)
            ·
              refine ⟨210959457090251910762433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281279276120335881016577 210959457090251910762433)
              ·
                refine ⟨158219592817688933071825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210959457090251910762433 158219592817688933071825)
                ·
                  refine ⟨118664694613266699803869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158219592817688933071825 118664694613266699803869)
                  ·
                    rfl

theorem cell20_259986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_259986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_259986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_259986 prefixEnd_259986 := by exact prefixLift 259986
  have htrace : WordTrace (prefixWord ++ tailWord_259986) baseStart_259986 baseEnd_259986 := by
    simpa [prefixWord, tailWord_259986, baseEnd_259986] using wordTrace_append hprefix tailTrace_259986
  have hstable : (prefixWord ++ tailWord_259986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259986).length < 2 ^ (prefixWord ++ tailWord_259986).sum := by decide
  have hdescent : baseEnd_259986 < baseStart_259986 := by decide
  rcases family_descends (prefixWord ++ tailWord_259986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260091 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_260091 : Nat := 118140960795 + 260091 * 2 ^ 59
def prefixEnd_260091 : Nat := 4983230072969 + 3 ^ 40 * 260091 * 2
def baseEnd_260091 : Nat := 118712619474353001303439

theorem tailTrace_260091 : CollatzResearch.WordTrace tailWord_260091 prefixEnd_260091 118712619474353001303439 := by
  unfold tailWord_260091
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486298100742201851452127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6324198733828134567634751 9486298100742201851452127)
  ·
    refine ⟨14229447151113302777178191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9486298100742201851452127 14229447151113302777178191)
    ·
      refine ⟨21344170726669954165767287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14229447151113302777178191 21344170726669954165767287)
      ·
        refine ⟨32016256090004931248650931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344170726669954165767287 32016256090004931248650931)
        ·
          refine ⟨48024384135007396872976397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32016256090004931248650931 48024384135007396872976397)
          ·
            refine ⟨18009144050627773827366149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48024384135007396872976397 18009144050627773827366149)
            ·
              refine ⟨3376714509492707592631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18009144050627773827366149 3376714509492707592631153)
              ·
                refine ⟨2532535882119530694473365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376714509492707592631153 2532535882119530694473365)
                ·
                  refine ⟨118712619474353001303439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2532535882119530694473365 118712619474353001303439)
                  ·
                    rfl

theorem cell20_260091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_260091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260091 prefixEnd_260091 := by exact prefixLift 260091
  have htrace : WordTrace (prefixWord ++ tailWord_260091) baseStart_260091 baseEnd_260091 := by
    simpa [prefixWord, tailWord_260091, baseEnd_260091] using wordTrace_append hprefix tailTrace_260091
  have hstable : (prefixWord ++ tailWord_260091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260091).length < 2 ^ (prefixWord ++ tailWord_260091).sum := by decide
  have hdescent : baseEnd_260091 < baseStart_260091 := by decide
  rcases family_descends (prefixWord ++ tailWord_260091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260094 : List Nat := [4, 2, 2, 2, 1, 1, 8]
def baseStart_260094 : Nat := 118140960795 + 260094 * 2 ^ 59
def prefixEnd_260094 : Nat := 4983230072969 + 3 ^ 40 * 260094 * 2
def baseEnd_260094 : Nat := 13190443195122036022603

theorem tailTrace_260094 : CollatzResearch.WordTrace tailWord_260094 prefixEnd_260094 13190443195122036022603 := by
  unfold tailWord_260094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185800939966416670476417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6324271679820888909207557 1185800939966416670476417)
  ·
    refine ⟨889350704974812502857313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1185800939966416670476417 889350704974812502857313)
    ·
      refine ⟨667013028731109377142985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 889350704974812502857313 667013028731109377142985)
      ·
        refine ⟨500259771548332032857239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667013028731109377142985 500259771548332032857239)
        ·
          refine ⟨750389657322498049285859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500259771548332032857239 750389657322498049285859)
          ·
            refine ⟨1125584485983747073928789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750389657322498049285859 1125584485983747073928789)
            ·
              refine ⟨13190443195122036022603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1125584485983747073928789 13190443195122036022603)
              ·
                rfl

theorem cell20_260094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_260094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260094 prefixEnd_260094 := by exact prefixLift 260094
  have htrace : WordTrace (prefixWord ++ tailWord_260094) baseStart_260094 baseEnd_260094 := by
    simpa [prefixWord, tailWord_260094, baseEnd_260094] using wordTrace_append hprefix tailTrace_260094
  have hstable : (prefixWord ++ tailWord_260094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260094).length < 2 ^ (prefixWord ++ tailWord_260094).sum := by decide
  have hdescent : baseEnd_260094 < baseStart_260094 := by decide
  rcases family_descends (prefixWord ++ tailWord_260094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260100 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_260100 : Nat := 118140960795 + 260100 * 2 ^ 59
def prefixEnd_260100 : Nat := 4983230072969 + 3 ^ 40 * 260100 * 2
def baseEnd_260100 : Nat := 118716727319588970003403

theorem tailTrace_260100 : CollatzResearch.WordTrace tailWord_260100 prefixEnd_260100 118716727319588970003403 := by
  unfold tailWord_260100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743313178854798194264877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6324417571806397592353169 4743313178854798194264877)
  ·
    refine ⟨1778742442070549322849329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4743313178854798194264877 1778742442070549322849329)
    ·
      refine ⟨1334056831552911992136997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1778742442070549322849329 1334056831552911992136997)
      ·
        refine ⟨250135655916170998525687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1334056831552911992136997 250135655916170998525687)
        ·
          refine ⟨375203483874256497788531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250135655916170998525687 375203483874256497788531)
          ·
            refine ⟨562805225811384746682797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375203483874256497788531 562805225811384746682797)
            ·
              refine ⟨211051959679269280006049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562805225811384746682797 211051959679269280006049)
              ·
                refine ⟨158288969759451960004537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211051959679269280006049 158288969759451960004537)
                ·
                  refine ⟨118716727319588970003403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158288969759451960004537 118716727319588970003403)
                  ·
                    rfl

theorem cell20_260100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_260100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260100 prefixEnd_260100 := by exact prefixLift 260100
  have htrace : WordTrace (prefixWord ++ tailWord_260100) baseStart_260100 baseEnd_260100 := by
    simpa [prefixWord, tailWord_260100, baseEnd_260100] using wordTrace_append hprefix tailTrace_260100
  have hstable : (prefixWord ++ tailWord_260100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260100).length < 2 ^ (prefixWord ++ tailWord_260100).sum := by decide
  have hdescent : baseEnd_260100 < baseStart_260100 := by decide
  rcases family_descends (prefixWord ++ tailWord_260100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260104 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_260104 : Nat := 118140960795 + 260104 * 2 ^ 59
def prefixEnd_260104 : Nat := 4983230072969 + 3 ^ 40 * 260104 * 2
def baseEnd_260104 : Nat := 118718553028582733870053

theorem tailTrace_260104 : CollatzResearch.WordTrace tailWord_260104 prefixEnd_260104 118718553028582733870053 := by
  unfold tailWord_260104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743386124847552535837683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6324514833130070047783577 4743386124847552535837683)
  ·
    refine ⟨7115079187271328803756525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4743386124847552535837683 7115079187271328803756525)
    ·
      refine ⟨2668154695226748301408697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7115079187271328803756525 2668154695226748301408697)
      ·
        refine ⟨2001116021420061226056523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668154695226748301408697 2001116021420061226056523)
        ·
          refine ⟨3001674032130091839084785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001116021420061226056523 3001674032130091839084785)
          ·
            refine ⟨2251255524097568879313589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3001674032130091839084785 2251255524097568879313589)
            ·
              refine ⟨211055205384147082435649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2251255524097568879313589 211055205384147082435649)
              ·
                refine ⟨158291404038110311826737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211055205384147082435649 158291404038110311826737)
                ·
                  refine ⟨118718553028582733870053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158291404038110311826737 118718553028582733870053)
                  ·
                    rfl

theorem cell20_260104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_260104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260104 prefixEnd_260104 := by exact prefixLift 260104
  have htrace : WordTrace (prefixWord ++ tailWord_260104) baseStart_260104 baseEnd_260104 := by
    simpa [prefixWord, tailWord_260104, baseEnd_260104] using wordTrace_append hprefix tailTrace_260104
  have hstable : (prefixWord ++ tailWord_260104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260104).length < 2 ^ (prefixWord ++ tailWord_260104).sum := by decide
  have hdescent : baseEnd_260104 < baseStart_260104 := by decide
  rcases family_descends (prefixWord ++ tailWord_260104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260153 : List Nat := [1, 2, 1, 5, 3, 8]
def baseStart_260153 : Nat := 118140960795 + 260153 * 2 ^ 59
def prefixEnd_260153 : Nat := 4983230072969 + 3 ^ 40 * 260153 * 2
def baseEnd_260153 : Nat := 4397811776435420045797

theorem tailTrace_260153 : CollatzResearch.WordTrace tailWord_260153 prefixEnd_260153 4397811776435420045797 := by
  unfold tailWord_260153
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488559426517586440209113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6325706284345057626806075 9488559426517586440209113)
  ·
    refine ⟨7116419569888189830156835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9488559426517586440209113 7116419569888189830156835)
    ·
      refine ⟨10674629354832284745235253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7116419569888189830156835 10674629354832284745235253)
      ·
        refine ⟨1000746502015526694865805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10674629354832284745235253 1000746502015526694865805)
        ·
          refine ⟨375279938255822510574677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000746502015526694865805 375279938255822510574677)
          ·
            refine ⟨4397811776435420045797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 375279938255822510574677 4397811776435420045797)
            ·
              rfl

theorem cell20_260153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 8].length) (baseStart_260153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260153 prefixEnd_260153 := by exact prefixLift 260153
  have htrace : WordTrace (prefixWord ++ tailWord_260153) baseStart_260153 baseEnd_260153 := by
    simpa [prefixWord, tailWord_260153, baseEnd_260153] using wordTrace_append hprefix tailTrace_260153
  have hstable : (prefixWord ++ tailWord_260153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260153).length < 2 ^ (prefixWord ++ tailWord_260153).sum := by decide
  have hdescent : baseEnd_260153 < baseStart_260153 := by decide
  rcases family_descends (prefixWord ++ tailWord_260153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260184 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_260184 : Nat := 118140960795 + 260184 * 2 ^ 59
def prefixEnd_260184 : Nat := 4983230072969 + 3 ^ 40 * 260184 * 2
def baseEnd_260184 : Nat := 118755067208458011203059

theorem tailTrace_260184 : CollatzResearch.WordTrace tailWord_260184 prefixEnd_260184 118755067208458011203059 := by
  unfold tailWord_260184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744845044702639367293803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6326460059603519156391737 4744845044702639367293803)
  ·
    refine ⟨7117267567053959050940705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4744845044702639367293803 7117267567053959050940705)
    ·
      refine ⟨5337950675290469288205529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7117267567053959050940705 5337950675290469288205529)
      ·
        refine ⟨4003463006467851966154147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5337950675290469288205529 4003463006467851966154147)
        ·
          refine ⟨6005194509701777949231221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003463006467851966154147 6005194509701777949231221)
          ·
            refine ⟨562986985284541682740427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6005194509701777949231221 562986985284541682740427)
            ·
              refine ⟨844480477926812524110641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562986985284541682740427 844480477926812524110641)
              ·
                refine ⟨633360358445109393082981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844480477926812524110641 633360358445109393082981)
                ·
                  refine ⟨118755067208458011203059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633360358445109393082981 118755067208458011203059)
                  ·
                    rfl

theorem cell20_260184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_260184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260184 prefixEnd_260184 := by exact prefixLift 260184
  have htrace : WordTrace (prefixWord ++ tailWord_260184) baseStart_260184 baseEnd_260184 := by
    simpa [prefixWord, tailWord_260184, baseEnd_260184] using wordTrace_append hprefix tailTrace_260184
  have hstable : (prefixWord ++ tailWord_260184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260184).length < 2 ^ (prefixWord ++ tailWord_260184).sum := by decide
  have hdescent : baseEnd_260184 < baseStart_260184 := by decide
  rcases family_descends (prefixWord ++ tailWord_260184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260201 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 2]
def baseStart_260201 : Nat := 118140960795 + 260201 * 2 ^ 59
def prefixEnd_260201 : Nat := 4983230072969 + 3 ^ 40 * 260201 * 2
def baseEnd_260201 : Nat := 118762826471681507636323

theorem tailTrace_260201 : CollatzResearch.WordTrace tailWord_260201 prefixEnd_260201 118762826471681507636323 := by
  unfold tailWord_260201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490310130343690637956457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6326873420229127091970971 9490310130343690637956457)
  ·
    refine ⟨7117732597757767978467343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9490310130343690637956457 7117732597757767978467343)
    ·
      refine ⟨10676598896636651967701015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117732597757767978467343 10676598896636651967701015)
      ·
        refine ⟨16014898344954977951551523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676598896636651967701015 16014898344954977951551523)
        ·
          refine ⟨24022347517432466927327285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16014898344954977951551523 24022347517432466927327285)
          ·
            refine ⟨2252095079759293774436933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24022347517432466927327285 2252095079759293774436933)
            ·
              refine ⟨422267827454867582706925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2252095079759293774436933 422267827454867582706925)
              ·
                refine ⟨158350435295575343515097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422267827454867582706925 158350435295575343515097)
                ·
                  refine ⟨118762826471681507636323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158350435295575343515097 118762826471681507636323)
                  ·
                    rfl

theorem cell20_260201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_260201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260201 prefixEnd_260201 := by exact prefixLift 260201
  have htrace : WordTrace (prefixWord ++ tailWord_260201) baseStart_260201 baseEnd_260201 := by
    simpa [prefixWord, tailWord_260201, baseEnd_260201] using wordTrace_append hprefix tailTrace_260201
  have hstable : (prefixWord ++ tailWord_260201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260201).length < 2 ^ (prefixWord ++ tailWord_260201).sum := by decide
  have hdescent : baseEnd_260201 < baseStart_260201 := by decide
  rcases family_descends (prefixWord ++ tailWord_260201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260215 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_260215 : Nat := 118140960795 + 260215 * 2 ^ 59
def prefixEnd_260215 : Nat := 4983230072969 + 3 ^ 40 * 260215 * 2
def baseEnd_260215 : Nat := 118769216453159681169599

theorem tailTrace_260215 : CollatzResearch.WordTrace tailWord_260215 prefixEnd_260215 118769216453159681169599 := by
  unfold tailWord_260215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490820752292971028966099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6327213834861980685977399 9490820752292971028966099)
  ·
    refine ⟨14236231128439456543449149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490820752292971028966099 14236231128439456543449149)
    ·
      refine ⟨5338586673164796203793431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14236231128439456543449149 5338586673164796203793431)
      ·
        refine ⟨8007880009747194305690147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338586673164796203793431 8007880009747194305690147)
        ·
          refine ⟨12011820014620791458535221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007880009747194305690147 12011820014620791458535221)
          ·
            refine ⟨1126108126370699199237677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12011820014620791458535221 1126108126370699199237677)
            ·
              refine ⟨422290547389012199714129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126108126370699199237677 422290547389012199714129)
              ·
                refine ⟨316717910541759149785597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422290547389012199714129 316717910541759149785597)
                ·
                  refine ⟨118769216453159681169599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316717910541759149785597 118769216453159681169599)
                  ·
                    rfl

theorem cell20_260215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_260215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260215 prefixEnd_260215 := by exact prefixLift 260215
  have htrace : WordTrace (prefixWord ++ tailWord_260215) baseStart_260215 baseEnd_260215 := by
    simpa [prefixWord, tailWord_260215, baseEnd_260215] using wordTrace_append hprefix tailTrace_260215
  have hstable : (prefixWord ++ tailWord_260215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260215).length < 2 ^ (prefixWord ++ tailWord_260215).sum := by decide
  have hdescent : baseEnd_260215 < baseStart_260215 := by decide
  rcases family_descends (prefixWord ++ tailWord_260215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260256 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_260256 : Nat := 118140960795 + 260256 * 2 ^ 59
def prefixEnd_260256 : Nat := 4983230072969 + 3 ^ 40 * 260256 * 2
def baseEnd_260256 : Nat := 118787929970345760802765

theorem tailTrace_260256 : CollatzResearch.WordTrace tailWord_260256 prefixEnd_260256 118787929970345760802765 := by
  unfold tailWord_260256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746158072572217515604311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6328210763429623354139081 4746158072572217515604311)
  ·
    refine ⟨7119237108858326273406467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746158072572217515604311 7119237108858326273406467)
    ·
      refine ⟨10678855663287489410109701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119237108858326273406467 10678855663287489410109701)
      ·
        refine ⟨2002285436866404264395569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10678855663287489410109701 2002285436866404264395569)
        ·
          refine ⟨1501714077649803198296677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002285436866404264395569 1501714077649803198296677)
          ·
            refine ⟨281571389559338099680627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1501714077649803198296677 281571389559338099680627)
            ·
              refine ⟨422357084339007149520941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281571389559338099680627 422357084339007149520941)
              ·
                refine ⟨158383906627127681070353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422357084339007149520941 158383906627127681070353)
                ·
                  refine ⟨118787929970345760802765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158383906627127681070353 118787929970345760802765)
                  ·
                    rfl

theorem cell20_260256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_260256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260256 prefixEnd_260256 := by exact prefixLift 260256
  have htrace : WordTrace (prefixWord ++ tailWord_260256) baseStart_260256 baseEnd_260256 := by
    simpa [prefixWord, tailWord_260256, baseEnd_260256] using wordTrace_append hprefix tailTrace_260256
  have hstable : (prefixWord ++ tailWord_260256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260256).length < 2 ^ (prefixWord ++ tailWord_260256).sum := by decide
  have hdescent : baseEnd_260256 < baseStart_260256 := by decide
  rcases family_descends (prefixWord ++ tailWord_260256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260263 : List Nat := [1, 1, 6, 2, 3, 1, 6]
def baseStart_260263 : Nat := 118140960795 + 260263 * 2 ^ 59
def prefixEnd_260263 : Nat := 4983230072969 + 3 ^ 40 * 260263 * 2
def baseEnd_260263 : Nat := 13199013884564983063267

theorem tailTrace_260263 : CollatzResearch.WordTrace tailWord_260263 prefixEnd_260263 13199013884564983063267 := by
  unfold tailWord_260263
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492571456119075226713443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6328380970746050151142295 9492571456119075226713443)
  ·
    refine ⟨14238857184178612840070165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9492571456119075226713443 14238857184178612840070165)
    ·
      refine ⟨667446430508372476878289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14238857184178612840070165 667446430508372476878289)
      ·
        refine ⟨500584822881279357658717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667446430508372476878289 500584822881279357658717)
        ·
          refine ⟨187719308580479759122019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500584822881279357658717 187719308580479759122019)
          ·
            refine ⟨281578962870719638683029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187719308580479759122019 281578962870719638683029)
            ·
              refine ⟨13199013884564983063267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281578962870719638683029 13199013884564983063267)
              ·
                rfl

theorem cell20_260263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 6].length) (baseStart_260263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260263 prefixEnd_260263 := by exact prefixLift 260263
  have htrace : WordTrace (prefixWord ++ tailWord_260263) baseStart_260263 baseEnd_260263 := by
    simpa [prefixWord, tailWord_260263, baseEnd_260263] using wordTrace_append hprefix tailTrace_260263
  have hstable : (prefixWord ++ tailWord_260263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260263).length < 2 ^ (prefixWord ++ tailWord_260263).sum := by decide
  have hdescent : baseEnd_260263 < baseStart_260263 := by decide
  rcases family_descends (prefixWord ++ tailWord_260263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260273 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 2]
def baseStart_260273 : Nat := 118140960795 + 260273 * 2 ^ 59
def prefixEnd_260273 : Nat := 4983230072969 + 3 ^ 40 * 260273 * 2
def baseEnd_260273 : Nat := 118795689233569257236029

theorem tailTrace_260273 : CollatzResearch.WordTrace tailWord_260273 prefixEnd_260273 118795689233569257236029 := by
  unfold tailWord_260273
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492936186082846934577473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6328624124055231289718315 9492936186082846934577473)
  ·
    refine ⟨7119702139562135200933105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492936186082846934577473 7119702139562135200933105)
    ·
      refine ⟨5339776604671601400699829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119702139562135200933105 5339776604671601400699829)
      ·
        refine ⟨500604056687962631315609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5339776604671601400699829 500604056687962631315609)
        ·
          refine ⟨375453042515971973486707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500604056687962631315609 375453042515971973486707)
          ·
            refine ⟨563179563773957960230061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375453042515971973486707 563179563773957960230061)
            ·
              refine ⟨211192336415234235086273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563179563773957960230061 211192336415234235086273)
              ·
                refine ⟨158394252311425676314705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211192336415234235086273 158394252311425676314705)
                ·
                  refine ⟨118795689233569257236029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158394252311425676314705 118795689233569257236029)
                  ·
                    rfl

theorem cell20_260273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_260273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260273 prefixEnd_260273 := by exact prefixLift 260273
  have htrace : WordTrace (prefixWord ++ tailWord_260273) baseStart_260273 baseEnd_260273 := by
    simpa [prefixWord, tailWord_260273, baseEnd_260273] using wordTrace_append hprefix tailTrace_260273
  have hstable : (prefixWord ++ tailWord_260273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260273).length < 2 ^ (prefixWord ++ tailWord_260273).sum := by decide
  have hdescent : baseEnd_260273 < baseStart_260273 := by decide
  rcases family_descends (prefixWord ++ tailWord_260273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260274 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_260274 : Nat := 118140960795 + 260274 * 2 ^ 59
def prefixEnd_260274 : Nat := 4983230072969 + 3 ^ 40 * 260274 * 2
def baseEnd_260274 : Nat := 118796145660817698202691

theorem tailTrace_260274 : CollatzResearch.WordTrace tailWord_260274 prefixEnd_260274 118796145660817698202691 := by
  unfold tailWord_260274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373243164769806026340969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6328648439386149403575917 2373243164769806026340969)
  ·
    refine ⟨1779932373577354519755727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2373243164769806026340969 1779932373577354519755727)
    ·
      refine ⟨2669898560366031779633591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779932373577354519755727 2669898560366031779633591)
      ·
        refine ⟨4004847840549047669450387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669898560366031779633591 4004847840549047669450387)
        ·
          refine ⟨6007271760823571504175581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004847840549047669450387 6007271760823571504175581)
          ·
            refine ⟨2252726910308839314065843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6007271760823571504175581 2252726910308839314065843)
            ·
              refine ⟨3379090365463258971098765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252726910308839314065843 3379090365463258971098765)
              ·
                refine ⟨1267158887048722114162037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3379090365463258971098765 1267158887048722114162037)
                ·
                  refine ⟨118796145660817698202691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1267158887048722114162037 118796145660817698202691)
                  ·
                    rfl

theorem cell20_260274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_260274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260274 prefixEnd_260274 := by exact prefixLift 260274
  have htrace : WordTrace (prefixWord ++ tailWord_260274) baseStart_260274 baseEnd_260274 := by
    simpa [prefixWord, tailWord_260274, baseEnd_260274] using wordTrace_append hprefix tailTrace_260274
  have hstable : (prefixWord ++ tailWord_260274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260274).length < 2 ^ (prefixWord ++ tailWord_260274).sum := by decide
  have hdescent : baseEnd_260274 < baseStart_260274 := by decide
  rcases family_descends (prefixWord ++ tailWord_260274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260284 : List Nat := [2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_260284 : Nat := 118140960795 + 260284 * 2 ^ 59
def prefixEnd_260284 : Nat := 4983230072969 + 3 ^ 40 * 260284 * 2
def baseEnd_260284 : Nat := 39600236644434035956439

theorem tailTrace_260284 : CollatzResearch.WordTrace tailWord_260284 prefixEnd_260284 39600236644434035956439 := by
  unfold tailWord_260284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746668694521497906613953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6328891592695330542151937 4746668694521497906613953)
  ·
    refine ⟨3560001520891123429960465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4746668694521497906613953 3560001520891123429960465)
    ·
      refine ⟨2670001140668342572470349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3560001520891123429960465 2670001140668342572470349)
      ·
        refine ⟨1001250427750628464676381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2670001140668342572470349 1001250427750628464676381)
        ·
          refine ⟨375468910406485674253643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1001250427750628464676381 375468910406485674253643)
          ·
            refine ⟨563203365609728511380465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375468910406485674253643 563203365609728511380465)
            ·
              refine ⟨422402524207296383535349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563203365609728511380465 422402524207296383535349)
              ·
                refine ⟨39600236644434035956439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422402524207296383535349 39600236644434035956439)
                ·
                  rfl

theorem cell20_260284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_260284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260284 prefixEnd_260284 := by exact prefixLift 260284
  have htrace : WordTrace (prefixWord ++ tailWord_260284) baseStart_260284 baseEnd_260284 := by
    simpa [prefixWord, tailWord_260284, baseEnd_260284] using wordTrace_append hprefix tailTrace_260284
  have hstable : (prefixWord ++ tailWord_260284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260284).length < 2 ^ (prefixWord ++ tailWord_260284).sum := by decide
  have hdescent : baseEnd_260284 < baseStart_260284 := by decide
  rcases family_descends (prefixWord ++ tailWord_260284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260360 : List Nat := [2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_260360 : Nat := 118140960795 + 260360 * 2 ^ 59
def prefixEnd_260360 : Nat := 4983230072969 + 3 ^ 40 * 260360 * 2
def baseEnd_260360 : Nat := 39611799468061207111891

theorem tailTrace_260360 : CollatzResearch.WordTrace tailWord_260360 prefixEnd_260360 39611799468061207111891 := by
  unfold tailWord_260360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748054668383830396497267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6330739557845107195329689 4748054668383830396497267)
  ·
    refine ⟨7122082002575745594745901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748054668383830396497267 7122082002575745594745901)
    ·
      refine ⟨2670780750965904598029713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7122082002575745594745901 2670780750965904598029713)
      ·
        refine ⟨2003085563224428448522285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2670780750965904598029713 2003085563224428448522285)
        ·
          refine ⟨751157086209160668195857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2003085563224428448522285 751157086209160668195857)
          ·
            refine ⟨563367814656870501146893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751157086209160668195857 563367814656870501146893)
            ·
              refine ⟨211262930496326437930085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563367814656870501146893 211262930496326437930085)
              ·
                refine ⟨39611799468061207111891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211262930496326437930085 39611799468061207111891)
                ·
                  rfl

theorem cell20_260360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_260360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260360 prefixEnd_260360 := by exact prefixLift 260360
  have htrace : WordTrace (prefixWord ++ tailWord_260360) baseStart_260360 baseEnd_260360 := by
    simpa [prefixWord, tailWord_260360, baseEnd_260360] using wordTrace_append hprefix tailTrace_260360
  have hstable : (prefixWord ++ tailWord_260360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260360).length < 2 ^ (prefixWord ++ tailWord_260360).sum := by decide
  have hdescent : baseEnd_260360 < baseStart_260360 := by decide
  rcases family_descends (prefixWord ++ tailWord_260360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260384 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_260384 : Nat := 118140960795 + 260384 * 2 ^ 59
def prefixEnd_260384 : Nat := 4983230072969 + 3 ^ 40 * 260384 * 2
def baseEnd_260384 : Nat := 118846352658146204535575

theorem tailTrace_260384 : CollatzResearch.WordTrace tailWord_260384 prefixEnd_260384 118846352658146204535575 := by
  unfold tailWord_260384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748492344340356445934103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6331323125787141927912137 4748492344340356445934103)
  ·
    refine ⟨7122738516510534668901155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748492344340356445934103 7122738516510534668901155)
    ·
      refine ⟨10684107774765802003351733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122738516510534668901155 10684107774765802003351733)
      ·
        refine ⟨1001635103884293937814225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10684107774765802003351733 1001635103884293937814225)
        ·
          refine ⟨751226327913220453360669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001635103884293937814225 751226327913220453360669)
          ·
            refine ⟨281709872967457670010251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751226327913220453360669 281709872967457670010251)
            ·
              refine ⟨422564809451186505015377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281709872967457670010251 422564809451186505015377)
              ·
                refine ⟨316923607088389878761533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422564809451186505015377 316923607088389878761533)
                ·
                  refine ⟨118846352658146204535575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316923607088389878761533 118846352658146204535575)
                  ·
                    rfl

theorem cell20_260384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_260384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260384 prefixEnd_260384 := by exact prefixLift 260384
  have htrace : WordTrace (prefixWord ++ tailWord_260384) baseStart_260384 baseEnd_260384 := by
    simpa [prefixWord, tailWord_260384, baseEnd_260384] using wordTrace_append hprefix tailTrace_260384
  have hstable : (prefixWord ++ tailWord_260384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260384).length < 2 ^ (prefixWord ++ tailWord_260384).sum := by decide
  have hdescent : baseEnd_260384 < baseStart_260384 := by decide
  rcases family_descends (prefixWord ++ tailWord_260384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260419 : List Nat := [1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_260419 : Nat := 118140960795 + 260419 * 2 ^ 59
def prefixEnd_260419 : Nat := 4983230072969 + 3 ^ 40 * 260419 * 2
def baseEnd_260419 : Nat := 39620775870613879456255

theorem tailTrace_260419 : CollatzResearch.WordTrace tailWord_260419 prefixEnd_260419 39620775870613879456255 := by
  unfold tailWord_260419
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498261243553913869392311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6332174162369275912928207 9498261243553913869392311)
  ·
    refine ⟨14247391865330870804088467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498261243553913869392311 14247391865330870804088467)
    ·
      refine ⟨21371087797996306206132701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14247391865330870804088467 21371087797996306206132701)
      ·
        refine ⟨8014157924248614827299763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21371087797996306206132701 8014157924248614827299763)
        ·
          refine ⟨12021236886372922240949645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8014157924248614827299763 12021236886372922240949645)
          ·
            refine ⟨4507963832389845840356117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12021236886372922240949645 4507963832389845840356117)
            ·
              refine ⟨211310804643274023766693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4507963832389845840356117 211310804643274023766693)
              ·
                refine ⟨39620775870613879456255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211310804643274023766693 39620775870613879456255)
                ·
                  rfl

theorem cell20_260419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_260419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260419 prefixEnd_260419 := by exact prefixLift 260419
  have htrace : WordTrace (prefixWord ++ tailWord_260419) baseStart_260419 baseEnd_260419 := by
    simpa [prefixWord, tailWord_260419, baseEnd_260419] using wordTrace_append hprefix tailTrace_260419
  have hstable : (prefixWord ++ tailWord_260419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260419).length < 2 ^ (prefixWord ++ tailWord_260419).sum := by decide
  have hdescent : baseEnd_260419 < baseStart_260419 := by decide
  rcases family_descends (prefixWord ++ tailWord_260419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260519 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_260519 : Nat := 118140960795 + 260519 * 2 ^ 59
def prefixEnd_260519 : Nat := 4983230072969 + 3 ^ 40 * 260519 * 2
def baseEnd_260519 : Nat := 118907970336685735035023

theorem tailTrace_260519 : CollatzResearch.WordTrace tailWord_260519 prefixEnd_260519 118907970336685735035023 := by
  unfold tailWord_260519
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501908543191630948032611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6334605695461087298688407 9501908543191630948032611)
  ·
    refine ⟨14252862814787446422048917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501908543191630948032611 14252862814787446422048917)
    ·
      refine ⟨668102944443161551033543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14252862814787446422048917 668102944443161551033543)
      ·
        refine ⟨1002154416664742326550315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668102944443161551033543 1002154416664742326550315)
        ·
          refine ⟨1503231624997113489825473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002154416664742326550315 1503231624997113489825473)
          ·
            refine ⟨1127423718747835117369105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503231624997113489825473 1127423718747835117369105)
            ·
              refine ⟨845567789060876338026829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127423718747835117369105 845567789060876338026829)
              ·
                refine ⟨317087920897828626760061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845567789060876338026829 317087920897828626760061)
                ·
                  refine ⟨118907970336685735035023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317087920897828626760061 118907970336685735035023)
                  ·
                    rfl

theorem cell20_260519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_260519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260519 prefixEnd_260519 := by exact prefixLift 260519
  have htrace : WordTrace (prefixWord ++ tailWord_260519) baseStart_260519 baseEnd_260519 := by
    simpa [prefixWord, tailWord_260519, baseEnd_260519] using wordTrace_append hprefix tailTrace_260519
  have hstable : (prefixWord ++ tailWord_260519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260519).length < 2 ^ (prefixWord ++ tailWord_260519).sum := by decide
  have hdescent : baseEnd_260519 < baseStart_260519 := by decide
  rcases family_descends (prefixWord ++ tailWord_260519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260554 : List Nat := [3, 1, 2, 1, 2, 2, 9]
def baseStart_260554 : Nat := 118140960795 + 260554 * 2 ^ 59
def prefixEnd_260554 : Nat := 4983230072969 + 3 ^ 40 * 260554 * 2
def baseEnd_260554 : Nat := 13213771698931240985357

theorem tailTrace_260554 : CollatzResearch.WordTrace tailWord_260554 prefixEnd_260554 13213771698931240985357 := by
  unfold tailWord_260554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375796274516207981389179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6335456732043221283704477 2375796274516207981389179)
  ·
    refine ⟨3563694411774311972083769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2375796274516207981389179 3563694411774311972083769)
    ·
      refine ⟨2672770808830733979062827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3563694411774311972083769 2672770808830733979062827)
      ·
        refine ⟨4009156213246100968594241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672770808830733979062827 4009156213246100968594241)
        ·
          refine ⟨3006867159934575726445681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009156213246100968594241 3006867159934575726445681)
          ·
            refine ⟨2255150369950931794834261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006867159934575726445681 2255150369950931794834261)
            ·
              refine ⟨13213771698931240985357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2255150369950931794834261 13213771698931240985357)
              ·
                rfl

theorem cell20_260554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_260554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260554 prefixEnd_260554 := by exact prefixLift 260554
  have htrace : WordTrace (prefixWord ++ tailWord_260554) baseStart_260554 baseEnd_260554 := by
    simpa [prefixWord, tailWord_260554, baseEnd_260554] using wordTrace_append hprefix tailTrace_260554
  have hstable : (prefixWord ++ tailWord_260554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260554).length < 2 ^ (prefixWord ++ tailWord_260554).sum := by decide
  have hdescent : baseEnd_260554 < baseStart_260554 := by decide
  rcases family_descends (prefixWord ++ tailWord_260554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260564 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_260564 : Nat := 118140960795 + 260564 * 2 ^ 59
def prefixEnd_260564 : Nat := 4983230072969 + 3 ^ 40 * 260564 * 2
def baseEnd_260564 : Nat := 118928509562865578534839

theorem tailTrace_260564 : CollatzResearch.WordTrace tailWord_260564 prefixEnd_260564 118928509562865578534839 := by
  unfold tailWord_260564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751774914014301816710373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6335699885352402422280497 4751774914014301816710373)
  ·
    refine ⟨890957796377681590633195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4751774914014301816710373 890957796377681590633195)
    ·
      refine ⟨1336436694566522385949793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890957796377681590633195 1336436694566522385949793)
      ·
        refine ⟨1002327520924891789462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1336436694566522385949793 1002327520924891789462345)
        ·
          refine ⟨751745640693668842096759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002327520924891789462345 751745640693668842096759)
          ·
            refine ⟨1127618461040503263145139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751745640693668842096759 1127618461040503263145139)
            ·
              refine ⟨1691427691560754894717709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127618461040503263145139 1691427691560754894717709)
              ·
                refine ⟨634285384335283085519141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691427691560754894717709 634285384335283085519141)
                ·
                  refine ⟨118928509562865578534839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634285384335283085519141 118928509562865578534839)
                  ·
                    rfl

theorem cell20_260564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_260564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260564 prefixEnd_260564 := by exact prefixLift 260564
  have htrace : WordTrace (prefixWord ++ tailWord_260564) baseStart_260564 baseEnd_260564 := by
    simpa [prefixWord, tailWord_260564, baseEnd_260564] using wordTrace_append hprefix tailTrace_260564
  have hstable : (prefixWord ++ tailWord_260564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260564).length < 2 ^ (prefixWord ++ tailWord_260564).sum := by decide
  have hdescent : baseEnd_260564 < baseStart_260564 := by decide
  rcases family_descends (prefixWord ++ tailWord_260564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260592 : List Nat := [2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_260592 : Nat := 118140960795 + 260592 * 2 ^ 59
def prefixEnd_260592 : Nat := 4983230072969 + 3 ^ 40 * 260592 * 2
def baseEnd_260592 : Nat := 39647096508607308533797

theorem tailTrace_260592 : CollatzResearch.WordTrace tailWord_260592 prefixEnd_260592 39647096508607308533797 := by
  unfold tailWord_260592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752285535963582207720015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6336380714618109610293353 4752285535963582207720015)
  ·
    refine ⟨7128428303945373311580023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4752285535963582207720015 7128428303945373311580023)
    ·
      refine ⟨10692642455918059967370035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128428303945373311580023 10692642455918059967370035)
      ·
        refine ⟨16038963683877089951055053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692642455918059967370035 16038963683877089951055053)
        ·
          refine ⟨6014611381453908731645645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16038963683877089951055053 6014611381453908731645645)
          ·
            refine ⟨2255479268045215774367117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014611381453908731645645 2255479268045215774367117)
            ·
              refine ⟨845804725516955915387669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2255479268045215774367117 845804725516955915387669)
              ·
                refine ⟨39647096508607308533797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 845804725516955915387669 39647096508607308533797)
                ·
                  rfl

theorem cell20_260592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_260592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260592 prefixEnd_260592 := by exact prefixLift 260592
  have htrace : WordTrace (prefixWord ++ tailWord_260592) baseStart_260592 baseEnd_260592 := by
    simpa [prefixWord, tailWord_260592, baseEnd_260592] using wordTrace_append hprefix tailTrace_260592
  have hstable : (prefixWord ++ tailWord_260592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260592).length < 2 ^ (prefixWord ++ tailWord_260592).sum := by decide
  have hdescent : baseEnd_260592 < baseStart_260592 := by decide
  rcases family_descends (prefixWord ++ tailWord_260592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260602 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_260602 : Nat := 118140960795 + 260602 * 2 ^ 59
def prefixEnd_260602 : Nat := 4983230072969 + 3 ^ 40 * 260602 * 2
def baseEnd_260602 : Nat := 118945853798306335268017

theorem tailTrace_260602 : CollatzResearch.WordTrace tailWord_260602 prefixEnd_260602 118945853798306335268017 := by
  unfold tailWord_260602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376233950472734030826015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6336623867927290748869373 2376233950472734030826015)
  ·
    refine ⟨3564350925709101046239023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376233950472734030826015 3564350925709101046239023)
    ·
      refine ⟨5346526388563651569358535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564350925709101046239023 5346526388563651569358535)
      ·
        refine ⟨8019789582845477354037803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346526388563651569358535 8019789582845477354037803)
        ·
          refine ⟨12029684374268216031056705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019789582845477354037803 12029684374268216031056705)
          ·
            refine ⟨9022263280701162023292529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12029684374268216031056705 9022263280701162023292529)
            ·
              refine ⟨6766697460525871517469397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022263280701162023292529 6766697460525871517469397)
              ·
                refine ⟨158594471731075113690689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6766697460525871517469397 158594471731075113690689)
                ·
                  refine ⟨118945853798306335268017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158594471731075113690689 118945853798306335268017)
                  ·
                    rfl

theorem cell20_260602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_260602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260602 prefixEnd_260602 := by exact prefixLift 260602
  have htrace : WordTrace (prefixWord ++ tailWord_260602) baseStart_260602 baseEnd_260602 := by
    simpa [prefixWord, tailWord_260602, baseEnd_260602] using wordTrace_append hprefix tailTrace_260602
  have hstable : (prefixWord ++ tailWord_260602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260602).length < 2 ^ (prefixWord ++ tailWord_260602).sum := by decide
  have hdescent : baseEnd_260602 < baseStart_260602 := by decide
  rcases family_descends (prefixWord ++ tailWord_260602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260609 : List Nat := [1, 2, 4, 1, 3, 3, 6]
def baseStart_260609 : Nat := 118140960795 + 260609 * 2 ^ 59
def prefixEnd_260609 : Nat := 4983230072969 + 3 ^ 40 * 260609 * 2
def baseEnd_260609 : Nat := 13216560976560602448295

theorem tailTrace_260609 : CollatzResearch.WordTrace tailWord_260609 prefixEnd_260609 13216560976560602448295 := by
  unfold tailWord_260609
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505191112865576318808881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6336794075243717545872587 9505191112865576318808881)
  ·
    refine ⟨7128893334649182239106661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9505191112865576318808881 7128893334649182239106661)
    ·
      refine ⟨1336667500246721669832499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7128893334649182239106661 1336667500246721669832499)
      ·
        refine ⟨2005001250370082504748749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336667500246721669832499 2005001250370082504748749)
        ·
          refine ⟨751875468888780939280781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005001250370082504748749 751875468888780939280781)
          ·
            refine ⟨281953300833292852230293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751875468888780939280781 281953300833292852230293)
            ·
              refine ⟨13216560976560602448295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281953300833292852230293 13216560976560602448295)
              ·
                rfl

theorem cell20_260609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_260609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260609 prefixEnd_260609 := by exact prefixLift 260609
  have htrace : WordTrace (prefixWord ++ tailWord_260609) baseStart_260609 baseEnd_260609 := by
    simpa [prefixWord, tailWord_260609, baseEnd_260609] using wordTrace_append hprefix tailTrace_260609
  have hstable : (prefixWord ++ tailWord_260609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260609).length < 2 ^ (prefixWord ++ tailWord_260609).sum := by decide
  have hdescent : baseEnd_260609 < baseStart_260609 := by decide
  rcases family_descends (prefixWord ++ tailWord_260609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260616 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_260616 : Nat := 118140960795 + 260616 * 2 ^ 59
def prefixEnd_260616 : Nat := 4983230072969 + 3 ^ 40 * 260616 * 2
def baseEnd_260616 : Nat := 118952243779784508801293

theorem tailTrace_260616 : CollatzResearch.WordTrace tailWord_260616 prefixEnd_260616 118952243779784508801293 := by
  unfold tailWord_260616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752723211920108257156851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6336964282560144342875801 4752723211920108257156851)
  ·
    refine ⟨7129084817880162385735277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4752723211920108257156851 7129084817880162385735277)
    ·
      refine ⟨2673406806705060894650729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7129084817880162385735277 2673406806705060894650729)
      ·
        refine ⟨2005055105028795670988047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673406806705060894650729 2005055105028795670988047)
        ·
          refine ⟨3007582657543193506482071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005055105028795670988047 3007582657543193506482071)
          ·
            refine ⟨4511373986314790259723107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007582657543193506482071 4511373986314790259723107)
            ·
              refine ⟨6767060979472185389584661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511373986314790259723107 6767060979472185389584661)
              ·
                refine ⟨317205983412758690136781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6767060979472185389584661 317205983412758690136781)
                ·
                  refine ⟨118952243779784508801293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317205983412758690136781 118952243779784508801293)
                  ·
                    rfl

theorem cell20_260616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_260616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260616 prefixEnd_260616 := by exact prefixLift 260616
  have htrace : WordTrace (prefixWord ++ tailWord_260616) baseStart_260616 baseEnd_260616 := by
    simpa [prefixWord, tailWord_260616, baseEnd_260616] using wordTrace_append hprefix tailTrace_260616
  have hstable : (prefixWord ++ tailWord_260616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260616).length < 2 ^ (prefixWord ++ tailWord_260616).sum := by decide
  have hdescent : baseEnd_260616 < baseStart_260616 := by decide
  rcases family_descends (prefixWord ++ tailWord_260616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260668 : List Nat := [2, 2, 2, 2, 3, 9]
def baseStart_260668 : Nat := 118140960795 + 260668 * 2 ^ 59
def prefixEnd_260668 : Nat := 4983230072969 + 3 ^ 40 * 260668 * 2
def baseEnd_260668 : Nat := 4406517703581608854361

theorem tailTrace_260668 : CollatzResearch.WordTrace tailWord_260668 prefixEnd_260668 4406517703581608854361 := by
  unfold tailWord_260668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753671509825914697603329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6338228679767886263471105 4753671509825914697603329)
  ·
    refine ⟨3565253632369436023202497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4753671509825914697603329 3565253632369436023202497)
    ·
      refine ⟨2673940224277077017401873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3565253632369436023202497 2673940224277077017401873)
      ·
        refine ⟨2005455168207807763051405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673940224277077017401873 2005455168207807763051405)
        ·
          refine ⟨752045688077927911144277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005455168207807763051405 752045688077927911144277)
          ·
            refine ⟨4406517703581608854361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 752045688077927911144277 4406517703581608854361)
            ·
              rfl

theorem cell20_260668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 9].length) (baseStart_260668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260668 prefixEnd_260668 := by exact prefixLift 260668
  have htrace : WordTrace (prefixWord ++ tailWord_260668) baseStart_260668 baseEnd_260668 := by
    simpa [prefixWord, tailWord_260668, baseEnd_260668] using wordTrace_append hprefix tailTrace_260668
  have hstable : (prefixWord ++ tailWord_260668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260668).length < 2 ^ (prefixWord ++ tailWord_260668).sum := by decide
  have hdescent : baseEnd_260668 < baseStart_260668 := by decide
  rcases family_descends (prefixWord ++ tailWord_260668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260670 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_260670 : Nat := 118140960795 + 260670 * 2 ^ 59
def prefixEnd_260670 : Nat := 4983230072969 + 3 ^ 40 * 260670 * 2
def baseEnd_260670 : Nat := 118976890851200321001073

theorem tailTrace_260670 : CollatzResearch.WordTrace tailWord_260670 prefixEnd_260670 118976890851200321001073 := by
  unfold tailWord_260670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188426995705572967097433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6338277310429722491186309 1188426995705572967097433)
  ·
    refine ⟨891320246779179725323075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1188426995705572967097433 891320246779179725323075)
    ·
      refine ⟨1336980370168769587984613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891320246779179725323075 1336980370168769587984613)
      ·
        refine ⟨250683819406644297747115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1336980370168769587984613 250683819406644297747115)
        ·
          refine ⟨376025729109966446620673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250683819406644297747115 376025729109966446620673)
          ·
            refine ⟨282019296832474834965505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376025729109966446620673 282019296832474834965505)
            ·
              refine ⟨211514472624356126224129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282019296832474834965505 211514472624356126224129)
              ·
                refine ⟨158635854468267094668097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211514472624356126224129 158635854468267094668097)
                ·
                  refine ⟨118976890851200321001073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158635854468267094668097 118976890851200321001073)
                  ·
                    rfl

theorem cell20_260670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_260670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260670 prefixEnd_260670 := by exact prefixLift 260670
  have htrace : WordTrace (prefixWord ++ tailWord_260670) baseStart_260670 baseEnd_260670 := by
    simpa [prefixWord, tailWord_260670, baseEnd_260670] using wordTrace_append hprefix tailTrace_260670
  have hstable : (prefixWord ++ tailWord_260670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260670).length < 2 ^ (prefixWord ++ tailWord_260670).sum := by decide
  have hdescent : baseEnd_260670 < baseStart_260670 := by decide
  rcases family_descends (prefixWord ++ tailWord_260670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260675 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_260675 : Nat := 118140960795 + 260675 * 2 ^ 59
def prefixEnd_260675 : Nat := 4983230072969 + 3 ^ 40 * 260675 * 2
def baseEnd_260675 : Nat := 118979172987442525834385

theorem tailTrace_260675 : CollatzResearch.WordTrace tailWord_260675 prefixEnd_260675 118979172987442525834385 := by
  unfold tailWord_260675
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507598330626469590711479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6338398887084313060474319 9507598330626469590711479)
  ·
    refine ⟨14261397495939704386067219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9507598330626469590711479 14261397495939704386067219)
    ·
      refine ⟨21392096243909556579100829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14261397495939704386067219 21392096243909556579100829)
      ·
        refine ⟨8022036091466083717162811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21392096243909556579100829 8022036091466083717162811)
        ·
          refine ⟨12033054137199125575744217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022036091466083717162811 12033054137199125575744217)
          ·
            refine ⟨9024790602899344181808163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033054137199125575744217 9024790602899344181808163)
            ·
              refine ⟨13537185904349016272712245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024790602899344181808163 13537185904349016272712245)
              ·
                refine ⟨1269111178532720275566773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13537185904349016272712245 1269111178532720275566773)
                ·
                  refine ⟨118979172987442525834385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269111178532720275566773 118979172987442525834385)
                  ·
                    rfl

theorem cell20_260675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_260675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260675 prefixEnd_260675 := by exact prefixLift 260675
  have htrace : WordTrace (prefixWord ++ tailWord_260675) baseStart_260675 baseEnd_260675 := by
    simpa [prefixWord, tailWord_260675, baseEnd_260675] using wordTrace_append hprefix tailTrace_260675
  have hstable : (prefixWord ++ tailWord_260675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260675).length < 2 ^ (prefixWord ++ tailWord_260675).sum := by decide
  have hdescent : baseEnd_260675 < baseStart_260675 := by decide
  rcases family_descends (prefixWord ++ tailWord_260675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260712 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_260712 : Nat := 118140960795 + 260712 * 2 ^ 59
def prefixEnd_260712 : Nat := 4983230072969 + 3 ^ 40 * 260712 * 2
def baseEnd_260712 : Nat := 118996060795634841600901

theorem tailTrace_260712 : CollatzResearch.WordTrace tailWord_260712 prefixEnd_260712 118996060795634841600901 := by
  unfold tailWord_260712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754473915746212454904195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6339298554328283273205593 4754473915746212454904195)
  ·
    refine ⟨7131710873619318682356293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754473915746212454904195 7131710873619318682356293)
    ·
      refine ⟨1337195788803622252941805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7131710873619318682356293 1337195788803622252941805)
      ·
        refine ⟨501448420801358344853177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1337195788803622252941805 501448420801358344853177)
        ·
          refine ⟨376086315601018758639883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501448420801358344853177 376086315601018758639883)
          ·
            refine ⟨564129473401528137959825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376086315601018758639883 564129473401528137959825)
            ·
              refine ⟨423097105051146103469869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564129473401528137959825 423097105051146103469869)
              ·
                refine ⟨158661414394179788801201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423097105051146103469869 158661414394179788801201)
                ·
                  refine ⟨118996060795634841600901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158661414394179788801201 118996060795634841600901)
                  ·
                    rfl

theorem cell20_260712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_260712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260712 prefixEnd_260712 := by exact prefixLift 260712
  have htrace : WordTrace (prefixWord ++ tailWord_260712) baseStart_260712 baseEnd_260712 := by
    simpa [prefixWord, tailWord_260712, baseEnd_260712] using wordTrace_append hprefix tailTrace_260712
  have hstable : (prefixWord ++ tailWord_260712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260712).length < 2 ^ (prefixWord ++ tailWord_260712).sum := by decide
  have hdescent : baseEnd_260712 < baseStart_260712 := by decide
  rcases family_descends (prefixWord ++ tailWord_260712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260713 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_260713 : Nat := 118140960795 + 260713 * 2 ^ 59
def prefixEnd_260713 : Nat := 4983230072969 + 3 ^ 40 * 260713 * 2
def baseEnd_260713 : Nat := 118996517222883282567563

theorem tailTrace_260713 : CollatzResearch.WordTrace tailWord_260713 prefixEnd_260713 118996517222883282567563 := by
  unfold tailWord_260713
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508984304488802080594793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6339322869659201387063195 9508984304488802080594793)
  ·
    refine ⟨7131738228366601560446095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9508984304488802080594793 7131738228366601560446095)
    ·
      refine ⟨10697607342549902340669143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131738228366601560446095 10697607342549902340669143)
      ·
        refine ⟨16046411013824853511003715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10697607342549902340669143 16046411013824853511003715)
        ·
          refine ⟨24069616520737280266505573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046411013824853511003715 24069616520737280266505573)
          ·
            refine ⟨4513053097638240049969795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24069616520737280266505573 4513053097638240049969795)
            ·
              refine ⟨6769579646457360074954693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513053097638240049969795 6769579646457360074954693)
              ·
                refine ⟨1269296183710755014054005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6769579646457360074954693 1269296183710755014054005)
                ·
                  refine ⟨118996517222883282567563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269296183710755014054005 118996517222883282567563)
                  ·
                    rfl

theorem cell20_260713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_260713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260713 prefixEnd_260713 := by exact prefixLift 260713
  have htrace : WordTrace (prefixWord ++ tailWord_260713) baseStart_260713 baseEnd_260713 := by
    simpa [prefixWord, tailWord_260713, baseEnd_260713] using wordTrace_append hprefix tailTrace_260713
  have hstable : (prefixWord ++ tailWord_260713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260713).length < 2 ^ (prefixWord ++ tailWord_260713).sum := by decide
  have hdescent : baseEnd_260713 < baseStart_260713 := by decide
  rcases family_descends (prefixWord ++ tailWord_260713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260716 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_260716 : Nat := 118140960795 + 260716 * 2 ^ 59
def prefixEnd_260716 : Nat := 4983230072969 + 3 ^ 40 * 260716 * 2
def baseEnd_260716 : Nat := 118997886504628605467551

theorem tailTrace_260716 : CollatzResearch.WordTrace tailWord_260716 prefixEnd_260716 118997886504628605467551 := by
  unfold tailWord_260716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754546861738966796477001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6339395815651955728636001 4754546861738966796477001)
  ·
    refine ⟨3565910146304225097357751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4754546861738966796477001 3565910146304225097357751)
    ·
      refine ⟨5348865219456337646036627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565910146304225097357751 5348865219456337646036627)
      ·
        refine ⟨8023297829184506469054941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348865219456337646036627 8023297829184506469054941)
        ·
          refine ⟨3008736685944189925895603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8023297829184506469054941 3008736685944189925895603)
          ·
            refine ⟨4513105028916284888843405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008736685944189925895603 4513105028916284888843405)
            ·
              refine ⟨1692414385843606833316277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4513105028916284888843405 1692414385843606833316277)
              ·
                refine ⟨158663848672838140623401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692414385843606833316277 158663848672838140623401)
                ·
                  refine ⟨118997886504628605467551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158663848672838140623401 118997886504628605467551)
                  ·
                    rfl

theorem cell20_260716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_260716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260716 prefixEnd_260716 := by exact prefixLift 260716
  have htrace : WordTrace (prefixWord ++ tailWord_260716) baseStart_260716 baseEnd_260716 := by
    simpa [prefixWord, tailWord_260716, baseEnd_260716] using wordTrace_append hprefix tailTrace_260716
  have hstable : (prefixWord ++ tailWord_260716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260716).length < 2 ^ (prefixWord ++ tailWord_260716).sum := by decide
  have hdescent : baseEnd_260716 < baseStart_260716 := by decide
  rcases family_descends (prefixWord ++ tailWord_260716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260754 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_260754 : Nat := 118140960795 + 260754 * 2 ^ 59
def prefixEnd_260754 : Nat := 4983230072969 + 3 ^ 40 * 260754 * 2
def baseEnd_260754 : Nat := 119015230740069362200729

theorem tailTrace_260754 : CollatzResearch.WordTrace tailWord_260754 prefixEnd_260754 119015230740069362200729 := by
  unfold tailWord_260754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377619924335066520709329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6340319798226844055224877 2377619924335066520709329)
  ·
    refine ⟨1783214943251299890531997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2377619924335066520709329 1783214943251299890531997)
    ·
      refine ⟨668705603719237458949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1783214943251299890531997 668705603719237458949499)
      ·
        refine ⟨1003058405578856188424249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668705603719237458949499 1003058405578856188424249)
        ·
          refine ⟨752293804184142141318187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003058405578856188424249 752293804184142141318187)
          ·
            refine ⟨1128440706276213211977281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752293804184142141318187 1128440706276213211977281)
            ·
              refine ⟨846330529707159908982961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128440706276213211977281 846330529707159908982961)
              ·
                refine ⟨634747897280369931737221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846330529707159908982961 634747897280369931737221)
                ·
                  refine ⟨119015230740069362200729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634747897280369931737221 119015230740069362200729)
                  ·
                    rfl

theorem cell20_260754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_260754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260754 prefixEnd_260754 := by exact prefixLift 260754
  have htrace : WordTrace (prefixWord ++ tailWord_260754) baseStart_260754 baseEnd_260754 := by
    simpa [prefixWord, tailWord_260754, baseEnd_260754] using wordTrace_append hprefix tailTrace_260754
  have hstable : (prefixWord ++ tailWord_260754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260754).length < 2 ^ (prefixWord ++ tailWord_260754).sum := by decide
  have hdescent : baseEnd_260754 < baseStart_260754 := by decide
  rcases family_descends (prefixWord ++ tailWord_260754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
